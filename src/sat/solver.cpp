#include "sat/solver.h"

#include "fmt/format.h"
#include "sat/binary.h"
#include "sat/disjunction.h"
#include "sat/elimination.h"
#include "sat/probing.h"
#include "sat/propengine.h"
#include "sat/subsumption.h"
#include "sat/vivification.h"

namespace dawn {

static void printHeader()
{
	fmt::print(
	    "c     vars    units     bins    longs  size   learnt  size  glue\n");
}

static void printLine(Sat &sat)
{
	// number of unary/binary clauses
	size_t unaryCount = sat.units.size();
	size_t binaryCount = 0;
	for (auto &b : sat.bins)
		binaryCount += b.size();
	binaryCount /= 2;

	// number/size/glue of irred/learnt long clauses
	size_t longCount = 0;
	size_t learntCount = 0;
	size_t longLits = 0;
	size_t learntLits = 0;
	size_t learntGlue = 0;

	for (auto [ci, cl] : sat.clauses)
		if (!cl.isRemoved())
		{
			(void)ci;
			if (cl.irred())
			{
				longCount += 1;
				longLits += cl.size();
			}
			else
			{
				learntCount += 1;
				learntLits += cl.size();
				learntGlue += cl.glue;
			}
		}

	fmt::print(
	    "c {:#8} {:#8} {:#8} {:#8} {:5.2f} {:#8} {:5.2f} {:5.2f} {:8.2f} MiB\n",
	    sat.varCount(), unaryCount, binaryCount, longCount,
	    (double)longLits / longCount, learntCount,
	    (double)learntLits / learntCount, (double)learntGlue / learntCount,
	    sat.memory_usage() / 1024. / 1024.);
}

int luby(int i)
{
	assert(i > 0);
	if (__builtin_popcount(i + 1) == 1)
		return (i + 1) / 2;
	else
		return luby(i - (1 << (31 - __builtin_clz(i))) + 1);
}

int restartSize(int iter, SolverConfig const &config)
{
	assert(iter >= 1);
	switch (config.restart_type)
	{
	case RestartType::constant:
		return config.restart_base;
	case RestartType::linear:
		return iter * config.restart_base;
	case RestartType::geometric:
		return std::pow(config.restart_mult, iter - 1) * config.restart_base;
	case RestartType::luby:
		return luby(iter) * config.restart_base;
	default:
		assert(false);
	}
}

Solution buildSolution(const PropEngine &p)
{
	assert(!p.conflict);
	auto outer = Sat(p.sat.varCountOuter());
	for (auto [ci, cl] : p.sat.extension_clauses)
	{
		(void)ci;
		outer.addClauseOuter(cl.lits());
	}

	auto outerProp = PropEngineLight(outer);
	assert(!outerProp.conflict);
	for (int i = 0; i < p.sat.varCountOuter(); ++i)
	{
		Lit inner = p.sat.outerToInner(Lit(i, false));
		if (inner.fixed())
			outerProp.propagate(Lit(i, inner.sign()));
		else if (inner.proper())
		{
			if (p.assign[inner])
				outerProp.propagate(Lit(i, false));
			else if (p.assign[inner.neg()])
				outerProp.propagate(Lit(i, true));
			else
				assert(false);
		}
		else if (inner == Lit::elim())
		{}
		else
			assert(false);
		assert(!outerProp.conflict);
	}

	for (size_t i = p.sat.removed_vars.size(); i--;)
	{
		Lit a = Lit(p.sat.removed_vars[i], false);
		if (outerProp.assign[a] || outerProp.assign[a.neg()])
			continue;
		outerProp.propagate(a);
		assert(!outerProp.conflict);
	}

	auto sol = Solution(outerProp.assign);
	assert(sol.valid());
	return sol;
}

/** returns solution if found, or std::nullopt if limits reached or
 * contradiction */
std::optional<Solution> search(PropEngine &p, int64_t maxConfl,
                               SolverConfig const &config)
{
	Sat &sat = p.sat;

	util::StopwatchGuard _(sat.stats.swSearch);

	ActivityHeap activityHeap(sat);
	for (int i = 0; i < sat.varCount(); ++i)
		activityHeap.push(i);

	p.config.otf = config.otf;
	p.config.lhbr = config.lhbr;
	p.config.full_resolution = config.full_resolution;
	p.activity_heap = &activityHeap;

	int64_t nConfl = 0;

	std::vector<Lit> buf;

	while (true)
	{
		// handle conflicts
		while (p.conflict)
		{
			nConfl += 1;

			// level 0 conflict -> UNSAT
			if (p.level() == 0)
			{
				sat.addEmpty();
				return std::nullopt;
			}

			// analyze conflict
			int backLevel;
			uint8_t glue;
			backLevel = p.analyzeConflict(buf);
			if (config.full_resolution)
			{
				glue = buf.size() > 255 ? 255 : (uint8_t)buf.size();
				assert(glue == p.calcGlue(buf));
			}
			else
				glue = p.calcGlue(buf);

			sat.decayVariableActivity();
			sat.stats.nLearnt += 1;
			sat.stats.nLitsLearnt += buf.size();

			// unroll to apropriate level and propagate new learnt clause
			p.unroll(backLevel);
			Reason r = p.addLearntClause(buf, glue);
			p.propagateFull(buf[0], r);
			for (Lit x : p.trail(p.level()))
				sat.polarity[x.var()] = x.sign();

			buf.resize(0);
		}

		/** maxConfl reached -> unroll and exit */
		if (nConfl > maxConfl || interrupt)
		{
			if (p.level() > 0)
				p.unroll(0);
			return std::nullopt;
		}

		// choose a branching variable
		// int branch = p.unassignedVariable();
		int branch = -1;

		while (!activityHeap.empty())
		{
			int v = activityHeap.pop();
			if (p.assign[Lit(v, false)] || p.assign[Lit(v, true)])
				continue;

			// check the heap(very expensive, debug only)
			// for (int i = 0; i < sat.varCount(); ++i)
			//	assert(assign[Lit(i, false)] || assign[Lit(i, true)] ||
			//	       sat.activity[i] <= sat.activity[v]);

			branch = v;
			break;
		}

		// no unassigned left -> solution is found
		if (branch == -1)
			return buildSolution(p);

		Lit branchLit = Lit(branch, sat.polarity[branch]);

		if (config.branch_dom >= 1)
		{
			// NOTE: the counter avoids infinite loop due to equivalent vars
			// TODO: think again about the order of binary clauses. That has an
			//       influence here
			int counter = 0;
		again:
			for (Lit l : sat.bins[branchLit]) // l.neg implies branchLit
				if (!p.assign[l])
					if (config.branch_dom >= 2 ||
					    sat.polarity[l.var()] == l.neg().sign())
					{
						branchLit = l.neg();
						if (++counter < 5)
							goto again;
						else
							break;
					}
		}

		// propagate branch
		p.branch(branchLit);
		for (Lit x : p.trail(p.level()))
			sat.polarity[x.var()] = x.sign();
	}
}

void cleanClausesSize(ClauseStorage &clauses, size_t nKeep)
{
	std::vector<std::vector<CRef>> list(200);
	for (auto [ci, cl] : clauses)
	{
		if (cl.irred())
			continue;
		if (cl.size() >= list.size())
		{
			cl.remove();
			continue;
		}
		list[cl.size()].push_back(ci);
	}

	size_t count = 0;
	size_t len = 0;
	for (; len < list.size() && count < nKeep; len++)
		count += list[len].size();
	for (; len < list.size(); len++)
		for (CRef ci : list[len])
			clauses[ci].remove();
}

void cleanClausesGlue(ClauseStorage &clauses, size_t nKeep)
{
	std::vector<std::vector<CRef>> list(200);
	for (auto [ci, cl] : clauses)
	{
		if (cl.irred())
			continue;
		if (cl.glue >= list.size())
		{
			cl.remove();
			continue;
		}
		list[cl.glue].push_back(ci);
	}

	size_t count = 0;
	size_t len = 0;
	for (; len < list.size() && count < nKeep; len++)
		count += list[len].size();
	for (; len < list.size(); len++)
		for (CRef ci : list[len])
			clauses[ci].remove();
}

/** run the full inprocessing */
void inprocess(Sat &sat, SolverConfig const &config)
{

	// printBinaryStats(sat);
	cleanup(sat);

	for (int iter = 0;
	     config.inprocessIters == 0 || iter < config.inprocessIters; ++iter)
	{
		bool change = false;
		// failed literal probing settings:
		// 0 = none
		// 1 = only run while very successful
		// 2 = run until everything is found
		// 3 = also run binary probing
		if (config.probing > 0)
			change |= probe(sat, config.probing >= 2 ? 0 : 10000);

		if (config.subsume >= 1)
			change |= subsumeBinary(sat);

		if (config.subsume >= 2)
			change |= subsumeLong(sat);

		if (config.probing >= 3)
			change |= probeBinary(sat);

		if (config.vivify >= 1)
			change |= runVivification(sat, config.vivify >= 2);

		if (config.bva >= 1)
			change |= makeDisjunctions(sat);

		if (config.vivify >= 1)
			change |= runVivification(sat, config.vivify >= 2);

		// cleanup
		// (do this last, because it cant lead to anything new for the other
		// passes)
		if (config.tbr > 0)
			runBinaryReduction(sat);

		if (!change)
			break;
	}
}

int solve(Sat &sat, Solution &sol, SolverConfig const &config)
{
	util::StopwatchGuard _(sat.stats.swTotal);

	int64_t lastInprocess = sat.stats.nConfls();
	inprocess(sat, config);
	// run BVE only once at the beginning, not at every inprocessing
	// (it ignores and removes learnt clauses, so can be very harmful)
	if (config.bve > 0)
	{
		if (run_variable_elimination(sat))
			inprocess(sat, config);
	}

	fmt::print("c after preprocessing: {} vars and {} clauses\n",
	           sat.varCount(), sat.clauseCount());

	printHeader();
	int64_t lastPrint = sat.stats.nConfls();

	// it is kinda expensive to reconstruct the PropEngine at every restart,
	// so we keep it and only reconstruct after inprocessing or cleaning has run
	std::unique_ptr<PropEngine> propEngine = nullptr;

	// main solver loop
	for (int iter = 1;; ++iter)
	{
		// check limit
		if (sat.stats.nConfls() >= config.max_confls)
		{
			fmt::print("c conflict limit reached. abort solver.\n");
			return 30;
		}

		if (propEngine == nullptr)
			propEngine = std::make_unique<PropEngine>(sat);

		// search for a number of conflicts
		if (auto tmp =
		        search(*propEngine.get(), restartSize(iter, config), config);
		    tmp)
		{
			assert(!sat.contradiction);
			sol = *tmp;
			return 10;
		}

		if (sat.contradiction)
			return 20;

		if (interrupt)
		{
			fmt::print("c interrupted. abort solver.\n");
			return 30;
		}
		bool needInprocess = sat.stats.nConfls() > lastInprocess + 20000;

		if (needInprocess || sat.stats.nConfls() > lastPrint + 1000)
		{
			printLine(sat);
			lastPrint = sat.stats.nConfls();
		}

		// inprocessing
		if (needInprocess)
		{
			propEngine.reset();
			lastInprocess = sat.stats.nConfls();
			inprocess(sat, config);

			// clause cleaning
			for (auto [ci, cl] : sat.clauses)
			{
				(void)ci;
				if (cl.irred())
					continue;
				if (cl.size() > config.max_learnt_size ||
				    cl.glue > config.max_learnt_glue)
					cl.remove();
			}
			if ((int64_t)sat.longCountRed() > config.max_learnt)
			{
				if (config.use_glue)
					cleanClausesGlue(sat.clauses, config.max_learnt);
				else
					cleanClausesSize(sat.clauses, config.max_learnt);
				sat.clauses.compactify();
			}
			if (sat.longCountRed() > (size_t)sat.stats.nConfls() / 4)
			{
				if (config.use_glue)
					cleanClausesGlue(sat.clauses, sat.stats.nConfls() / 8);
				else
					cleanClausesSize(sat.clauses, sat.stats.nConfls() / 8);
				sat.clauses.compactify();
			}

			printHeader();
			printLine(sat);
		}
	}
}

} // namespace dawn
