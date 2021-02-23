#include "sat/solver.h"

#include "fmt/format.h"
#include "sat/binary.h"
#include "sat/elimination.h"
#include "sat/probing.h"
#include "sat/propengine.h"
#include "sat/subsumption.h"
#include "sat/vivification.h"

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
	for (Lit a : p.trail())
	{
		outerProp.propagate(p.sat.innerToOuter(a));
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
std::optional<Solution> search(Sat &sat, int64_t maxConfl,
                               SolverConfig const &config)
{
	StopwatchGuard _(sat.stats.swSearch);

	printHeader();

	ActivityHeap activityHeap(sat);
	for (int i = 0; i < sat.varCount(); ++i)
		activityHeap.push(i);

	PropEngine p(sat);
	p.config.otf = config.otf;
	p.config.lhbr = config.lhbr;
	p.config.full_resolution = config.full_resolution;
	p.activity_heap = &activityHeap;

	int64_t nConfl = 0;
	int64_t lastPrint = INT64_MIN;

	std::vector<Lit> buf;

	while (true)
	{
		if (nConfl >= lastPrint + 1000)
		{
			lastPrint = nConfl;
			printLine(sat);
		}

		// handle conflicts
		while (p.conflict)
		{
			nConfl += 1;

			// level 0 conflict -> UNSAT
			if (p.level() == 0)
			{
				sat.addEmpty();
				printLine(sat);
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
			printLine(sat);
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
		{
			printLine(sat);
			return buildSolution(p);
		}

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

int unitPropagation(Sat &sat)
{
	// early out if no units
	if (!sat.contradiction && sat.units.empty())
		return 0;

	auto p = PropEngineLight(sat);

	// conflict -> add empty clause and remove everything else
	if (p.conflict)
	{
		sat.addEmpty();
		sat.units.resize(0);
		for (int i = 0; i < sat.varCount() * 2; ++i)
			sat.bins[i].resize(0);
		sat.clauses.clear();
		return 1;
	}

	assert(p.trail().size() != 0);

	auto trans = std::vector<Lit>(sat.varCount(), Lit::undef());
	for (Lit u : p.trail())
	{
		assert(trans[u.var()] != Lit::fixed(u.sign()).neg());
		trans[u.var()] = Lit::fixed(u.sign());
	}
	int newVarCount = 0;
	for (int i = 0; i < sat.varCount(); ++i)
	{
		if (trans[i] == Lit::undef())
			trans[i] = Lit(newVarCount++, false);
	}

	// NOTE: this renumber() changes sat and thus invalidates p
	sat.renumber(trans, newVarCount);
	assert(sat.units.empty());

	return (int)p.trail().size();
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

// Very cheap preprocessing: unit-propagation and SCC
int inprocessCheap(Sat &sat)
{
	Stopwatch sw;
	sw.start();

	int totalUP = 0;
	int totalSCC = 0;
	int iter = 0;
	for (;; ++iter) // in princinple, this loop should be capped...
	{
		if (int nFound = unitPropagation(sat); nFound)
			totalUP += nFound;
		if (int nFound = runSCC(sat); nFound)
			totalSCC += nFound;
		else
			break;
	}

	fmt::print("c UP+SCC ({} iterations) removed {} + {} variables in {:.2f}\n",
	           iter, totalUP, totalSCC, sw.secs());
	return totalUP + totalSCC;
}

/** run the full inprocessing */
void inprocess(Sat &sat, SolverConfig const &config)
{
	// printBinaryStats(sat);
	inprocessCheap(sat);

	// failed literal probing settings:
	// 0 = none
	// 1 = only run while very successful
	// 2 = run until everything is found
	// 3 = also run binary probing
	if (config.probing > 0)
		while (!interrupt)
		{
			if (probe(sat, config.probing >= 2 ? 0 : 10000) == 0)
				break;
			int fixed_vars = inprocessCheap(sat);
			if (config.probing <= 1 && fixed_vars < 10000)
				break;
		}

	if (config.probing >= 3)
		probeBinary(sat);

	// maybe-not-so-cheap preprocessing: subsumption+SSR
	if (config.subsume >= 1 && !interrupt)
	{
		bool changeA = subsumeBinary(sat);
		bool changeB = (config.subsume >= 2) && subsumeLong(sat);
		if (changeA || changeB)
		{
			if (config.subsume >= 3)
				return inprocess(sat, config);
			else
				inprocessCheap(sat);
		}
	}

	if (config.vivify)
	{
		if (run_vivification(sat))
			return inprocess(sat, config);
	}

	// cleanup
	// (do this last, because it cant lead to anything new for the other passes)
	if (config.tbr > 0)
		runBinaryReduction(sat);
}

int solve(Sat &sat, Solution &sol, SolverConfig const &config)
{
	StopwatchGuard _(sat.stats.swTotal);

	inprocess(sat, config);

	if (config.bve > 0)
	{
		int nRemoved = run_variable_elimination(sat);
		fmt::print("c BVE removed {} variables\n", nRemoved);
		if (nRemoved)
			inprocess(sat, config);
	}

	fmt::print("c after preprocessing: {} vars and {} clauses\n",
	           sat.varCount(), sat.clauseCount());

	// main solver loop
	for (int iter = 1;; ++iter)
	{
		// check limit
		if (sat.stats.nConfls() >= config.max_confls)
		{
			fmt::print("c conflict limit reached. abort solver.\n");
			return 30;
		}

		// search for a number of conflicts
		if (auto tmp = search(sat, 2000 * iter, config); tmp)
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

		// inprocessing
		std::cout << "c cleanup" << std::endl;
		inprocess(sat, config);

		if (interrupt)
		{
			fmt::print("c interrupted. abort solver.\n");
			return 30;
		}

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
	}
}
