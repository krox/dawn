#include "sat/solver.h"

#include "fmt/format.h"
#include "sat/binary.h"
#include "sat/propengine.h"
#include "sat/subsumption.h"
#include <iomanip>

/**
 * Do one sweep of failed literal probing
 *   - only tries at roots of implication graph
 *   - does UIP analysis in case something is found
 *   - does not use or modify polarity/activity of variables
 */
int probe(Sat &sat)
{
	PropEngine p(sat);
	if (p.conflict)
		return 0;

	// list and shuffle candidates
	std::vector<Lit> candidates;
	for (int i = 0; i < 2 * sat.varCount(); ++i)
	{
		auto l = Lit(i);
		if (sat.bins[l.neg()].empty())
			continue;
		if (!sat.bins[l].empty())
			continue;

		candidates.push_back(l);
		auto dist =
		    std::uniform_int_distribution<size_t>(0, candidates.size() - 1);
		auto k = dist(sat.stats.rng);
		std::swap(candidates.back(), candidates[k]);
	}

	if (candidates.size() > 10000)
		candidates.resize(10000);
	std::sort(candidates.begin(), candidates.end());

	int nTries = 0, nFails = 0;
	std::vector<Lit> buf;

	for (Lit branch : candidates)
	{
		// skip fixed literals
		if (p.assign[branch] || p.assign[branch.neg()])
			continue;

		// skip non-roots (former roots might have become non-roots)
		if (sat.bins[branch.neg()].empty() || !sat.bins[branch].empty())
			continue;

		nTries += 1;

		p.branch(branch);

		if (p.conflict) // literal failed -> analyze and learn unit
		{
			nFails += 1;
			int backLevel = p.analyzeConflict(buf);
			assert(backLevel == 0);
			assert(buf.size() == 1);
			p.unroll(0);
			p.addLearntClause(buf, 1);
			p.propagateFull(buf[0], Reason::undef());
			buf.resize(0);

			// UNSAT encountered
			if (p.conflict)
				return 1;
		}
		else // no fail -> do nothing
		{
			p.unroll(0);
		}
	}

	return nFails;
}

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
	    sat.clauses.memory_usage() / 1024. / 1024.);
}

Solution buildSolution(const PropEngine &p)
{
	auto sol = Solution(p.sat.varCountOuter());
	for (int i = 0; i < p.sat.varCountOuter(); ++i)
	{
		auto a = Lit(p.sat.outerToInner(Lit(i, false)));
		if (a.fixed())
		{
			sol.set(Lit(i, a.sign()));
		}
		else
		{
			assert(a.proper() && a.var() < p.sat.varCount());

			assert(p.assign[a] || p.assign[a.neg()]);
			assert(!(p.assign[a] && p.assign[a.neg()]));
			if (p.assign[a])
				sol.set(Lit(i, false));
			if (p.assign[a.neg()])
				sol.set(Lit(i, true));
		}
	}
	assert(sol.valid());
	return sol;
}

/** return true if solved (contradiction or solution found), false if maxConfl
 * reached */
std::optional<Solution> search(Sat &sat, int64_t maxConfl)
{
	StopwatchGuard _(sat.stats.swSearch);

	printHeader();

	PropEngine p(sat);
	ActivityHeap activityHeap(sat);
	for (int i = 0; i < sat.varCount(); ++i)
		activityHeap.push(i);

	int64_t nConfl = 0;
	int64_t lastPrint = INT64_MIN;

	std::vector<Lit> buf;

	auto callback = [&](Lit l) {
		sat.bumpVariableActivity(l.var());
		activityHeap.update(l.var());
	};

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
			int backLevel = p.analyzeConflict(buf, callback);
			sat.decayVariableActivity();
			auto glue = p.calcGlue(buf);
			sat.stats.nLearnt += 1;
			sat.stats.nLitsLearnt += buf.size();

			// unroll to apropriate level and propagate new learnt clause
			p.unroll_and_activate(backLevel, activityHeap);
			Reason r = p.addLearntClause(buf, glue);
			p.propagateFull(buf[0], r);
			for (Lit x : p.trail(p.level()))
				sat.polarity[x.var()] = x.sign();

			buf.resize(0);
		}

		/** maxConfl reached -> unroll and exit */
		if (nConfl > maxConfl || sat.stats.interrupt)
		{
			if (p.level() > 0)
				p.unroll_and_activate(0, activityHeap);
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

		// propagate branch
		p.branch(Lit(branch, sat.polarity[branch]));
		for (Lit x : p.trail(p.level()))
			sat.polarity[x.var()] = x.sign();
	}
}

int unitPropagation(Sat &sat)
{
	if (sat.contradiction || sat.unaryCount() == 0)
		return 0;

	// TODO: a "light" version of PropEngine would be sufficient here,
	//       withouth any conflict-analysis and such
	auto p = PropEngine(sat);
	int nFound;
	if (p.conflict)
	{
		nFound = 1;
		sat.addEmpty();
	}
	else
	{
		sat.units.assign(p.trail().begin(), p.trail().end());
		nFound = (int)sat.units.size();
	}

	sat.cleanup();
	assert(sat.unaryCount() == 0);
	return nFound;
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
void inprocessCheap(Sat &sat)
{
	while (true)
	{
		if (int nFound = unitPropagation(sat); nFound)
			fmt::print("c  UP removed {} variables\n", nFound);
		else if (int nFound = runSCC(sat); nFound)
			fmt::print("c SCC removed {} variables\n", nFound);
		else
			break;
	}
}

void inprocess(Sat &sat)
{
	printBinaryStats(sat);
	inprocessCheap(sat);

	for (int iter = 0; iter < 5 && !sat.stats.interrupt; ++iter)
	{
		printBinaryStats(sat);
		if (int nFound = probe(sat); nFound)
		{
			fmt::print("c FLP found {} failing literals\n", nFound);
			inprocessCheap(sat);
		}
		else
			break;
	}

	// maybe-not-so-cheap preprocessing: subsumption+SSR
	if (sat.stats.subsume >= 1 && !sat.stats.interrupt)
	{
		subsumeBinary(sat);
		if (sat.stats.subsume >= 2)
			subsumeLong(sat);
		inprocessCheap(sat);
	}
}

/** returns 10 for SAT, 20 for UNSAT, 30 for UNKNOWN (timeout or similar) */
int solve(Sat &sat, Solution &sol)
{
	StopwatchGuard _(sat.stats.swTotal);

	inprocess(sat);

	fmt::print("c after preprocessing: {} vars and {} clauses\n",
	           sat.varCount(), sat.clauseCount());

	// main solver loop
	for (int iter = 0;; ++iter)
	{
		// check limit
		if (sat.stats.nConfls() >= sat.stats.maxConfls)
		{
			fmt::print("c conflict limit reached. abort solver.\n");
			return 30;
		}

		// search for a number of conflicts
		if (auto tmp = search(sat, 10000); tmp)
		{
			if (sat.contradiction)
				return 20;
			sol = *tmp;
			return 10;
		}

		if (sat.stats.interrupt)
		{
			fmt::print("c interrupted. abort solver.\n");
			return 30;
		}

		// inprocessing
		std::cout << "c cleanup" << std::endl;
		inprocess(sat);

		if (sat.stats.interrupt)
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
			if (cl.size() > sat.stats.maxLearntSize ||
			    cl.glue > sat.stats.maxLearntGlue)
				cl.remove();
		}
		if ((int64_t)sat.longCountRed() > sat.stats.maxLearnt)
		{
			if (sat.stats.useGlue)
				cleanClausesGlue(sat.clauses, sat.stats.maxLearnt);
			else
				cleanClausesSize(sat.clauses, sat.stats.maxLearnt);
			sat.cleanup();
		}
		if (sat.longCountRed() > (size_t)sat.stats.nConfls() / 4)
		{
			if (sat.stats.useGlue)
				cleanClausesGlue(sat.clauses, sat.stats.nConfls() / 8);
			else
				cleanClausesSize(sat.clauses, sat.stats.nConfls() / 8);
			sat.cleanup();
		}
	}
}
