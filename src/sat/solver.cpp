#include "sat/solver.h"

#include "fmt/format.h"
#include "sat/binary.h"
#include "sat/probing.h"
#include "sat/propengine.h"
#include "sat/subsumption.h"

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

/** returns solution if found, or std::nullopt if limits reached or
 * contradiction */
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
			int backLevel;
			uint8_t glue;
			if (sat.stats.fullResolution)
			{
				backLevel = p.analyzeConflictFull(buf, callback);
				glue = buf.size() > 255 ? 255 : (uint8_t)buf.size();
				assert(glue == p.calcGlue(buf));
			}
			else
			{
				backLevel = p.analyzeConflict(buf, callback);
				glue = p.calcGlue(buf);
			}

			sat.decayVariableActivity();
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
int inprocessCheap(Sat &sat)
{
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

	fmt::print("c UP+SCC ({} iterations) removed {} + {} variables\n", iter,
	           totalUP, totalSCC);
	return totalUP + totalSCC;
}

/** run the full inprocessing, as configured in sat.stats */
void inprocess(Sat &sat)
{
	// printBinaryStats(sat);
	inprocessCheap(sat);

	// failed literal probing settings:
	// 0 = none
	// 1 = only run while very successful
	// 2 = run until everything is found
	if (sat.stats.probing == 1)
		while (!sat.stats.interrupt)
		{
			int nFound = probe(sat, 10000);
			fmt::print("c FLP (partial) found {} failing literals\n", nFound);
			if (nFound == 0)
				break;
			if (inprocessCheap(sat) < 10000)
				break;
		}

	if (sat.stats.probing >= 2)
		while (!sat.stats.interrupt)
		{
			int nFound = probe(sat, 0);
			fmt::print("c FLP (full) found {} failing literals\n", nFound);
			if (nFound == 0)
				break;
			inprocessCheap(sat);
		}

	// maybe-not-so-cheap preprocessing: subsumption+SSR
	if (sat.stats.subsume >= 1 && !sat.stats.interrupt)
	{
		subsumeBinary(sat);
		if (sat.stats.subsume >= 2)
			subsumeLong(sat);
		inprocessCheap(sat);
	}

	// cleanup
	// (do this last, because it cant lead to anything new for the other passes)
	if (sat.stats.tbr > 0)
		runBinaryReduction(sat);
}

int solve(Sat &sat, Solution &sol)
{
	StopwatchGuard _(sat.stats.swTotal);

	inprocess(sat);

	fmt::print("c after preprocessing: {} vars and {} clauses\n",
	           sat.varCount(), sat.clauseCount());

	// main solver loop
	for (int iter = 1;; ++iter)
	{
		// check limit
		if (sat.stats.nConfls() >= sat.stats.maxConfls)
		{
			fmt::print("c conflict limit reached. abort solver.\n");
			return 30;
		}

		// search for a number of conflicts
		if (auto tmp = search(sat, 2000 * iter); tmp)
		{
			assert(!sat.contradiction);
			sol = *tmp;
			return 10;
		}

		if (sat.contradiction)
			return 20;

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
