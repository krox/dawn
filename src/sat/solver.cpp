#include "sat/solver.h"

#include "fmt/format.h"
#include "sat/propengine.h"
#include "sat/scc.h"
#include "sat/subsumption.h"
#include <iomanip>

/** do one full sweep of failed literal probing */
void probe(Sat &sat)
{
	ActivityHeap dummy(sat);
	PropEngine p(sat);
	if (p.conflict)
		return;

	std::vector<Lit> buf;
	for (int i = 0; i < 2 * p.sat.varCount(); ++i)
	{
		Lit branch = Lit(i);

		// skip fixed literals
		if (p.assign[branch] || p.assign[branch.neg()])
			continue;

		// only do roots of the binary implication graph
		if (p.sat.bins[branch.neg()].empty())
			continue;
		if (!p.sat.bins[branch].empty())
			continue;

		p.branch(branch);

		if (p.conflict) // literal failed -> analyze and learn unit
		{
			int backLevel = p.analyzeConflict(buf, dummy);
			assert(backLevel == 0);
			assert(buf.size() == 1);
			p.unroll(0);
			p.addClause(buf, false);
			p.propagateFull(buf[0], Reason::undef());
			buf.resize(0);

			// UNSAT encountered
			if (p.conflict)
				return;
		}
		else // no fail -> do nothing
		{
			p.unroll(0);
		}
	}
}

static void printHeader()
{
	fmt::print("c     vars    units     bins    longs   learnt learnt-size\n");
}

static void printLine(Sat &sat)
{
	fmt::print("c {:#8} {:#8} {:#8} {:#8} {:#8} {:5.2f} {:8.2f} MiB\n",
	           sat.varCount(), sat.unaryCount(), sat.binaryCount(),
	           sat.longCountIrred(), sat.longCountRed(),
	           (double)sat.litCountRed() / sat.longCountRed(),
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

			// otherwise anaylze,unroll,learn
			int backLevel = p.analyzeConflict(buf, activityHeap);
			p.unroll(backLevel, activityHeap);
			p.sat.stats.nLearnt += 1;
			Reason r = p.addClause(buf, false);
			assert(!p.assign[buf[0]] && !p.assign[buf[0].neg()]);
			for (int i = 1; i < (int)buf.size(); ++i)
				assert(p.assign[buf[i].neg()]);
			p.propagateFull(buf[0], r);
			buf.resize(0);
		}

		/** maxConfl reached -> unroll and exit */
		if (nConfl > maxConfl)
		{
			if (p.level() > 0)
				p.unroll(0, activityHeap);
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
		p.branch(Lit(branch, false));
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
		sat.units = p.trail;
		nFound = (int)sat.units.size();
	}

	sat.cleanup();
	assert(sat.unaryCount() == 0);
	return nFound;
}

void cleanClauses(ClauseStorage &clauses, size_t nKeep)
{
	std::vector<std::vector<CRef>> list(64);
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

/** returns 10 for SAT, 20 for UNSAT, 30 for UNKNOWN (timeout or similar) */
int solve(Sat &sat, Solution &sol)
{
	StopwatchGuard _(sat.stats.swTotal);

	// Very cheap preprocessing: unit-propagation and SCC
	while (true)
	{
		if (int nFound = unitPropagation(sat); nFound)
			fmt::print("c  UP removed {} variables\n", nFound);
		else if (int nFound = runSCC(sat); nFound)
			fmt::print("c SCC removed {} variables\n", nFound);
		else
			break;
	}
	fmt::print("c after initial cleanup: {} vars and {} clauses\n",
	           sat.varCount(), sat.clauseCount());

	// maybe-not-so-cheap preprocessing: subsumption+SSR and FLP
	subsumeBinary(sat);
	probe(sat);
	fmt::print("c after initial FLP and subsumption: {} vars and {} clauses\n",
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

		std::cout << "c cleanup" << std::endl;
		unitPropagation(sat);
		runSCC(sat);
		subsumeBinary(sat);

		for (auto [ci, cl] : sat.clauses)
		{
			(void)ci;
			if (!cl.irred() && cl.size() > sat.stats.maxLearntSize)
				cl.remove();
		}

		sat.cleanup();

		if (sat.longCountRed() > (size_t)sat.stats.nConfls() / 2)
		{
			cleanClauses(sat.clauses, sat.stats.nConfls() / 4);
			sat.cleanup();
		}
	}
}
