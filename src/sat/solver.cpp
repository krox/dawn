#include "sat/solver.h"

#include "fmt/format.h"
#include "sat/propengine.h"
#include "sat/scc.h"
#include <iomanip>

/** do one full sweep of failed literal probing */
void probe(PropEngine &p)
{
	assert(p.level() == 0);
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
			int backLevel = p.analyzeConflict(buf);
			assert(backLevel == 0);
			assert(buf.size() == 1);
			p.unroll(0);
			p.addClause(buf);
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

/** return true if solved (contradiction or solution found), false if maxConfl
 * reached */
bool search(PropEngine &p, uint64_t maxConfl)
{
	StopwatchGuard _(p.sat.stats.swSearch);

	uint64_t nConfl = 0;
	std::vector<Lit> buf;

	while (true)
	{
		// handle conflicts
		while (p.conflict)
		{
			nConfl += 1;

			// level 0 conflict -> UNSAT
			if (p.level() == 0)
				return true;

			// otherwise anaylze,unroll,learn
			int backLevel = p.analyzeConflict(buf);
			p.unroll(backLevel);
			Reason r = p.addClause(buf);
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
				p.unroll(0);
			return false;
		}

		// choose a branching variable
		// int branch = p.unassignedVariable();
		int branch = p.mostActiveVariable();

		// no unassigned left -> solution is found
		if (branch == -1)
		{
			std::cout << "c solution found after " << nConfl << " conflicts"
			          << std::endl;
			return true;
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

/** return true if solved, false if unsat */
bool solve(Sat &sat, Solution &sol)
{
	StopwatchGuard _(sat.stats.swTotal);

	// Step 1: Run unit-propagation and scc until completion. These are
	// extremely fast so we do them before anything more complicated.
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

	// Step 2: top-level failed-literal-probing.
	// TODO: this may need some kind of limit as it is potentially quite slow.
	auto p = std::make_unique<PropEngine>(sat);
	probe(*p);
	fmt::print("c after initial FLP: {} vars and {} clauses\n", sat.varCount(),
	           sat.clauseCount());

	// Step 3: main solver loop
	std::cout << "c " << std::setw(8) << "vars"
	          << " " << std::setw(8) << "units"
	          << " " << std::setw(8) << "bins"
	          << " " << std::setw(8) << "longs" << std::endl;

	int lastCleanup = 0;
	for (int iter = 0;; ++iter)
	{
		// print statistics line directly before going into the searcher
		std::cout << "c " << std::setw(8) << sat.varCount() << std::setw(8)
		          << sat.unaryCount() << " " << std::setw(8)
		          << sat.binaryCount() << " " << std::setw(8) << sat.longCount()
		          << " " << std::setw(8)
		          << sat.clauses.memory_usage() / 1024. / 1024. << " MiB"
		          << std::endl;

		// search for a number of conflicts
		assert(p->level() == 0);
		if (search(*p, 1000))
		{
			if (p->conflict)
				return false;
			sol.varCount(sat.varCountOuter());
			for (int i = 0; i < sat.varCountOuter(); ++i)
			{
				auto a = Lit(sat.outerToInner(Lit(i, false)));
				if (a.fixed())
				{
					sol.set(Lit(i, a.sign()));
				}
				else
				{
					assert(a.proper() && a.var() < sat.varCount());

					assert(p->assign[a] || p->assign[a.neg()]);
					assert(!(p->assign[a] && p->assign[a.neg()]));
					if (p->assign[a])
						sol.set(Lit(i, false));
					if (p->assign[a.neg()])
						sol.set(Lit(i, true));
				}
			}
			assert(sol.valid());
			return true;
		}

		// occasional cleanup when there are units/equivalences
		if (runSCC(sat) || sat.units.size() >= 100 ||
		    (sat.units.size() > 0 && iter - lastCleanup >= 10))
		{
			lastCleanup = iter;
			std::cout << "c cleanup" << std::endl;
			sat.cleanup();

			// runSCC/cleanup invalidates the PropEngine, so recreate it
			p = std::make_unique<PropEngine>(sat);
		}
	}
	return !p->conflict;
}
