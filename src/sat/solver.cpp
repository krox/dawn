#include "sat/solver.h"

#include "sat/propengine.h"
#include <iomanip>
#include <iostream>

/** do one full sweep of failed literal probing */
void probe(PropEngine &p)
{
	assert(p.level() == 0);
	if (p.conflict)
		return;

	std::vector<Lit> buf;
	for (uint32_t i = 0; i < 2 * p.sat.varCount(); ++i)
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
			p.propagateFull(buf[0], REASON_UNDEF);
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
bool search(PropEngine &p, Solution &sol, uint64_t maxConfl)
{
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
			p.unroll(0);
			return false;
		}

		// choose a branching variable
		int branch = p.unassignedVariable();

		// no unassigned left -> solution is found
		if (branch == -1)
		{
			sol = p.assign;
			std::cout << "c solution found after " << nConfl << " conflicts"
			          << std::endl;
			return true;
		}

		// propagate branch
		p.branch(Lit(branch, false));
	}
}

/** return true if solved, false if unsat */
bool solve(Sat &sat, Solution &sol)
{
	auto p = std::make_unique<PropEngine>(sat);

	probe(*p);

	std::cout << "c " << std::setw(8) << "vars"
	          << " " << std::setw(8) << "bins"
	          << " " << std::setw(8) << "longs" << std::endl;

	while (true)
	{
		assert(p->level() == 0);
		if (p->trail.size() > sat.units.size())
		{
			sat.units = p->trail;
			sat.cleanup();
			p = std::make_unique<PropEngine>(sat);
		}

		std::cout << "c " << std::setw(8) << sat.varCount() - sat.unaryCount()
		          << " " << std::setw(8) << sat.binaryCount() << " "
		          << std::setw(8) << sat.longCount() << std::endl;
		if (search(*p, sol, 1000))
			break;
	}
	return !p->conflict;
}
