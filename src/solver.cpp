#include "solver.h"

/** return true if solved, false if unsat */
bool solve(ClauseSet& cs, Solution& sol)
{
	PropEngine p(cs);

	std::vector<Lit> branches;

	if(cs.contradiction) // NOTE: do this after PropEngine constructor
		return false;

	while(true)
	{
		// choose a branching variable
		int branch = p.unassignedVariable();
		if(branch == -1) // no unassigned left -> solution is found
		{
			sol = p.assign;
			return true;
		}

		// propagate branch
		p.newLevel();
		branches.push_back(Lit(branch, false));
		if(p.propagateFull(Lit(branch, false)))
			continue;

		// handle conflicts
		while(true)
		{
			assert(p.level() == (int)branches.size());

			// level 0 conflict -> UNSAT
			if(p.level() == 0)
				return false;

			// unroll last descision and propagate opposite literal
			p.unrollLevel(p.level()-1);
			auto l = branches.back().neg();
			branches.pop_back();
			if(p.propagateFull(l))
				break;
		}
	}
}
