#include "solver.h"

std::vector<bool> solve(ClauseSet& cs)
{
	PropEngine p(cs);
	std::vector<bool> sol;

	std::vector<Lit> branches;

	if(cs.contradiction) // NOTE: do this after PropEngine constructor
		return sol;

	while(true)
	{
		// choose a branching variable
		int branch = p.unassignedVariable();
		if(branch == -1) // no unassigned left -> solution is found
		{
			sol = p.assign;
			return sol;
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
				return sol;

			// unroll last descision and propagate opposite literal
			p.unrollLevel(p.level()-1);
			auto l = branches.back().neg();
			branches.pop_back();
			if(p.propagateFull(l))
				break;
		}
	}
}
