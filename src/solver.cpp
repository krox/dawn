#include "solver.h"
#include <iostream>

/** return true if solved, false if unsat */
bool solveSimple(ClauseSet& cs, Solution& sol, bool doProbing)
{
	uint64_t nConfl = 0;
	PropEngine p(cs);

	std::vector<Lit> branches;

	if(cs.contradiction) // NOTE: do this after PropEngine constructor
		return false;

	while(true)
	{
		// choose a branching variable
		int branch = doProbing ? p.probeFull() : p.unassignedVariable();

		if(branch == -2)
			goto handle_conflict;

		if(branch == -1) // no unassigned left -> solution is found
		{
			sol = p.assign;
			std::cout << "c solution found after " << nConfl << " conflicts" << std::endl;
			return true;
		}

		// propagate branch
		p.newLevel();
		branches.push_back(Lit(branch, false));
		if(p.propagateFull(Lit(branch, false)))
			continue;

		// handle conflicts
		handle_conflict:
		while(true)
		{
			nConfl += 1;
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
