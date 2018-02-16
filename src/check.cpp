#include <iostream>
#include <dimacs.h>
#include "sat.h"
#include "solver.h"

bool check(const ClauseSet& cs, const Solution& sol)
{
	if(cs.contradiction)
		return false;
	for(Lit a : cs.units)
		if(!sol.satisfied(a))
			return false;
	for(int i = 0; i < 2*(int)cs.varCount(); ++i)
		for(Lit b : cs.bins[Lit(i)])
			if(!sol.satisfied(Lit(i), b))
				return false;
	for(auto [i,c] : cs.clauses)
		if(!sol.satisfied(c))
			return false;
	return true;
}

int main(int argc, char *argv[])
{
	if(argc != 3)
	{
		std::cerr << "usage: check <cnf-file> <solution-file>" << std::endl;
		return -1;
	}

	ClauseSet cs;
	parseCnf(argv[1], cs);

	Solution sol;
	sol.varCount(cs.varCount());
	parseSolution(argv[2], sol);

	if(check(cs, sol))
	{
		std::cout << "c solution checked" << std::endl;
		return 0;
	}
	else
	{
		std::cout << "c SOLUTION CHECK FAILED" << std::endl;
		return -1;
	}
}
