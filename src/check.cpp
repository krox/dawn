#include "sat/dimacs.h"
#include "sat/sat.h"
#include "sat/solver.h"
#include <iostream>

bool check(const Sat &sat, const Solution &sol)
{
	if (sat.contradiction)
		return false;
	for (Lit a : sat.units)
		if (!sol.satisfied(a))
			return false;
	for (int i = 0; i < 2 * (int)sat.varCount(); ++i)
		for (Lit b : sat.bins[Lit(i)])
			if (!sol.satisfied(Lit(i), b))
				return false;
	for (auto [i, c] : sat.clauses)
		if (!sol.satisfied(c))
			return false;
	return true;
}

int main(int argc, char *argv[])
{
	if (argc != 3)
	{
		std::cerr << "usage: check <cnf-file> <solution-file>" << std::endl;
		return -1;
	}

	Sat sat;
	parseCnf(argv[1], sat);

	Solution sol;
	sol.varCount(sat.varCount());
	parseSolution(argv[2], sol);

	if (check(sat, sol))
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
