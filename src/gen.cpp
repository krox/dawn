#include "sat/dimacs.h"
#include "sat/solution.h"
#include <iostream>
#include <random>
#include <string>

using namespace dawn;

int main(int argc, char *argv[])
{
	if (argc != 3)
	{
		std::cerr << "usage: gen <var-count> <clause-count>" << std::endl;
		return -1;
	}

	auto varCount = std::stoi(argv[1]);
	auto clauseCount = std::stoi(argv[2]);

	// random number generator
	std::random_device rd;
	std::mt19937 rng(rd());
	std::uniform_int_distribution<uint32_t> litDist(0, 2 * varCount - 1);
	std::bernoulli_distribution coinDist(0.5);

	// random solution
	Solution sol(varCount);
	for (int i = 0; i < varCount; ++i)
		sol.set(Lit(i, coinDist(rng)));

	// generate clauses that are satisfied by the solution
	Sat sat(varCount);
	std::vector<Lit> cl;
	for (int ci = 0; ci < clauseCount;)
	{
		while (cl.size() < 3)
		{
			Lit a = Lit(litDist(rng));
			for (Lit b : cl)
				if (a.var() == b.var())
					goto next_lit;
			cl.push_back(a);
		next_lit:;
		}

		if (sol.satisfied(cl))
		{
			++ci;
			sat.addClause(cl, true);
		}

		cl.resize(0);
	}
	std::cout << "p cnf " << varCount << " " << clauseCount << std::endl;
	std::cout << sat;
}
