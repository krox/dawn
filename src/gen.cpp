#include "fmt/format.h"
#include "sat/assignment.h"
#include "sat/dimacs.h"
#include "sat/sat.h"
#include <random>
#include <string>

using namespace dawn;

int main(int argc, char *argv[])
{
	if (argc > 3)
	{
		fmt::print("usage: gen <var-count> <clause-count>\n");
		return -1;
	}

	// NOTE: 4.26 is roughly the hardest clause/variable ratio for random
	//       3-sat instances, and also the phase transition between mostly
	//       satisfiable and mostly unsatisfiable instances. This program only
	//       generates satisfiable instances, so this fact might not be exactly
	//       applicable, but it is a reasonable default value nontheless.
	int varCount = argc >= 2 ? std::stoi(argv[1]) : 100;
	int clauseCount = argc >= 3 ? std::stoi(argv[2]) : (int)(4.26 * varCount);

	// random number generator
	std::random_device rd;
	std::mt19937 rng(rd());
	std::uniform_int_distribution<uint32_t> litDist(0, 2 * varCount - 1);
	std::bernoulli_distribution coinDist(0.5);

	// random solution
	Assignment sol(varCount);
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

	fmt::print("{}", sat);
}
