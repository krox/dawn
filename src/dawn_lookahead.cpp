#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/dimacs.h"
#include "sat/sat.h"
#include "sat/solver.h"
#include <csignal>
#include <iostream>
#include <random>
#include <unistd.h>

static Sat sat;

extern "C" void interruptHandler(int)
{
	interrupt.store(true);
	signal(SIGINT, SIG_DFL); // remove the handler so that a second SIGINT will
	                         // abort the program
}

/**
 * Propagate x and backtracks immediately.
 * Returns -1 on conflict, and number of implied literals otherwise.
 * Also marks all implied lits in seen. (only useful if not conflicted)
 */
int probe(PropEngineLight &p, Lit x)
{
	p.mark();
	p.propagate(x);
	if (p.conflict)
	{
		p.unroll();
		return -1;
	}
	else
	{
		auto r = (int)p.trail(p.level()).size();
		p.unroll();
		return r;
	}
}

int main(int argc, char *argv[])
{
	// command line arguments
	std::string cnfFile, solFile;
	bool shuffle = false;
	int64_t seed = 0;
	int timeout = 0;
	CLI::App app{"sat solver"};
	app.add_option("input", cnfFile, "input CNF in dimacs format");
	app.add_option("output", solFile, "output solution in dimacs format");
	app.add_option("--max-time", timeout,
	               "stop solving after (approximately) this time (seconds)");
	app.add_flag("--shuffle", shuffle,
	             "shuffle the variables and their polarities before solving");
	app.add_option(
	    "--seed", seed,
	    "seed for random number generator (default=0, unpredictable=-1)");
	CLI11_PARSE(app, argc, argv);

	// read CNF from file or stdin
	parseCnf(cnfFile, sat);

	if (seed == -1)
		seed = std::random_device()();
	sat.rng.seed(seed);
	if (shuffle)
		shuffleVariables(sat);

	std::signal(SIGINT, &interruptHandler);
	if (timeout > 0)
	{
		std::signal(SIGALRM, &interruptHandler);
		alarm(timeout);
	}

	inprocessCheap(sat);

	// solve
	auto p = PropEngineLight(sat);
	std::vector<Lit> branches;
	size_t counter = 0;
	while (true)
	{
	again:
		assert(p.level() == (int)branches.size());
		// resolve conflicts by backtracking
		while (p.conflict)
		{
			// top-level conflict -> UNSAT
			if (branches.empty())
			{
				fmt::print("c UNSATISFIABLE\n");
				return 20;
			}

			// otherwise, backtrack one level and propagate inverse branch
			Lit a = branches.back();
			branches.pop_back();
			p.unroll();
			p.propagate(a.neg());
		}

		if (counter++ % 64 == 0)
		{
			fmt::print("c ({})", p.trail(0).size());
			for (int l = 1; l <= p.level(); ++l)
				fmt::print(" ({})", p.trail(l).size());
			fmt::print("\n");
		}

		// probe everything and select best branching variable
		int branch = -1;
		int bestScore = 0;
		bool change = false;
		for (int i = 0; i < sat.varCount(); ++i)
		{
			Lit a = Lit(i, false);
			if (p.assign[a] || p.assign[a.neg()])
				continue;

			int countA = probe(p, a);
			if (countA == -1)
			{
				change = true;
				p.propagate(a.neg());
				if (p.conflict)
					goto again;
				else
					continue;
			}

			int countB = probe(p, a.neg());
			if (countB == -1)
			{
				change = true;
				p.propagate(a);
				if (p.conflict)
					goto again;
				else
					continue;
			}

			if (countA + countB > bestScore)
			{
				bestScore = countA + countB;
				branch = i;
			}
		}

		if (change)
			goto again;

		// no branching var found -> everything is assigned -> SAT
		if (branch == -1)
		{
			fmt::print("c SATISFIABLE\n");
			return 10;
		}

		// do a branch
		p.mark();
		branches.push_back(Lit(branch, false));
		p.propagate(Lit(branch, false));
	}
}
