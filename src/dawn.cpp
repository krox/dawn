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
	sat.stats.interrupt.store(true);
	signal(SIGINT, SIG_DFL); // remove the handler so that a second SIGINT will
	                         // abort the program
}

int main(int argc, char *argv[])
{
	// command line arguments
	std::string cnfFile, solFile;
	bool shuffle = false;
	int64_t seed = 0;
	int timeout = 0;
	bool allSolutions = false;
	CLI::App app{"sat solver"};
	app.add_option("input", cnfFile, "input CNF in dimacs format");
	app.add_option("output", solFile, "output solution in dimacs format");
	app.add_flag("--all", allSolutions,
	             "find all solutions instead of just one");
	app.add_flag("--watch-stats", sat.stats.watchStats,
	             "print watchlist statistics");
	app.add_option("--otf", sat.stats.otf,
	               "on-the-fly strengthening of learnt clauses"
	               "(0=off, 1=basic, 2=recursive=default)");
	app.add_option("--branch-dominating", sat.stats.branchDom,
	               "branch on dominating literal instead of chosen one itself"
	               "0=off, 1=matching polarity only, 2=always");
	app.add_option("--subsume", sat.stats.subsume,
	               "subsumption and self-subsuming resolution"
	               "(0=off, 1=binary, 2=full=default, 3=full until fixpoint)");
	app.add_option("--probing", sat.stats.probing,
	               "failed-literal probing"
	               "(0=off, 1=limited, 2=full)");
	app.add_option("--tbr", sat.stats.tbr,
	               "transitive reduction for binaries"
	               "(0=off, 2=full)");
	app.add_option("--max-learnt-size", sat.stats.maxLearntSize,
	               "learnt clauses larger than this are removed very quickly "
	               "independent of cleaning strategy");
	app.add_option("--max-learnt-glue", sat.stats.maxLearntGlue);
	app.add_option("--max-learnt", sat.stats.maxLearnt);
	app.add_flag("--lhbr", sat.stats.lhbr, "lazy hyper-binary resolution");
	app.add_flag("--full-resolution", sat.stats.fullResolution,
	             "learn by full resolution instead of UIP (default=off)");
	app.add_flag("--use-glue", sat.stats.useGlue,
	             "use glue for clause-cleaning (default=true)");
	app.add_option("--max-confls", sat.stats.maxConfls,
	               "stop solving after (approximately) this many conflicts");
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
	sat.stats.rng.seed(seed);
	if (shuffle)
		shuffleVariables(sat);

	std::signal(SIGINT, &interruptHandler);
	if (timeout > 0)
	{
		std::signal(SIGALRM, &interruptHandler);
		alarm(timeout);
	}

	// solve
	int result = 10;
	while (result == 10)
	{
		Solution sol;
		result = solve(sat, sol);

		// print to stdout
		if (result == 10)
		{
			std::cout << "s SATISFIABLE" << std::endl;
			if (solFile == "")
				std::cout << sol << std::endl;
		}
		else if (result == 20)
			std::cout << "s UNSATISFIABLE" << std::endl;
		else if (result == 30)
			std::cout << "s UNKNOWN" << std::endl;
		else
			assert(false);

		// print to file
		if (solFile != "")
		{
			std::ofstream f(solFile, std::ofstream::out);
			if (result == 10)
			{
				f << "s SATISFIABLE" << std::endl;
				f << sol << std::endl;
			}
			else if (result == 20)
				f << "s UNSATISFIABLE" << std::endl;
			else if (result == 30)
				f << "s UNKNOWN" << std::endl;
			else
				assert(false);
		}

		// if all solutions are requestes, add a clause excluding the current
		// solution and start again
		if (allSolutions && result == 10)
		{
			assert(sol.valid());
			std::vector<Lit> cl;
			for (int i = 0; i < sol.varCount(); ++i)
				if (sol.satisfied(Lit(i, false)))
					cl.push_back(Lit(i, true));
				else
					cl.push_back(Lit(i, false));
			sat.addClauseOuter(cl);
		}
		else
			break;
	}

	// statistics
	sat.stats.dump();
	return result; // 10/20/30 return code exactly like cryptominisat
}
