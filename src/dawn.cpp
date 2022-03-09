#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/dimacs.h"
#include "sat/sat.h"
#include "sat/solver.h"
#include <csignal>
#include <cstdio>
#include <random>
#include <unistd.h>

using namespace dawn;

extern "C" void interruptHandler(int)
{
	interrupt.store(true);
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
	bool watch_stats = false;
	SolverConfig config;
	CLI::App app{"sat solver"};

	// general options and limits
	app.add_option("input", cnfFile, "input CNF in dimacs format");
	app.add_option("output", solFile, "output solution in dimacs format");
	app.add_flag("--all", allSolutions,
	             "find all solutions instead of just one");
	app.add_option("--max-confls", config.max_confls,
	               "stop solving after (approximately) this many conflicts");
	app.add_option("--max-time", timeout,
	               "stop solving after (approximately) this time (seconds)");

	// options for the CDCL search
	app.add_option("--otf", config.otf,
	               "on-the-fly strengthening of learnt clauses"
	               "(0=off, 1=basic, 2=recursive=default)");
	app.add_flag("--lhbr", config.lhbr, "lazy hyper-binary resolution");
	app.add_flag("--full-resolution", config.full_resolution,
	             "learn by full resolution instead of UIP (default=off)");
	app.add_option("--branch-dominating", config.branch_dom,
	               "branch on dominating literal instead of chosen one itself"
	               "0=off, 1=matching polarity only, 2=always");

	// clause cleaning
	app.add_option("--max-learnt-size", config.max_learnt_size,
	               "learnt clauses larger than this are removed very quickly "
	               "independent of cleaning strategy");
	app.add_option("--max-learnt-glue", config.max_learnt_glue);
	app.add_option("--max-learnt", config.max_learnt);

	app.add_flag("--use-glue", config.use_glue,
	             "use glue for clause-cleaning (default=true)");

	// restarts
	app.add_option("--restart-type", config.restart_type,
	               "constant, linear, geometric, luby");
	app.add_option("--restart-base", config.restart_base,
	               "base multiplier (default=100)");
	app.add_option("--restart-mult", config.restart_mult,
	               "multiplier for geometric restart (default=1.1)");

	// inprocessing options
	app.add_option("--probing", config.probing,
	               "failed-literal probing"
	               "(0=off, 1=limited=default, 2=full, 3=full+binary)");
	app.add_option("--subsume", config.subsume,
	               "subsumption and self-subsuming resolution"
	               "(0=off, 1=binary, 2=full=default)");
	app.add_option("--tbr", config.tbr,
	               "transitive reduction for binaries"
	               "(0=off, 2=full)");
	app.add_option("--vivify", config.vivify,
	               "clause vivification"
	               "(0=off, 1=normal, 2=also binary strengthen)");
	app.add_option("--bve", config.bve, "bounded variable elimination");
	app.add_option("--bva", config.bva, "bounded variable addition");
	app.add_option("--inprocess-iters", config.inprocessIters,
	               "immediately repeat inprocessing if anything was found "
	               "(default = 1 = probably enough)");

	// other options
	app.add_flag("--watch-stats", watch_stats, "print watchlist statistics");
	app.add_option(
	    "--seed", seed,
	    "seed for random number generator (default=0, unpredictable=-1)");
	app.add_flag("--shuffle", shuffle,
	             "shuffle the variables and their polarities before solving");
	CLI11_PARSE(app, argc, argv);

	// read CNF from file or stdin
	util::Stopwatch sw;
	sw.start();
	auto [originalClauses, varCount] = parseCnf(cnfFile);
	sw.stop();
	Sat sat = Sat(varCount, originalClauses); // clauses are copied here!
	sat.stats.swParsing = sw;

	if (seed == -1)
		seed = std::random_device()();
	sat.rng.seed(seed);
	if (shuffle)
		shuffleVariables(sat);
	sat.stats.watch_stats = watch_stats;

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
		Assignment sol;
		result = solve(sat, sol, config);

		// print to stdout
		if (result == 10)
		{
			fmt::print("s SATISFIABLE\n");
			if (sol.satisfied(originalClauses))
				std::cout << "s solution checked" << std::endl;
			else
			{
				std::cout << "s SOLUTION CHECK FAILED" << std::endl;
				return -1;
			}
		}
		else if (result == 20)
			fmt::print("s UNSATISFIABLE\n");
		else if (result == 30)
			fmt::print("s UNKNOWN\n");
		else
			assert(false);

		// print to file
		if (solFile != "")
		{
			auto file = fmt::output_file(solFile);
			if (result == 10)
			{
				file.print("s SATISFIABLE\n");

				file.print("v {} 0\n");
				file.print(" 0\n");
			}
			else if (result == 20)
				file.print("s UNSATISFIABLE\n");
			else if (result == 30)
				file.print("s UNKNOWN\n");
			else
				assert(false);
		}

		// if all solutions are requestes, add a clause excluding the current
		// solution and start again
		if (allSolutions && result == 10)
		{
			assert(sol.complete());
			std::vector<Lit> cl;
			for (int i = 0; i < sol.var_count(); ++i)
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
