#include "CLI/CLI.hpp"
#include "sat/dimacs.h"
#include "sat/sat.h"
#include "sat/solver.h"
#include "sat/stats.h"
#include <csignal>
#include <string>

using namespace dawn;

extern "C" void interruptHandler(int);

namespace {
struct Options
{
	std::string cnfFile, solFile;
	bool shuffle = false;
	int64_t seed = 0;
	int timeout = 0;
	bool watch_stats = false;
	SolverConfig config;
};

void run_solve_command(Options opt)
{
	// read CNF from file or stdin
	util::Stopwatch sw;
	sw.start();
	auto [originalClauses, varCount] = parseCnf(opt.cnfFile);
	sw.stop();
	Sat sat = Sat(varCount, originalClauses); // clauses are copied here!
	sat.stats.swParsing = sw;

	if (opt.seed == -1)
		opt.seed = std::random_device()();
	sat.rng.seed(opt.seed);
	if (opt.shuffle)
		shuffleVariables(sat);
	sat.stats.watch_stats = opt.watch_stats;

	std::signal(SIGINT, &interruptHandler);
	if (opt.timeout > 0)
	{
		std::signal(SIGALRM, &interruptHandler);
		alarm(opt.timeout);
	}

	// solve
	int result = 10;
	while (result == 10)
	{
		Assignment sol;
		result = solve(sat, sol, opt.config);

		// print to stdout
		if (result == 10)
		{
			fmt::print("s SATISFIABLE\n");
			if (sol.satisfied(originalClauses))
				std::cout << "s solution checked" << std::endl;
			else
			{
				std::cout << "s SOLUTION CHECK FAILED" << std::endl;
				std::exit(-1);
			}
		}
		else if (result == 20)
			fmt::print("s UNSATISFIABLE\n");
		else if (result == 30)
			fmt::print("s UNKNOWN\n");
		else
			assert(false);

		// print to file
		if (opt.solFile != "")
		{
			auto file = fmt::output_file(opt.solFile);
			if (result == 10)
			{
				file.print("s SATISFIABLE\n");
				file.print("v {} 0\n", sol);
			}
			else if (result == 20)
				file.print("s UNSATISFIABLE\n");
			else if (result == 30)
				file.print("s UNKNOWN\n");
			else
				assert(false);
		}

		break;
	}

	// statistics
	sat.stats.dump();
	std::exit(result);
}
} // namespace

void setup_solve_command(CLI::App &app)
{
	auto opt = std::make_shared<Options>();

	// input/output
	app.add_option("input", opt->cnfFile, "input CNF in dimacs format")
	    ->type_name("<filename>");
	app.add_option("output", opt->solFile, "output solution in dimacs format")
	    ->type_name("<filename>");

	// general options
	auto g = "Options";
	app.add_option("--max-confls", opt->config.max_confls,
	               "stop solving after (approximately) this many conflicts")
	    ->group(g);
	app.add_option("--max-time", opt->timeout,
	               "stop solving after (approximately) this time (seconds)")
	    ->group(g);
	app.add_option(
	       "--seed", opt->seed,
	       "seed for random number generator (default=0, unpredictable=-1)")
	    ->group(g);
	app.add_flag("--shuffle", opt->shuffle,
	             "shuffle the variables and their polarities before solving")
	    ->group(g);

	// options for the CDCL search
	g = "Clause Learning";
	app.add_option("--otf", opt->config.otf,
	               "on-the-fly strengthening of learnt clauses"
	               "(0=off, 1=basic, 2=recursive=default)")
	    ->group(g);
	app.add_flag("--full-resolution", opt->config.full_resolution,
	             "learn by full resolution instead of UIP (default=off)")
	    ->group(g);
	app.add_option("--branch-dominating", opt->config.branch_dom,
	               "branch on dominating literal instead of chosen one itself"
	               "0=off, 1=matching polarity only, 2=always")
	    ->group(g);

	// clause cleaning
	g = "Clause Cleaning";
	app.add_option("--max-learnt-size", opt->config.max_learnt_size,
	               "learnt clauses larger than this are removed very quickly "
	               "independent of cleaning strategy")
	    ->group(g);
	app.add_option("--max-learnt-glue", opt->config.max_learnt_glue)->group(g);
	app.add_option("--max-learnt", opt->config.max_learnt)->group(g);

	app.add_flag("--use-glue", opt->config.use_glue,
	             "use glue for clause-cleaning (default=true)")
	    ->group(g);

	// restarts
	g = "Restarts";
	app.add_option("--restart-type", opt->config.restart_type,
	               "constant, linear, geometric, luby")
	    ->group(g);
	app.add_option("--restart-base", opt->config.restart_base,
	               "base multiplier (default=100)")
	    ->group(g);
	app.add_option("--restart-mult", opt->config.restart_mult,
	               "multiplier for geometric restart (default=1.1)")
	    ->group(g);

	// inprocessing options
	g = "Inprocessing";
	app.add_option("--probing", opt->config.probing,
	               "failed-literal probing"
	               "(0=off, 1=limited=default, 2=full, 3=full+binary)")
	    ->group(g);
	app.add_option("--subsume", opt->config.subsume,
	               "subsumption and self-subsuming resolution"
	               "(0=off, 1=binary, 2=full=default)")
	    ->group(g);
	app.add_option("--tbr", opt->config.tbr,
	               "transitive reduction for binaries"
	               "(0=off, 2=full)")
	    ->group(g);
	app.add_option("--vivify", opt->config.vivify,
	               "clause vivification"
	               "(0=off, 1=normal, 2=also binary strengthen, 3=also learnt)")
	    ->group(g);
	app.add_option("--bve", opt->config.bve, "bounded variable elimination")
	    ->group(g);
	app.add_option("--bva", opt->config.bva, "bounded variable addition")
	    ->group(g);
	app.add_option("--inprocess-iters", opt->config.inprocessIters,
	               "immediately repeat inprocessing if anything was found "
	               "(default = 1 = probably enough)")
	    ->group(g);

	// verbosity
	g = "Verbosity";
	app.add_flag("--watch-stats", opt->watch_stats,
	             "print watchlist statistics after solving")
	    ->group(g);
	app.add_flag_function(
	       "--silent", [](int64_t) { Logger::set_level(Logger::Level::warn); },
	       "remove most logging")
	    ->group(g);
	app.add_option("--debug", "increase verbosity of some component")
	    ->multi_option_policy(CLI::MultiOptionPolicy::TakeAll)
	    ->each(
	        [](std::string s) { Logger::set_level(s, Logger::Level::debug); })
	    ->group(g);
	app.add_option("--trace", "increase verbosity of some component even more")
	    ->multi_option_policy(CLI::MultiOptionPolicy::TakeAll)
	    ->each(
	        [](std::string s) { Logger::set_level(s, Logger::Level::trace); })
	    ->group(g);

	app.callback([opt]() { run_solve_command(*opt); });
}