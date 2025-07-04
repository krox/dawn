#include "CLI/CLI.hpp"
#include "sat/cnf.h"
#include "sat/dimacs.h"
#include "sat/solver.h"
#include "sat/stats.h"
#include <csignal>
#include <stop_token>
#include <string>

using namespace dawn;

namespace {
std::stop_source global_ssource;
extern "C" void interruptHandler(int)
{
	global_ssource.request_stop();
	signal(SIGINT, SIG_DFL); // remove the handler so that a second SIGINT will
	                         // abort the program
}
} // namespace

namespace {
struct Options
{
	std::string cnfFile, solFile;
	std::string binary_solution_file;
	bool shuffle = false;
	int64_t seed = 0;
	int timeout = 0;
	bool watch_stats = false;
	SolverConfig config;
};

void run_solve_command(Options opt)
{
	util::Logger::set_sink(
	    [](std::string_view msg) { fmt::print("c {}\n", msg); });
	// read CNF from file or stdin
	auto [originalClauses, varCount] = parseCnf(opt.cnfFile);
	auto sat = Cnf(varCount, originalClauses); // clauses are copied here!
	if (opt.seed == -1)
		opt.seed = std::random_device()();
	auto rng = util::xoshiro256(opt.seed);
	if (opt.shuffle)
		shuffle_variables(sat, rng);

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
		result = solve(sat, sol, opt.config, global_ssource.get_token());

		// print to stdout
		if (result == 10)
		{
			fmt::print("s SATISFIABLE\n");
			assert(sol.var_count() == varCount);
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

		// print to binary file
		if (opt.binary_solution_file != "")
		{
			// write
			auto buf = util::bit_vector(sol.var_count());
			for (int i = 0; i < sol.var_count(); ++i)
				buf[i] = sol.satisfied(Lit(i, false));

			// write buf to file

			std::ofstream f(opt.binary_solution_file, std::ios::binary);
			if (!f)
				throw std::runtime_error(
				    "Could not open binary solution file: " +
				    opt.binary_solution_file);

			f.write((const char *)buf.data(), (buf.size() + 7) / 8);
			f.close();
		}

		break;
	}

	// statistics
	util::Logger::print_summary();
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
	app.add_option("--binary-solution", opt->binary_solution_file,
	               "output solution as plain binary file")
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
	app.add_option("--max-learnt", opt->config.max_learnt)->group(g);

	// restarts
	g = "Restarts";
	app.add_option("--restart-type", opt->config.restart_type,
	               "constant, linear, geometric, luby")
	    ->transform(CLI::CheckedTransformer(std::map<std::string, RestartType>{
	        {"constant", RestartType::constant},
	        {"linear", RestartType::linear},
	        {"geometric", RestartType::geometric},
	        {"luby", RestartType::luby}}))
	    ->group(g);
	app.add_option("--restart-base", opt->config.restart_base,
	               "base multiplier (default=100)")
	    ->group(g);
	app.add_option("--restart-mult", opt->config.restart_mult,
	               "multiplier for geometric restart (default=1.1)")
	    ->group(g);

	// inprocessing options
	g = "Inprocessing";
	app.add_option("--bin-probing", opt->config.bin_probing,
	               "probe for failed binary (default=0)")
	    ->group(g);
	app.add_option("--subsume", opt->config.subsume,
	               "subsumption and self-subsuming resolution"
	               "(0=off, 1=binary, 2=full=default)")
	    ->group(g);
	app.add_option("--vivify", opt->config.vivify,
	               "clause vivification"
	               "(0=off, 1=normal, 2=also binary strengthen, 3=also learnt)")
	    ->group(g);
	app.add_option("--bve", opt->config.bve, "bounded variable elimination")
	    ->group(g);
	app.add_option("--bva", opt->config.bva, "bounded variable addition")
	    ->group(g);

	// verbosity
	g = "Verbosity";
	app.add_flag("--watch-stats", opt->watch_stats,
	             "print watchlist statistics after solving")
	    ->group(g);
	app.add_flag("--plot", opt->config.plot,
	             "live plotting of learning (requires gnuplot, somewhat "
	             "experimental)")
	    ->group(g);

	// silence these by default (part of 'cleanup', usually very fast)
	util::Logger::set_level("probing", util::Logger::Level::warning);
	util::Logger::set_level("TBR", util::Logger::Level::warning);

	app.callback([opt]() { run_solve_command(*opt); });
}