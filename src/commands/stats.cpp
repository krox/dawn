#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/cnf.h"
#include "sat/dimacs.h"

using namespace dawn;

namespace {

struct Options
{
	std::string input;
};

void run_stats_command(Options opt)
{
	auto [clauses, varCount] = parseCnf(opt.input);
	auto sat = Cnf(varCount, std::move(clauses)); // clauses are copied here!

	// print statistics about sat
	fmt::print("nvars  = {:>8}\n", sat.var_count());
	fmt::print("units  = {:>8}\n", sat.unary_count());
	fmt::print("binary = {:>8}\n", sat.binary_count());
	fmt::print("long   = {:>8}\n", sat.long_count());
}

} // namespace

void setup_stats_command(CLI::App &app)
{
	auto opt = std::make_shared<Options>();
	app.add_option("input", opt->input, "input file");
	app.callback([opt]() { run_stats_command(*opt); });
}