#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/cnf.h"
#include "sat/dimacs.h"
#include "sat/elimination.h"
#include "sat/subsumption.h"
#include "sat/vivification.h"

using namespace dawn;

namespace {

struct Options
{
	std::string input;
};

void run_simplify_command(Options opt)
{
	auto [clauses, varCount] = parseCnf(opt.input);
	auto sat = Cnf(varCount, std::move(clauses));

	print_stats(sat);

	cleanup(sat);
	run_subsumption(sat);
	cleanup(sat);
	run_vivification(sat, {.with_binary = true, .with_ternary = true}, {});
	cleanup(sat);
	run_subsumption(sat);
	cleanup(sat);

	for (int g : {0, 8, 16})
	{
		run_elimination(sat, {.growth = g, .discard_blocked = true});
		cleanup(sat);
		run_subsumption(sat);
		cleanup(sat);
		run_vivification(sat, {.with_binary = true, .with_ternary = true}, {});
		cleanup(sat);
		run_subsumption(sat);
		cleanup(sat);
	}
	print_stats(sat);
}

} // namespace

void setup_simplify_command(CLI::App &app)
{
	auto opt = std::make_shared<Options>();
	app.add_option("input", opt->input, "input file");
	app.callback([opt]() { run_simplify_command(*opt); });
}