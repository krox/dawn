#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/cnf.h"
#include "sat/dimacs.h"
#include "sat/solver.h"

using namespace dawn;

namespace {

struct Options
{
	std::string cnfFile, solFile;
};

void run_check_command(const Options &opt)
{
	auto [clauses, varCount] = parseCnf(opt.cnfFile);

	auto sol = Assignment(varCount);
	parseAssignment(opt.solFile, sol);

	if (sol.satisfied(clauses))
	{
		fmt::print("c solution checked\n");
		std::exit(0);
	}
	else
	{
		fmt::print("c SOLUTION CHECK FAILED\n");
		std::exit(-1);
	}
}
} // namespace

void setup_check_command(CLI::App &app)
{
	auto opt = std::make_shared<Options>();

	// input/output
	app.add_option("input", opt->cnfFile, "input CNF in dimacs format")
	    ->type_name("<filename>");
	app.add_option("output", opt->solFile, "output solution in dimacs format")
	    ->type_name("<filename>");
	app.callback([opt]() { run_check_command(*opt); });
}
