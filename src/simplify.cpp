#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/dimacs.h"
#include "sat/probing.h"
#include "sat/sat.h"
#include "sat/solver.h"

using namespace dawn;

int main(int argc, char *argv[])
{
	// command line arguments
	std::string cnfFile, outFile;
	CLI::App app{"Run some preprocessing on SAT instance."};
	app.add_option("input", cnfFile, "input CNF in dimacs format");
	app.add_option("output", outFile, "output CNF in dimacs format");
	CLI11_PARSE(app, argc, argv);

	auto [clauses, varCount] = parseCnf(cnfFile);
	Sat sat = Sat(varCount, std::move(clauses)); // clauses are copied here!
	cleanup(sat);
	dump(sat);
	return 0;
}
