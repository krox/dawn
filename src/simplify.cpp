#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/binary.h"
#include "sat/dimacs.h"
#include "sat/elimination.h"
#include "sat/probing.h"
#include "sat/sat.h"
#include "sat/solver.h"
#include "sat/subsumption.h"
#include "sat/vivification.h"

using namespace dawn;

void printStats(Sat const &sat)
{
	fmt::print("c {} vars with {} + {} + {} clauses\n", sat.varCount(),
	           sat.unaryCount(), sat.binaryCount(), sat.longCount());
}

int main(int argc, char *argv[])
{
	// command line arguments
	std::string cnfFile, outFile;
	CLI::App app{"Run some preprocessing on SAT instance."};
	app.add_option("input", cnfFile, "input CNF in dimacs format");
	app.add_option("output", outFile, "output CNF in dimacs format");
	CLI11_PARSE(app, argc, argv);

	auto [clauses, varCount] = parseCnf(cnfFile);
	Sat sat = Sat(varCount, std::move(clauses));

	while (true)
	{
		printStats(sat);

		runBinaryReduction(sat);
		if (cleanup(sat))
			continue;
		if (probe(sat, 999999999))
			continue;
		if (subsumeBinary(sat))
			continue;
		if (subsumeLong(sat))
			continue;
		if (runVivification(sat, true))
			continue;
		if (probeBinary(sat))
			continue;
		if (run_blocked_clause_elimination(sat))
			continue;

		break;
	}

	if (outFile == "")
		fmt::print("{}", sat);
	else
	{
		fmt::print("c writing cnf to {}\n", outFile);
		auto file = fmt::output_file(outFile);
		file.print("{}", sat);
	}
	return 0;
}
