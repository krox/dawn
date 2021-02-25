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

	// read CNF from file or stdin
	static Sat sat;
	parseCnf(cnfFile, sat);

	while (true)
	{
		inprocessCheap(sat);

		if (probe(sat, 0))
			continue;

		break;
	}
	dumpOuter(outFile, sat);
	return 0;
}
