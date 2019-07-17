#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/dimacs.h"
#include "sat/sat.h"
#include "sat/solver.h"
#include <iostream>

int main(int argc, char *argv[])
{
	// command line arguments
	std::string cnfFile, solFile;
	CLI::App app{"sat solver"};
	app.add_option("input", cnfFile, "input CNF in dimacs format");
	app.add_option("output", solFile, "output solution in dimacs format");
	CLI11_PARSE(app, argc, argv);

	// read CNF from file or stdin
	Sat sat;
	parseCnf(cnfFile, sat);

	// solve
	Solution sol;
	bool result = solve(sat, sol);

	// print to stdout
	if (result)
	{
		std::cout << "s SATISFIABLE" << std::endl;
		if (solFile == "")
			std::cout << sol << std::endl;
	}
	else
		std::cout << "s UNSATISFIABLE" << std::endl;

	// print to file
	if (solFile != "")
	{
		std::ofstream f(solFile, std::ofstream::out);
		if (result)
		{
			f << "s SATISFIABLE" << std::endl;
			f << sol << std::endl;
		}
		else
			f << "s UNSATISFIABLE" << std::endl;
	}

	// statistics
	sat.stats.dump();
}
