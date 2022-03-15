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
	int level = 99;
	int weakLevel = 99;
	CLI::App app{"Run some preprocessing on SAT instance."};
	app.add_option("input", cnfFile, "input CNF in dimacs format");
	app.add_option("output", outFile, "output CNF in dimacs format");
	app.add_option("-n", level, "equivalence normal form to apply (0-3)");
	app.add_option("-m", weakLevel,
	               "clause-removing normal form to apply (0-2)");
	CLI11_PARSE(app, argc, argv);

	auto [clauses, varCount] = parseCnf(cnfFile);
	Sat sat = Sat(varCount, std::move(clauses));

	// equivalence normals forms:
	//   level 0:
	//     * check input for variable count and syntax
	//     * remove tautologies and repeated literals
	//   level 1:
	//     * unit propagation
	//     * equivalent literals
	//     * transitive binary reduction
	//   level 2:
	//     * subsumption (also removes duplicate clauses)
	//     * self-subsuming resolution
	//     * also subsumes long clauses with (virtual) binaries
	//     * (subsumption withing binaries is already implied by SCC+TBR)
	//   level 3:
	//     * failed literal probing (without LHBR)
	//   level 4:
	//     * to be continued (some vivification)

	// clause removal
	//   level 1:
	//     * pure literals and unused variables
	//   level 2:
	//     * blocked-clause elimination
	//   level 3:
	//     * to be continued (BVE that actually requires some resolvents)

	if (level >= 1)
		while (true)
		{
			cleanup(sat);
			printStats(sat);
			bool change = false;
			if (level >= 2)
			{
				change |= subsumeBinary(sat);
				change |= subsumeLong(sat);
			}

			if (level >= 3)
			{
				change |= probe(sat, false, 999999999);
			}

			if (!change)
			{
				runBinaryReduction(sat);
				break;
			}
		}

	if (weakLevel >= 1)
		while (true)
		{
			printStats(sat);

			bool change = false;

			change |= run_pure_literal_elimination(sat);

			if (weakLevel >= 2)
				change |= run_blocked_clause_elimination(sat);

			if (!change)
				break;
		}

	printStats(sat);
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
