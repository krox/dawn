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
	fmt::print("c {} vars with {} + {} + {} clauses\n", sat.var_count(),
	           sat.unary_count(), sat.binary_count(), sat.long_count());
}

int main(int argc, char *argv[])
{
	// command line arguments
	std::string cnfFile, outFile;
	int level = 99;
	CLI::App app{"Run some preprocessing on SAT instance."};
	app.add_option("input", cnfFile, "input CNF in dimacs format");
	app.add_option("output", outFile, "output CNF in dimacs format");
	app.add_option("-n", level, "normal form to apply (0-3)");
	CLI11_PARSE(app, argc, argv);

	auto [clauses, varCount] = parseCnf(cnfFile);
	Sat sat = Sat(varCount, std::move(clauses));

	// equivalence normals forms:
	//   level 0: purely syntactical (to satisfy strict parsers)
	//     * check input for variable count and syntax
	//     * remove tautologies and repeated literals
	//   level 1: confluent / equivalence preserving / cheap
	//     * unit propagation
	//     * equivalent literals
	//     * remove pure/unused variables, duplicate/redundant binaries (TBR)
	//     * TODO: subsumption (without SSR) and duplicate longs
	//     * failed literal probing
	//     * TODO: binary probing with proper cutoff
	//     * TODO: full HBR, if that is possible in reasonable runtime
	//   level 2: not strictly confluent but non-decreasing strength
	//     * some LHBR
	//     * subsumption (+ self subsuming resolution, including virtual
	//       binaries). Note that binary<->binary is already implied by SCC+TBR
	//     * UP-based strengthening (called "vivification" here, though
	//       probably a superset of what the literature calls vivification)
	//     * TODO: strengthening of virtual binaries along binaries. Is this
	//             possible in somewhat reasonable runtime?
	//   level 3: only satisfiability is preserved. hope for the best.
	//     * bounded variable elimination/addition
	//     * blocked clause elimination/addition

	while (true)
	{
		printStats(sat);

		if (level >= 1)
		{
			cleanup(sat);
		}

		bool change = false;

		if (level >= 1)
		{
			// LHBR can violate confluency (full HBR would not), so we need to
			// deactivate it on level=1.
			change |= probe(sat, level >= 2, 999999999);
		}

		if (level >= 2)
			change |= run_subsumption(sat);

		if (change)
			continue;

		if (level >= 2)
		{
			// NOTE: redundant binaries can slow down vivification a lot, even
			//       though subsumption does not care much.
			// TODO: this can probably be solved  as a side effect of
			//       optimizing the "strengthen along binaries" part of vivify
			runBinaryReduction(sat);
			change |= run_vivification(sat);
		}

		if (change)
			continue;

		if (level == 2)
		{
			EliminationConfig elimConfig = {};
			elimConfig.level = 0; // only removes pure/unused
			change |= run_elimination(sat, elimConfig);
		}
		else if (level >= 3)
		{
			EliminationConfig elimConfig = {};
			elimConfig.level = 5; // full classic BVE
			change |= run_elimination(sat, elimConfig);
			change |= run_blocked_clause_elimination(sat);
			change |= run_blocked_clause_addition(sat);
		}

		if (change)
			continue;

		if (false) // brute-force resolution
		{
			EliminationConfig elimConfig = {};
			elimConfig.level = 10;
			elimConfig.max_eliminations = 50;
			change |= run_elimination(sat, elimConfig);
		}

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
