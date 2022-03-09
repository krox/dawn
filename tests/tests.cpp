#include "catch2/catch_test_macros.hpp"

#include "sat/sat.h"
#include "sat/elimination.h"

#include "fmt/format.h"
#include "fmt/ostream.h"

using namespace dawn;

TEST_CASE("parser and clause normalization")
{
	Sat sat(5);
	sat.addClauseOuter("1 -1");
	sat.addClauseOuter("1 2 3");
	sat.addClauseOuter("1 1 1 2 3");
	sat.addClauseOuter("3 3");

	CHECK(fmt::format("{}", sat) ==
R"(p cnf 5 3
3 0
1 2 3 0
1 2 3 0
)");
}

TEST_CASE("bounded variable elimination", "[BVE]")
{
	Sat sat(5);
	sat.addClauseOuter("1 2 3");
	sat.addClauseOuter("1 2 -3");
	sat.addClauseOuter("1 2");
	sat.addClauseOuter("-1 -2");
	run_variable_elimination(sat);
	fmt::print("{}", sat);
}
