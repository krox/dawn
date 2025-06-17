#include "catch2/catch_test_macros.hpp"

#include "sat/cnf.h"
#include "sat/elimination.h"

#include "fmt/format.h"
#include "fmt/ostream.h"

using namespace dawn;

TEST_CASE("parser and clause normalization") {
  Cnf sat(5);
  sat.add_clause_safe("1 -1");
  sat.add_clause_safe("1 2 3");
  sat.add_clause_safe("1 1 1 2 3");
  sat.add_clause_safe("3 3");

  CHECK(fmt::format("{}", sat) ==
        R"(p cnf 5 3
3 0
1 2 3 0
1 2 3 0
)");
}

TEST_CASE("bounded variable elimination", "[BVE]") {
  Cnf sat(5);
  sat.add_clause_safe("1 2 3");
  sat.add_clause_safe("1 2 -3");
  sat.add_clause_safe("1 2");
  sat.add_clause_safe("-1 -2");
  run_elimination(sat, {});
  // fmt::print("{}", sat);
}
