#pragma once

#include "sat.h"
#include "solution.h"
#include <string>

namespace dawn {

/** filename = "" means reading from stdin */
void parseCnf(std::string filename, Sat &sat);
void parseSolution(std::string filename, Solution &sol);

} // namespace dawn
