#pragma once

#include "clause.h"
#include "solution.h"
#include <string>

namespace dawn {

/** filename = "" means reading from stdin */
std::pair<ClauseStorage, int> parseCnf(std::string filename);
void parseSolution(std::string filename, Solution &sol);

} // namespace dawn
