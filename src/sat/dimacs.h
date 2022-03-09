#pragma once

#include "assignment.h"
#include "clause.h"
#include <string>

namespace dawn {

/** filename = "" means reading from stdin */
std::pair<ClauseStorage, int> parseCnf(std::string filename);
void parseAssignment(std::string filename, Assignment &sol);

} // namespace dawn
