#pragma once

#include "sat/sat.h"

namespace dawn {

/** returns number of removed variables */
int run_variable_elimination(Sat &sat);

} // namespace dawn
