#pragma once

#include "sat/sat.h"

namespace dawn {

// perform subsumption and self-subsuming resolution
//     - considers long/long and (virtual-)binary/long, but not binary/binary,
//       which is taken care of by transitive binary reduction elsewhere
//     - returns true if anything was found
bool run_subsumption(Sat &sat);

} // namespace dawn
