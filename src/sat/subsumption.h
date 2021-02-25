#pragma once

#include "sat/sat.h"

namespace dawn {

/**
 * Perform subsumption and self-subsuming resolution.
 * Returns true if anything was found.
 */
bool subsumeBinary(Sat &sat); // binary -> long
bool subsumeLong(Sat &sat);   // long -> long

} // namespace dawn
