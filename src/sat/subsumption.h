#ifndef SAT_SUBSUMPTION_H
#define SAT_SUBSUMPTION_H

#include "sat/sat.h"

/**
 * Perform subsumption and self-subsuming resolution.
 * Returns true if anything was found.
 */
bool subsumeBinary(Sat &sat); // binary -> long
bool subsumeLong(Sat &sat);   // long -> long

#endif
