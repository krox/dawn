#pragma once

#include "sat/sat.h"

namespace dawn {

/**
 * Do one sweep of failed literal probing
 *   - only tries at roots of implication graph
 *   - does UIP analysis in case something is found
 *   - does not use or modify polarity/activity of variables
 */
int probe(Sat &sat, bool lhbr, int maxTries);

/**
 * Probe for binaries. Quite expensive and probably not woth it for most
 * problems.
 */
int probeBinary(Sat &sat);

// One full sweep of in-tree probing. Possibly faster than probing all roots and
// includes full hyper-binary resolution.
bool intree_probing(Sat &, int maxTries = 0);

} // namespace dawn
