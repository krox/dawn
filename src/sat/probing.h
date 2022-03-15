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
 * problems. The naive version is especially slow and just for debugging.
 */
int probeBinaryNaive(Sat &sat);
int probeBinary(Sat &sat);

} // namespace dawn
