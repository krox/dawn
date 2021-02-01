#ifndef SAT_PROBING_H
#define SAT_PROBING_H

#include "sat/sat.h"

/**
 * Do one sweep of failed literal probing
 *   - only tries at roots of implication graph
 *   - does UIP analysis in case something is found
 *   - does not use or modify polarity/activity of variables
 */
int probe(Sat &sat, int maxTries);

/**
 * Probe for binaries. Quite expensive and probably not woth it for most
 * problems. The naive version is especially slow and just for debugging.
 */
int probeBinaryNaive(Sat &sat);
int probeBinary(Sat &sat);

#endif
