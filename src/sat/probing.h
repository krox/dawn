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

#endif
