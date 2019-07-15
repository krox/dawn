#ifndef SAT_SCC_H
#define SAT_SCC_H

#include "sat/sat.h"

/**
 * explicit solving of the two-sat sub-problem. I.e. looking for equivalent
 * variables. very fast (linear in problem size), implemented using tarjan's
 * algorithm for stongly connected components. returns true if something was
 * found, false if not (sat is unchanged in that case)
 */
bool runSCC(Sat &sat);

#endif
