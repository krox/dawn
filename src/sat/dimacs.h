#ifndef SAT_DIMACS_H
#define SAT_DIMACS_H

#include "sat.h"
#include "solution.h"
#include <string>

/** filename = "" means reading from stdin */
void parseCnf(std::string filename, Sat &sat);
void parseSolution(std::string filename, Solution &sol);

#endif
