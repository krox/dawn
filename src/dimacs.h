#ifndef DIMACS_H
#define DIMACS_H

#include <string>
#include "sat.h"
#include "solution.h"

/** filename = "" means reading from stdin */
void parseCnf(std::string filename, Sat& sat);
void parseSolution(std::string filename, Solution& sol);

#endif
