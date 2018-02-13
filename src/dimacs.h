#ifndef DIMACS_H
#define DIMACS_H

#include <string>
#include "sat.h"

void parseDimacs(std::string filename, ClauseSet& cs);

#endif
