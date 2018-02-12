#ifndef DIMACS_H
#define DIMACS_H

#include <string>
#include "clause.h"

void parseDimacs(std::string filename, ClauseStorage& clauses);

#endif
