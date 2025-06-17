#pragma once

#include "sat/cnf.h"

namespace dawn {
int makeDisjunctions(Cnf &);
void substituteDisjunctions(Cnf &);
} // namespace dawn
