#pragma once

#include "sat/sat.h"

namespace dawn {
int makeDisjunctions(Sat &sat);
void substituteDisjunctions(Sat &sat);
} // namespace dawn
