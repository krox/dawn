#pragma once

#include "sat/cnf.h"

namespace dawn {

// One full sweep of in-tree probing.
//   * Should be faster than the traditional "probing all roots"
//   * includes full hyper-binary resolution
//   * returns true if any progress was made
bool intree_probing(Cnf &);

// Probe for binaries.
// Quite expensive and probably not woth it for most problems.
int probeBinary(Cnf &cnf);

} // namespace dawn
