#pragma once

#include "sat/cnf.h"

namespace dawn {

// perform subsumption and self-subsuming resolution
//     - considers long/long and (virtual-)binary/long, but not binary/binary,
//       which is taken care of by transitive binary reduction elsewhere
//     - returns true if anything was found
bool run_subsumption(Cnf &cnf);

// Try to subsume b using a. This can either:
//    - do nothing (return false)
//    - shorten b (return true)
//    - remove b (return true, b.color = black)
// In the last case, color of a might change as well.
// NOTE: this method assumes that the lits in both clauses are sorted. If they
//       are not, it just produces some false-negatives. This means some
//       possible subsumptions will stay undetected, but nothing will break.
bool try_subsume(Clause &a, Clause &b);

} // namespace dawn
