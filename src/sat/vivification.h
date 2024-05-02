#pragma once

#include "sat/cnf.h"
#include <stop_token>

namespace dawn {

struct VivifyConfig
{
	// additionally to direct shortening, also try to strengthen along binary
	// implicatns
	bool with_binary = true;

	// also strengthen along ternary. This effectively includes replacing
	// definitions
	bool with_ternary = true;
};

// run vivification
//    * config controls which clauses are tried (irred/learnt, size cutoff) and
//      what exactly to try (just basic shortening, or also binary
//      strengthening)
//    * does not remove any clauses, just modifies existing ones. Therefore
//      suggest to run subsumption afterwards to clean up
//    * returns true if any change was made
bool run_vivification(Cnf &cnf, VivifyConfig const &config,
                      std::stop_token stoken);

} // namespace dawn
