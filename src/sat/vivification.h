#pragma once

#include "sat/sat.h"

namespace dawn {

struct VivifyConfig
{
	bool irred_only = true;
	bool with_binary = true;
	int verbosity = 0;
};

bool run_vivification(Sat &sat, VivifyConfig const &config = {});

} // namespace dawn
