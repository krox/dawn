#ifndef SAT_STATS_H
#define SAT_STATS_H

#include "util/stopwatch.h"

struct Stats
{
	// time of different parts of the solver
	util::Stopwatch swTotal, swParsing;
	util::Stopwatch swSCC, swCleanup, swProbing;
	util::Stopwatch swSearch, swSearchInit;

	// Write stats to stdout. Usually called once at the end of solving
	void dump();
};

#endif
