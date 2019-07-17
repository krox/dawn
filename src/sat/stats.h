#ifndef SAT_STATS_H
#define SAT_STATS_H

#include "util/stats.h"
#include "util/stopwatch.h"

struct Stats
{
	bool watchStats = false; // print histogram of watchlist size

	// histogram of the visited(!) binary-lists and watchlists
	util::IntHistogram binHistogram;
	util::IntHistogram watchHistogram;

	Stats() : binHistogram(0, 21), watchHistogram(0, 21) {}

	// statistics on the search process
	int64_t nLearnt = 0;
	int64_t nBinProps = 0, nBinConfls = 0;
	int64_t nLongProps = 0, nLongConfls = 0;

	// time of different parts of the solver
	util::Stopwatch swTotal, swParsing;
	util::Stopwatch swSCC, swCleanup, swProbing;
	util::Stopwatch swSearch, swSearchInit;

	// Write stats to stdout. Usually called once at the end of solving
	void dump();
};

#endif
