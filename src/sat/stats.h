#ifndef SAT_STATS_H
#define SAT_STATS_H

#include "util/random.h"
#include "util/stats.h"
#include "util/stopwatch.h"
#include <atomic>

struct Stats
{
	std::atomic_bool interrupt = false;

	// pRNG state
	util::xoshiro256 rng;

	// configuration
	int64_t maxConfls = INT64_MAX;
	bool watchStats = false; // print histogram of watchlist size
	int otf = 2;             // on-the-fly strengthening of learnt clauses
	                         // (0=off, 1=basic, 2=recursive)
	int subsume = 2;         // subsumption and self-subsuming resolution
	                         // (0=off, 1=binary, 2=full)
	int probing = 1;         // failed literal probing
	                         // (0=off, 1=limited, 2=full)
	bool lhbr = true;        // lazy hyper-binary resolution
	bool useGlue = true;     // use glue for clause cleaning
	int maxLearntSize = 100; // eagerly remove learnt very large learnt clauses
	int maxLearntGlue = 100;
	int64_t maxLearnt = INT64_MAX;

	// histogram of the visited(!) binary-lists and watchlists
	util::IntHistogram binHistogram;
	util::IntHistogram watchHistogram;

	Stats() : binHistogram(0, 21), watchHistogram(0, 21) {}

	// statistics on the search process
	int64_t nLearnt = 0;
	int64_t nBinProps = 0, nBinConfls = 0;
	int64_t nLongProps = 0, nLongConfls = 0;
	int64_t nLitsLearnt = 0, nLitsOtfRemoved = 0;
	int64_t nLhbr = 0;

	int64_t nProps() const { return nBinProps + nLongProps; }
	int64_t nConfls() const { return nBinConfls + nLongConfls; }

	// time of different parts of the solver
	util::Stopwatch swTotal, swParsing;
	util::Stopwatch swSCC, swCleanup, swProbing;
	util::Stopwatch swSearch, swSearchInit;
	util::Stopwatch swSubsumeBin, swSubsumeLong;

	// Write stats to stdout. Usually called once at the end of solving
	void dump();
};

#endif
