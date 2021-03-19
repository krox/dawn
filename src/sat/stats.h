#pragma once

#include "util/random.h"
#include "util/stats.h"
#include "util/stopwatch.h"
#include <atomic>

namespace dawn {

/** set by 'SIGINT' interrupt handler to indicate solving should stop ASAP */
inline std::atomic_bool interrupt = false;

enum class RestartType
{
	constant,
	linear,
	geometric,
	luby
};

struct SolverConfig
{
	// main searcher (CDLC)
	int otf = 2;                  // on-the-fly strengthening of learnt clauses
	                              // (0=off, 1=basic, 2=recursive)
	bool lhbr = true;             // lazy hyper-binary resolution
	bool full_resolution = false; // learn by full resolution instead of UIP
	int branch_dom = 0; // branch on dominator instead of chosen one itself
	                    // ( 0=off, 1=matching polarity only, 2=always

	// clause cleaning
	bool use_glue = true; // use glue for clause cleaning (otherwise size)
	int max_learnt_size = 100;
	int max_learnt_glue = 100;
	int64_t max_learnt = INT64_MAX;

	// restarts
	RestartType restart_type = RestartType::luby;
	int restart_base = 100;
	int restart_mult = 1.1; // only for geometric

	// pre-/inprocessing
	int inprocessIters = 1; // maximum number of iterations of inprocessing
	int subsume = 2;        // subsumption and self-subsuming resolution
	                        // (0=off, 1=binary, 2=full)
	int probing = 1;        // failed literal probing
	                        // (0=off, 1=limited, 2=full)
	int tbr = 2;            // transitive binary reduction
	                        // (0=off, 2=full)
	int vivify = 1;         // clause vivification
	int bve = 1;            // bounded variable elimination
	int bva = 0;            // bounded variable addition

	// other
	int64_t max_confls = INT64_MAX; // stop solving
};

struct Stats
{
	// histogram of the visited(!) binary-lists and watchlists
	util::IntHistogram binHistogram;        // length of binary-list
	util::IntHistogram watchHistogram;      // length of watch-list
	util::IntHistogram clauseSizeHistogram; // length of visited long clauses

	Stats()
	    : binHistogram(0, 21), watchHistogram(0, 21), clauseSizeHistogram(0, 21)
	{}

	bool watch_stats = false; // print histogram of watchlist size

	// statistics on the search process
	int64_t nLearnt = 0;
	int64_t nBinSatisfied = 0, nBinProps = 0, nBinConfls = 0;
	int64_t nLongSatisfied = 0, nLongShifts = 0, nLongProps = 0,
	        nLongConfls = 0;
	int64_t nLitsLearnt = 0, nLitsOtfRemoved = 0;
	int64_t nLhbr = 0;

	int64_t nProps() const { return nBinProps + nLongProps; }
	int64_t nConfls() const { return nBinConfls + nLongConfls; }

	// time of different parts of the solver
	util::Stopwatch swTotal, swParsing;
	util::Stopwatch swSCC, swCleanup, swProbing;
	util::Stopwatch swSearch, swSearchInit;
	util::Stopwatch swSubsumeBin, swSubsumeLong;
	util::Stopwatch swVivification, swBVE, swBVA;

	// Write stats to stdout. Usually called once at the end of solving
	void dump();
};

} // namespace dawn
