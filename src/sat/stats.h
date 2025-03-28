#pragma once

#include "util/random.h"
#include "util/stats.h"
#include "util/stopwatch.h"
#include <atomic>

namespace dawn {

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
	int otf = 2;        // on-the-fly strengthening of learnt clauses
	                    // (0=off, 1=basic, 2=recursive)
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
	float restart_mult = 1.1; // only for geometric

	// pre-/inprocessing
	int inprocessIters = 1; // maximum number of iterations of inprocessing
	int subsume = 2;        // subsumption and self-subsuming resolution
	                        // (0=off, 1=binary, 2=full)
	int bin_probing = 0;    // probe for binary clauses
	int vivify = 2;         // clause vivification
	int bve = 1;            // bounded variable elimination
	int bce = 1;            // blocked clause elimination
	int bva = 0;            // bounded variable addition

	// other
	int64_t max_confls = INT64_MAX; // stop solving
	bool plot = false;
};

struct LearnEvent
{
	int depth;
	int size;
};

struct PropStats
{
	// histogram of the visited(!) binary-lists and watchlists
	util::IntHistogram binHistogram;        // length of binary-list
	util::IntHistogram watchHistogram;      // length of watch-list
	util::IntHistogram clauseSizeHistogram; // length of visited long clauses

	// statistics on the search process
	int64_t nBinSatisfied = 0, nBinProps = 0, nBinConfls = 0;
	int64_t nLongSatisfied = 0, nLongShifts = 0, nLongProps = 0,
	        nLongConfls = 0;
	int64_t nLitsLearnt = 0, nLitsOtfRemoved = 0;

	int64_t nProps() const { return nBinProps + nLongProps; }
	int64_t nConfls() const { return nBinConfls + nLongConfls; }

	// Write stats to stdout. Usually called once at the end of solving
	void dump(bool with_histograms);
	void clear();

	std::vector<LearnEvent> learn_events;
};

PropStats &operator+=(PropStats &a, const PropStats &b);

} // namespace dawn
