#pragma once

#include "sat/activity_heap.h"
#include "sat/propengine.h"
#include "util/functional.h"
#include <stop_token>

namespace dawn {

// Core of a CDCL solver. This wraps a PropEngine together with some auxiliary
// state (variable activity, polarity).
//   * 'Searcher' owns all its data (clauses, activity heap, ...), so multiple
//     instances can be created and run concurrently.
// TODO: some support to run this concurrently in a separate thread.
class Searcher
{
  public:
	struct Config
	{
		// conflict analysis
		int otf = 2; // on-the-fly strengthening of learnt clauses
		             // (0=off, 1=basic, 2=recursive)

		// branching heuristic
		int branch_dom = 0; // branch on dominator instead of chosen literal
		                    // (0=off, 1=only matching polarity, 2=always)

		// restarts
		RestartType restart_type = RestartType::luby;
		int restart_base = 100;
		float restart_mult = 1.1; // only for geometric

		// mic
		int green_cutoff = 8; // max size of clause to be considered good
	};

	struct Result
	{
		ClauseStorage learnts;
		std::optional<Assignment> solution;
		PropStats stats;
	};

  private:
	// number of restarts so far
	int64_t iter_ = 0;

	// temporary buffer for learnt clauses
	std::vector<Lit> buf_;

	PropEngine p_;
	ActivityHeap act_;
	util::bit_vector polarity_;

	// Choose unassigned variable (and polarity) to branch on.
	// Returns Lit::undef() if everything is assigned.
	Lit choose_branch();

	// run one 'restart', i.e. starting and ending at decision level 0
	//   * number of conflicts in this restart is determined by config
	void run_restart(Result &result, std::stop_token stoken);

	Config config_;

  public:
	// Not moveable
	// (internal note: the PropEngine contains a reference to the activity heap)
	Searcher(Searcher const &) = delete;
	Searcher &operator=(Searcher const &) = delete;

	// This copies all clauses into the Searcher, so that it can be used
	// indepndent of the original CNF formula.
	explicit Searcher(Cnf const &cnf, Config const &config)
	    : p_(cnf), act_(cnf.var_count()), polarity_(cnf.var_count()),
	      config_(config)
	{}

	// Keeps running restarts until a satisfying assignment or a contradiction
	// is found, or some limit is reached.
	//   * Returned ClauseStorage contains all 'good' learnt clauses of this
	//     epoch (as determined by .config.green_cutoff). Clause-cleaning
	//     policies inside the Searcher are in principle independent of what the
	//     caller considers a 'good' clause. (Typically, the searcher will
	//     retain more clauses internally, at least for a while.)
	//   * If a contradiction is found, a ClauseStorage containing an empty
	//     clause will be returned.
	//   * 'max_confls' can be exceeded by a small margin, as the search will
	//     stop at the next restart.
	//   * This function is not thread-safe. Use multiple instances of
	//     'Searcher' in order to parallelize.
	Result run_epoch(int64_t max_confls, std::stop_token stoken);
};
} // namespace dawn