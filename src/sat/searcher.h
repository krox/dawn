#pragma once

#include "sat/activity_heap.h"
#include "sat/propengine.h"
#include "util/functional.h"
#include <stop_token>

namespace dawn {

// Core of a CDCL solver. This wraps a PropEngine together with some auxiliary
// state (variable activity, polarity).
//   * 'Searcher' owns all its data (clauses, activity heap, ...), so multiple
//     instances can be created and run concurrently. Resulting learnt clauses
//     are communicated back to the caller via a callback.
// TODO: some support to run this concurrently in a separate thread.
//       (depends on copying the CNF formula into the PropEngine or similar)
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

  private:
	// number of restarts so far
	int64_t iter_ = 0;

	// temporary buffer for learnt clauses
	std::vector<Lit> buf_;

	PropEngine p_;
	ActivityHeap act_;
	util::bit_vector polarity_;

	// analyze + otf-shorten + backtrack + propagate + callback
	void handle_conflict();

	Color on_learnt(std::span<const Lit> lits);

	// Choose unassigned variable (and polarity) to branch on.
	// Returns Lit::undef() if everything is assigned.
	Lit choose_branch();

	// run one 'restart', i.e. starting and ending at decision level 0
	//   * number of conflicts in this restart is determined by config
	void run_restart(std::stop_token stoken);

	Config config_;

  public:
	// Not moveable
	// (internal note: the PropEngine contains a reference to the activity heap)
	Searcher(Searcher const &) = delete;
	Searcher &operator=(Searcher const &) = delete;

	PropStats const &stats() const { return p_.stats; }

	// This copies all clauses into the Searcher, so that it can be used
	// indepndent of the original CNF formula.
	explicit Searcher(Cnf const &cnf, Config const &config)
	    : p_(cnf), act_(cnf.var_count()), polarity_(cnf.var_count()),
	      config_(config)
	{}

	int64_t ngreen = 0, nred = 0;
	ClauseStorage learnts_;
	std::optional<Assignment> solution_;

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
	void run_epoch(int64_t max_confls, std::stop_token stoken);

	// returns result since get_result was called last
	std::variant<Assignment, ClauseStorage> get_result() const
	{
		if (solution_)
			return *std::move(solution_);
		else
			return std::move(learnts_);
	}
};
} // namespace dawn