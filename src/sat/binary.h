#pragma once

#include "sat/sat.h"
#include "util/bit_vector.h"
#include <vector>

namespace dawn {

// TODO: a more unified "do binary stuff" function would be nice, that
//    - finds equivalent variables
//    - finds some failed literals (finding all binary-restriced fails is
//      potentially expensive. But finding some on the fly should be essentially
//      free)
//    - removes duplicate and redundant binaries
//    - sorts binaries w.r.t. some (approximate) top-order

/**
 * explicit solving of the two-sat sub-problem. I.e. looking for equivalent
 * variables. very fast (linear in problem size), implemented using tarjan's
 * algorithm for stongly connected components. returns number of equivalences
 * found (sat is unchanged if zero)
 */
int runSCC(Sat &sat);

/** print some stats about the binary implication graph */
void printBinaryStats(Sat const &sat);

/** remove redundant binary clauses */
void runBinaryReduction(Sat &sat);

/**
 * Computes a 'topological order' of all literals, i.e., an order such that
 * all binary implications go 'from left to right'.
 *
 * If there are cycles:
 *   - '.valid()' will return false
 *   - no strict topological order exists, but the computed order is still some
 *     approximation thereof so it might still be useful heuristically
 *   - you can use 'runSCC()' to remove cycles (may need repetition)
 */
class TopOrder
{
	Sat const &sat_;

	// temporary during construction
	util::bit_vector visited_;
	util::bit_vector visitedTemp_;

	// result of compution
	std::vector<Lit> lits_;  // literals in order
	std::vector<int> order_; // position of each lit
	bool valid_ = true;      // false if there are cycles

	void dfs(Lit a)
	{
		if (visited_[a])
			return;
		if (visitedTemp_[a])
		{
			valid_ = false;
			return;
		}
		visitedTemp_[a] = true;
		for (Lit b : sat_.bins[a])
			dfs(b.neg());
		order_[a] = (int)lits_.size();
		lits_.push_back(a);
		visitedTemp_[a] = false;
		visited_[a] = true;
	}

  public:
	TopOrder(Sat const &sat)
	    : sat_(sat), visited_(2 * sat.var_count()),
	      visitedTemp_(2 * sat.var_count())
	{
		lits_.reserve(2 * sat.var_count());
		order_.resize(2 * sat.var_count());

		// TODO: the topological order is usually not unique, so some
		//       (reproducible) randomization would be suitable, so that
		//       stamping based passes can be more effective when repeated
		//       multiple times

		for (Lit a : sat.all_lits())
			dfs(a);
		assert((int)lits_.size() == 2 * sat.var_count());
		visited_ = util::bit_vector{};
		visitedTemp_ = util::bit_vector{};
	}

	std::vector<Lit> const &lits() const { return lits_; }
	std::vector<int> const &order() const { return order_; }
	int order(Lit a) const { return order_[a]; }
	bool valid() const { return valid_; }
};

// Approximate reachability information using "stamping".
//     - O(n) setup and O(1) queries, thus faster than full closure
class Stamps
{
	int time_ = 0; // temporary during construction
	Sat const &sat_;

	std::vector<int> start_, end_;

	void dfs(Lit a)
	{
		if (start_[a] != -1)
			return;
		start_[a] = time_++;
		for (Lit b : sat_.bins[a.neg()])
			dfs(b);
		end_[a] = time_++;
	}

  public:
	Stamps(Sat &sat)
	    : sat_(sat), start_(sat.var_count() * 2, -1),
	      end_(sat.var_count() * 2, -1)
	{
		// Sort binaries by topological order. Not strictly necessary, but
		// makes it more efficient.
		// TODO: skip this step if known to already have been done
		auto top = TopOrder(sat);
		if (!top.valid())
			throw std::runtime_error(
			    "tried to compute stamps with non-acyclic graph");
		auto comp = [&top](Lit a, Lit b) {
			return top.order(a) < top.order(b);
		};
		for (auto &bs : sat.bins)
			std::sort(bs.begin(), bs.end(), comp);

		// compute stamps (a recursive lambda would look very sleek here^^)
		for (Lit a : top.lits())
			dfs(a);
	}

	bool has_path(Lit a, Lit b) const
	{
		// the full implication graph is symmetric, so we can use the one forest
		// in both direction, increasing effectivity
		if (start_[a] <= start_[b] && start_[b] <= end_[a])
			return true;
		if (start_[b.neg()] <= start_[a.neg()] &&
		    start_[a.neg()] <= end_[b.neg()])
			return true;
		return false;
	}
};

} // namespace dawn
