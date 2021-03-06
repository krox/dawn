#pragma once

#include "sat/sat.h"
#include "util/bit_vector.h"
#include <vector>

namespace dawn {

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
	    : sat_(sat), visited_(2 * sat.varCount()),
	      visitedTemp_(2 * sat.varCount())
	{
		lits_.reserve(2 * sat.varCount());
		order_.resize(2 * sat.varCount());

		for (int i = 0; i < 2 * sat.varCount(); ++i)
			dfs(Lit(i));
		assert((int)lits_.size() == 2 * sat.varCount());
		// TODO: release memory of visited[Temp] arrays (which is negligible)
	}

	std::vector<Lit> const &lits() const { return lits_; }
	std::vector<int> const &order() const { return order_; }
	int order(Lit a) const { return order_[a]; }
	bool valid() const { return valid_; }
};

} // namespace dawn
