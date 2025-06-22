#pragma once

#include "sat/cnf.h"
#include "util/bit_vector.h"
#include "util/vector.h"
#include <vector>

namespace dawn {

// TODO: a more unified "do binary stuff" function would be nice, that
//    - finds equivalent variables
//    - finds some failed literals (finding all binary-restriced fails is
//      potentially expensive. But finding some on the fly should be essentially
//      free)
//    - removes duplicate and redundant binaries
//    - sorts binaries w.r.t. some (approximate) top-order

// Topological order of all literals, i.e., an order such that all binary
// implications go 'from left to right'. If there are cycles in the graph
// (indicated by valid=false), no strict topological order exists, but the
// computed order is still some approximation thereof (namely a "post-order in
// the reversed graph), which might still be useful heuristically.
struct TopOrder
{
	std::vector<Lit> lits;  // literals in order
	std::vector<int> order; // position of each lit
	bool valid;             // false if there are cycles

	TopOrder(BinaryGraph const &);
};

// Fast, incomplete reachability in the binary implication graph.
// O(n) preprocessing, O(1) query, can produce false negatives.
struct Stamps
{
	std::vector<int> start, end;

	// returns true if an implication a => b is found.
	bool has_path(Lit a, Lit b) const;

	Stamps(BinaryGraph const &);
};

// Find and replace equivalent variables.
//    - Very fast (linear in problem size)
//    - Returns number of equivalences found (sat is unchanged if zero)
int run_scc(Cnf &);

// remove redundant binary clauses
void run_binary_reduction(Cnf &);

// print some stats about the binary implication graph
void print_binary_stats(BinaryGraph const &g);

inline bool Stamps::has_path(Lit a, Lit b) const
{
	// the full implication graph is symmetric, so we can use the one forest
	// in both direction, increasing effectivity
	if (start[a] <= start[b] && start[b] <= end[a])
		return true;
	if (start[b.neg()] <= start[a.neg()] && start[a.neg()] <= end[b.neg()])
		return true;
	return false;
}

} // namespace dawn
