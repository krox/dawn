#pragma once

#include "sat/assignment.h"
#include "sat/clause.h"
#include <ranges>
#include <span>
#include <vector>

namespace dawn {

// Maps a solution to the 'current', possibly transformed, CNF formula to a
// solution of the original problem.
//   * A basic solver solver would not need this, but it is required due to some
//     inprocessing steps, such as BCE and renumbering.
//   * note there is no 'add_var' method. Auxiliary Variables can be added just
//     by using them (in '.add_rule' or the like). The 'original' variable count
//     however is fixed at construction time and can not change.
class Reconstruction
{
	int outer_var_count_;
	int orig_var_count_;

	// inner variable -> outer literal
	// mapping must be injective, not necessarily surjective
	std::vector<Lit> to_outer_;

	// maps 'inner' to 'outer' using the to_outer_ mapping and lazily appending
	// to it.
	Lit to_outer(Lit a);

	// * rules are interpreted as "if not satisfied, flip leading variable"
	//   (could generalize to linear/xor rules, or other gates in the future)
	// * note: rules are not clauses, they may not be all satisfied by the
	//   eventual solution.
	// * rules need to be applied in reverse order of creation
	ClauseStorage rules_;

  public:
	explicit Reconstruction(int n) noexcept;

	// original variable count. can not change.
	int orig_var_count() const noexcept { return orig_var_count_; }

	// "plug in an ansatz", where 'trans' is mapping from old vars to new vars.
	// Does allow fixed and equivalent variables.
	void renumber(std::span<const Lit> trans, int newVarCount);

	// add a transformation rule, which will be applied (in reverse order)
	// by '.extend()' in the future
	void add_rule(std::span<const Lit> cl);

	// convenience function. sane as 'add_rule(cl)', but moves one of the lits
	// to the front.
	void add_rule(std::span<const Lit> cl, Lit pivot);

	// convenience wrappers for 'add_rule'
	void add_unit(Lit a);
	void add_equivalence(Lit a, Lit b);

	// number of rules recorded so far.
	size_t rule_count() const { return rules_.count(); }

	// map inner solution to outer solution
	Assignment operator()(Assignment const &) const;

	// bytes allocated on the heap (rules and renumbering arrays)
	size_t memory_usage() const;
};

} // namespace dawn
