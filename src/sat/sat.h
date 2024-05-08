#pragma once

#include "sat/cnf.h"
#include "sat/extender.h"
#include "sat/logging.h"
#include "sat/stats.h"
#include "util/bit_vector.h"
#include <cassert>
#include <vector>

namespace dawn {

// CNF clauses + extension data + some auxiliary stuff
class Sat : public Cnf
{
  private:
	std::vector<Lit> to_outer_; // inner variable -> outer literal
  public:
	Stats stats;
	util::xoshiro256 rng;

	// Rules needed to extend solution to original problem.
	// 'outer' variable numbering.
	Extender extender;

	// constructors
	explicit Sat(int n, ClauseStorage clauses_ = {});
	Sat() noexcept : Sat(0) {}

	// would work fine, just never used so we disallow copies to prevent bugs
	Sat(Sat const &) = delete;
	Sat &operator=(Sat const &) = delete;

	// translate inner to outer (can return Lit::zero()/Lit::one() for fixed)
	Lit to_outer(Lit a) const;
	Assignment to_outer(Assignment const &) const;

	// add variables
	int add_var();

	// add/count variables in the 'outer problem
	int add_var_outer();
	int var_count_outer() const;

	/**
	 * - renumber variables allowing for fixed and equivalent vars
	 * - invalidates all CRefs
	 * - suggested to call clauses.compacitfy() afterwards
	 * - if trans[v] is Lit::elim(), the variable v may not appear in any clause
	 */
	void renumber(std::span<const Lit> trans, int newVarCount);

	// sort clauses and literals in clauses. Invalidates all CRefs, just
	// intended for nicer human-readable output
	void sort_clauses();

	size_t memory_usage() const;
};

void shuffleVariables(Sat &sat);

inline Sat::Sat(int n, ClauseStorage clauses_)
    : Cnf(n, std::move(clauses_)), to_outer_(n), extender(n)
{
	for (int i = 0; i < n; ++i)
		to_outer_[i] = Lit(i, false);
}

inline Lit Sat::to_outer(Lit a) const
{
	if (!a.proper())
		return a;
	assert(a.var() < var_count());
	return to_outer_[a.var()] ^ a.sign();
}

inline int Sat::var_count_outer() const { return extender.var_count(); }

inline int Sat::add_var()
{
	int inner = var_count();
	int outer = extender.add_var();
	bins.emplace_back();
	bins.emplace_back();
	to_outer_.push_back(Lit(outer, false));
	return inner;
}

inline int Sat::add_var_outer()
{
	int i = add_var();
	return to_outer_[i].var();
}

// create list of all clauses (active and extension) in outer numbering
ClauseStorage getAllClausesOuter(Sat const &sat);
ClauseStorage getAllClauses(Sat const &sat);

// cheap simplifications that should probably be run before and after any more
// serious searches
//   * runs until fixed point:
//       * unit propagation
//       * equivalent literal substitution
//       * failed literal probing
//       * hyper binary resolution
//       * transitive binary reduction
//       * compactify clause storage
//   * TODO:
//       * pure literal elimination
//       * disconnected components?
void cleanup(Sat &sat);

// check that
//     * no contradiction
//     * no unit clauses
//     * no equivalent variables
bool is_normal_form(Cnf const &);

} // namespace dawn

template <> struct fmt::formatter<dawn::Sat> : public fmt::formatter<dawn::Cnf>
{};
