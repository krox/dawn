#pragma once

#include "sat/cnf.h"
#include "sat/reconstruction.h"
#include "sat/stats.h"
#include "util/bit_vector.h"
#include "util/logging.h"
#include <cassert>
#include <vector>

namespace dawn {

// CNF clauses + extension data + some auxiliary stuff
class Sat : public Cnf
{
  private:
	// mapping to original variables.
	Reconstruction recon_;

  public:
	util::xoshiro256 rng;

	// constructors
	explicit Sat(int n, ClauseStorage clauses_ = {});
	Sat() noexcept : Sat(0) {}

	// would work fine, just never used so we disallow copies to prevent bugs
	Sat(Sat const &) = delete;
	Sat &operator=(Sat const &) = delete;

	// add variables
	int add_var();

	void add_rule(std::span<const Lit> cl) { recon_.add_rule(cl); }

	void add_rule(std::span<const Lit> cl, Lit pivot)
	{
		recon_.add_rule(cl, pivot);
	}

	Assignment reconstruct_solution(Assignment const &a) const
	{
		return recon_(a);
	}

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
    : Cnf(n, std::move(clauses_)), recon_(n)
{}

inline int Sat::add_var()
{
	int i = var_count();
	bins.emplace_back();
	bins.emplace_back();
	return i;
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
