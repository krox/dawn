#pragma once

#include "sat/assignment.h"
#include "sat/clause.h"
#include <vector>

namespace dawn {

class Extender
{
	// clauses are interpreted as "if not satisfied, flip leading variable"
	//     * rules need to be applied in backwards order
	//     * these are not clauses in the sense that they are satisfied by a
	//       solution (indeed, contradictory clauses can happen). These are
	//       only "rules".
	//     * might generalize to other rules (like xor or cardinality) in the
	//       future as well. For now, 'ClauseStorage' is a reasonable
	//       datastructure, though semantically misleading
	ClauseStorage clauses_;
	int var_count_;

  public:
	explicit Extender(int n) noexcept : var_count_(n) {}

	int var_count() const { return var_count_; }
	int add_var() { return var_count_++; }

	// add a transformation rule, which will be applied (in reverse order)
	// by '.extend()' in the future
	void add_rule(std::span<const Lit> cl);

	size_t clause_count() const { return clauses_.count(); }

	// convenience functions to add one or more rules, effectively "defining"
	// a variable in terms of others
	void set_literal(Lit a);
	void set_equivalence(Lit a, Lit b);

	// apply fixup rules in reverse order of their creation
	void extend(Assignment &a) const;

	size_t memory_usage() const;
};

inline void Extender::add_rule(std::span<const Lit> cl)
{
	assert(cl.size() >= 1);
	for (auto a : cl)
		assert(a.proper());
	clauses_.add_clause(cl, true);

	// TODO: if cl is a unit clause, we could use it to simplify previous rules.
	//       (not necessarily remove it from all previous rules). Probably not
	//       performance relevant, but could be nice for human-readable
	//       output of a problem that has not been fully solved
}

inline void Extender::set_literal(Lit a) { add_rule({{a}}); }

inline void Extender::set_equivalence(Lit a, Lit b)
{
	assert(a.var() != b.var());
	add_rule({{a, b.neg()}});
	add_rule({{a.neg(), b}});
}

inline void Extender::extend(Assignment &a) const
{
	/*fmt::print("starting extension with:\n");
	for (auto [ci, cl] : clauses_)
	{
	    (void)ci;
	    fmt::print("\t{}\n", cl);
	}*/

	assert(a.complete());
	for (auto &cl : clauses_.all_reverse())
		if (!a.satisfied(cl))
			a.force_set(cl[0]);
}

inline size_t Extender::memory_usage() const { return clauses_.memory_usage(); }

} // namespace dawn
