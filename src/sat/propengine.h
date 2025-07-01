#pragma once

#include "sat/activity_heap.h"
#include "sat/cnf.h"
#include "util/bit_vector.h"
#include <cassert>
#include <optional>
#include <queue>
#include <vector>

namespace dawn {

struct Reason
{
	// msb=0 -> binary clause
	// msb=1 -> long clause
	uint32_t val_;

  public:
	constexpr Reason() : val_(UINT32_MAX) {}

	explicit constexpr Reason(Lit a) : val_(a) { assert(a.proper()); }

	explicit constexpr Reason(CRef cref) : val_(cref | (1u << 31))
	{
		assert(cref.proper());
	}

	static constexpr Reason undef() { return Reason(); }

	bool isBinary() const
	{
		return val_ != UINT32_MAX && (val_ & (1u << 31)) == 0;
	}

	bool isLong() const
	{
		return val_ != UINT32_MAX && (val_ & (1u << 31)) != 0;
	}

	bool isUndef() const { return val_ == UINT32_MAX; }

	Lit lit() const
	{
		assert(isBinary());
		return Lit(val_ & (UINT32_MAX >> 1));
	}

	CRef cref() const
	{
		assert(isLong());
		return CRef(val_ & (UINT32_MAX >> 1));
	}

	constexpr bool operator==(Reason b) const { return val_ == b.val_; }
};

// This class implements unit propagation and conflict analysis.
// Note that this only provides the algorithmic building blocks (i.e.
// maintaining the watch lists). The actual CDCL algorithm (with heuristics for
// branching, restarts, cleaning, etc.) is implemented in the Searcher class.
// TODO:
//   * blocking literal optimization and implicit ternary clauses
//   * all-level UIP resolution (restricted to conserve LBD)
//   * benchmark stats-tracking. Can be optimized with local counts in registers
//   * merge this (again) with PropEngineLight
class PropEngine
{
	util::bit_set seen; // temporary during conflict analysis

	std::vector<Lit> trail_; // assigned variables
	std::vector<int> mark_;  // indices into trail

	using watches_t = std::vector<util::small_vector<CRef, 7>>;
	watches_t watches;

	std::vector<Reason> reason; // only valid for assigned vars
	std::vector<int> assign_level;

	std::vector<Lit> conflict_clause;

	bool is_redundant(Lit lit, bool recursive); // helper for OTF strengthening
	void propagate_binary(Lit x, Reason r); // set 'x' and propagate bin clauses

  public:
	// NOTE: units are "stored" as level 0 assignments, so no need to have
	// them explicitly here.
	BinaryGraph bins;
	ClauseStorage clauses;

	Assignment assign;

	// NOTE: In some situations, '.conflict' is set without a '.conflict_clause'
	//       being recorded. Namely (1) when calling 'propagate()' on a literal
	//       that is already set false, or (2) for some level-0 conflicts.
	bool conflict = false;

	PropStats stats;

	// constructor copies and attaches all clauses
	explicit PropEngine(Cnf const &cnf);

	// number of variables
	int var_count() const;

	// create a new level. Only allowed if !conflict.
	void mark();

	// current level. Starts at 0, increases with each mark() by 1.
	int level() const;

	// unroll assignments up to some level
	//   - after unrolling, level() == l
	//   - re-add freed vars to activity-heap (if activity_heap != null)
	void unroll(); // unroll one level
	void unroll(int l);
	void unroll(int l, ActivityHeap &activity_heap);

	// read-only view (into trail_) of assignments
	std::span<const Lit> trail() const;      // all levels
	std::span<const Lit> trail(int l) const; // level l

	// assigns 'x' with reason 'r' and performs full unit propagation
	//   - on success, returns the number of newly set literals (including 'x')
	//   - on conflict, returns -1 and sets '.conflict' and '.conflictClause'
	//   - does not start a new level by itself
	//   - prioritizes propagation of binary clauses over long clauses, but
	//     order of long clauses is undefined due to the 2-watch scheme.
	int propagate(Lit x, Reason r = Reason::undef());

	// propagate the negation of multiple literals
	int propagate_neg(std::span<const Lit> xs);

	// propagate the negation of the xs, except for the pivot, for which the
	// positive is propagated.
	int propagate_neg(std::span<const Lit> xs, Lit pivot);

	// branch = mark + propagate
	int branch(Lit x);

	// probe = mark + propagate + unroll
	int probe(Lit x);
	int probe_neg(std::span<const Lit> xs);
	int probe_neg(std::span<const Lit> xs, Lit pivot);

	// analyze conflict up to UIP, outputs learnt clause, does NOT unroll
	//  - bumps activity of all involved variables (if activity_heap != null)
	//  - learnt clause is ordered by level, such that learnt[0] is the UIP
	//  - otf = 0 -> no strengthening, 1 -> basic, 2 -> recursive
	void analyze_conflict(std::vector<Lit> &learnt, ActivityHeap *activity_heap,
	                      int otf);

	// otf strengthening of learnt clause
	//   * only valid to do right after analyze_conflict(...)
	//     (re-uses the 'seen' array internally)
	//   * keeps the order of remaining literals the same
	void shorten_learnt(std::vector<Lit> &learnt, bool recursive);

	// determine backtrack level ( = level of learnt[1])
	int backtrack_level(std::span<const Lit> cl) const;

	// for debugging
	void print_trail() const;

	// TODO: remove/redo these. not a great interface
	// Add clause without propagating.
	// Watches are set on cl[0] and cl[1] (if cl.size() >= 3)
	// returns reason with which cl[0] might be propagated
	Reason add_clause(Lit c0, Lit c1);
	Reason add_clause(const std::vector<Lit> &cl, Color color);
};

inline int PropEngine::var_count() const { return assign.var_count(); }

inline int PropEngine::level() const { return (int)mark_.size(); }

inline void PropEngine::mark()
{
	assert(!conflict);
	mark_.push_back(trail_.size());
}

inline void PropEngine::unroll()
{
	assert(level() > 0);
	unroll(level() - 1);
}

inline void PropEngine::unroll(int l)
{
	assert(l >= 0);
	assert(l < level());

	conflict = false;
	conflict_clause.resize(0);

	while ((int)trail_.size() > mark_[l])
	{
		Lit lit = trail_.back();
		trail_.pop_back();
		assign.unset(lit);
	}
	mark_.resize(l);
}

inline void PropEngine::unroll(int l, ActivityHeap &activity_heap)
{
	assert(l < level());
	for (int i = mark_[l]; i < (int)trail_.size(); ++i)
		activity_heap.push(trail_[i].var());
	unroll(l);
}

inline std::span<const Lit> PropEngine::trail() const { return trail_; }

inline std::span<const Lit> PropEngine::trail(int l) const
{
	assert(0 <= l && l <= level());
	auto t = trail();
	if (l == 0 && level() == 0)
		return t;
	else if (l == 0)
		return t.subspan(0, mark_[0]);
	else if (l == level())
		return t.subspan(mark_[l - 1]);
	else
		return t.subspan(mark_[l - 1], mark_[l] - mark_[l - 1]);
}

/**
 * Unit propagation without any conflict analysis.
 * This can just check if there is a conflict and then backtrack.
 * Also does not keep statistics on propagations.
 */
class PropEngineLight
{
  public:
	Cnf &cnf;

  private:
	std::vector<Lit> trail_; // assigned variables
	std::vector<int> mark_;  // indices into trail

	void propagate_binary(Lit);
	int propagate_impl(Lit, bool hbr);

  public:
	using watches_t = std::vector<util::small_vector<CRef, 7>>;
	watches_t watches;

  public:
	Assignment assign;
	bool conflict = false;

	int64_t nHbr = 0;

	// constructor attaches all clauses
	explicit PropEngineLight(Cnf &cnf, bool attach_clauses = true);

	// NOTE: only clauses with cl[0] and cl[1] unassigned can be
	// attached/detached
	void attach_clause(CRef cref); // add a clause to the watch lists
	void detach_clause(CRef cref); // remove a clause from the watch lists

	// assign literal and perform unit propagation
	//     - returns number of set propagations (including x)
	//     - does nothing and returns 0 if already set
	//     - returns -1 on conflict
	int propagate(Lit x);

	// same as propagate(), but also create binary x->* clauses for any long
	// propagations found. This is only correct to use if everything currently
	// assigned follows from x.
	int propagate_with_hbr(Lit x);

	// propagate the negation of multiple literals.
	int propagate_neg(std::span<const Lit> xs);

	// propagate the negation of the xs, except for the pivot, for which the
	// positive is propagated.
	int propagate_neg(std::span<const Lit> xs, Lit pivot);

	// propagate and immediately backtracks. same return as propagate()
	int probe(Lit x);
	int probe_neg(std::span<const Lit> xs);
	int probe_neg(std::span<const Lit> xs, Lit pivot);

	void mark();       // create a new level
	void unroll();     // unrolls one level
	int level() const; // current level (starts at 0)

	std::span<const Lit> trail() const;
	std::span<const Lit> trail(int l) const;
};

} // namespace dawn
