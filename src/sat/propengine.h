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
//   * merge this (again) with PropEngineLight
class PropEngine
{
  public:
	// NOTE: units are "stored" as level 0 assignments, so no need to have
	// them explicitly here.
	BinaryGraph bins;
	ClauseStorage clauses;

  private:
	util::bit_vector seen; // temporary during conflict analysis

	// otf strengthening of learnt clause
	//   * only valid to do right after analyze_conflict(...)
	//     (re-uses the 'seen' array internally)
	//   * keeps the order of remaining literals the same
	void shorten_learnt(std::vector<Lit> &learnt, bool recursive);
	bool is_redundant(Lit lit, bool recursive); // helper for OTF strengthening

	std::vector<Lit> trail_; // assigned variables
	std::vector<int> mark_;  // indices into trail

  public:
	PropStats stats;

	using watches_t = std::vector<util::small_vector<CRef, 7>>;
	watches_t watches;

	std::vector<Reason> reason; // only valid for assigned vars
	std::vector<int> trailPos;  // ditto

	std::vector<Lit> conflictClause;

	void set(Lit x, Reason r);             // no unit propagation
	void propagateBinary(Lit x, Reason r); // binary unit propagation

  public:
	Assignment assign;
	bool conflict = false;

	/** constructor */
	PropEngine(Cnf const &cnf);

	// assign a literal and do unit propagation. Returns view (into .trail_)
	// containing all newly assigned literals, starting with x.
	std::span<const Lit> branch(Lit x);              // starts a new level
	std::span<const Lit> propagate(Lit x, Reason r); // stays on current level

	/** read-only view (into trail_) of assignments */
	std::span<const Lit> trail() const;      // all levels
	std::span<const Lit> trail(int l) const; // level l

	// Add clause without propagating.
	// Watches are set on cl[0] and cl[1] (if cl.size() >= 3)
	// returns reason with which cl[0] might be propagated
	Reason add_clause(Lit c0, Lit c1);
	Reason add_clause(const std::vector<Lit> &cl, Color color);

	int unassignedVariable() const; /** -1 if everything is assigned */

	int level() const; /** current level */
	int var_count() const { return assign.var_count(); }

	/**
	 * unroll assignments
	 *   - after unrolling, level() == l
	 *   - re-add freed vars to activity-heap (if activity_heap != null)
	 */
	void unroll(int l);
	void unroll(int l, ActivityHeap &activity_heap);

	/**
	 * analyze conflict up to UIP, outputs learnt clause, does NOT unroll
	 *  - bumps activity of all involved variables (if activity_heap != null)
	 *  - performs otf minimization (if enabled in configuration)
	 *  - learnt clause is ordered by level, such that learnt[0] is the UIP
	 *  - otf = 0 -> no strengthening, 1 -> basic, 2 -> recursive
	 */
	void analyze_conflict(std::vector<Lit> &learnt, ActivityHeap *activity_heap,
	                      int otf);

	// determine backtrack level ( = level of learnt[1])
	int backtrack_level(std::span<const Lit> cl) const;

	/** for debugging */
	void printTrail() const;
};

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
