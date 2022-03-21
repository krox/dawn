#pragma once

#include "sat.h"
#include "sat/activity_heap.h"
#include "util/bit_vector.h"
#include <cassert>
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

/**
 * Unit propagation.
 */
class PropEngine
{
  public:
	Sat &sat;

	// if this is != null,
	//   - variables are activated during .unroll()
	//   - variable-activity is bumped during conflict analysis
	ActivityHeap *activity_heap = nullptr;

	struct Config
	{
		int otf = 2;      // on-the-fly strengthening of learnt clauses
		                  // (0=off, 1=basic, 2=recursive)
		bool lhbr = true; // lazy hyper-binary resolution
		bool full_resolution = false; // learn by full resolution instead of UIP
	} config;

  private:
	util::bit_vector seen;     // temporary during conflict analysis
	bool isRedundant(Lit lit); // helper for OTF strengthening

	std::vector<Lit> trail_; // assigned variables
	std::vector<int> mark_;  // indices into trail

  public:
	using watches_t = std::vector<util::small_vector<CRef, 6>>;
	watches_t watches;

	std::vector<Reason> reason; // only valid for assigned vars
	std::vector<Lit> binDom;    // ditto
	std::vector<int> trailPos;  // ditto

	std::vector<Lit> conflictClause;

	void set(Lit x, Reason r);             // no unit propagation
	void propagateBinary(Lit x, Reason r); // binary unit propagation

	Lit analyzeBin(util::span<const Lit> reason); // helper for LHBR

  public:
	Assignment assign;
	bool conflict = false;

	/** constructor */
	PropEngine(Sat &sat);

	/** assign a literal and do unit propagation */
	void branch(Lit x);                  // starts a new level
	void propagateFull(Lit x, Reason r); // stays on current level

	/** read-only view (into trail_) of assignments */
	util::span<const Lit> trail() const;      // all levels
	util::span<const Lit> trail(int l) const; // level l

	/**
	 * Add clause to underlying ClauseSet without propagating.
	 * Watches are set on cl[0] and cl[1] (if cl.size() >= 3)
	 * returns reason with which cl[0] might be propagated
	 */
	Reason addLearntClause(Lit c0, Lit c1);
	Reason addLearntClause(const std::vector<Lit> &cl, uint8_t glue);

	int unassignedVariable() const; /** -1 if everything is assigned */

	int level() const; /** current level */

	/**
	 * unroll assignments
	 *   - after unrolling, level() == l
	 *   - re-add freed vars to activity-heap (if activity_heap != null)
	 */
	void unroll(int l);

	/**
	 * analyze conflict up to UIP, outputs learnt clause, does NOT unroll
	 *  - bumps activity of all involved variables (if activity_heap != null)
	 *  - performs otf minimization (if enabled in configuration)
	 *  - learnt clause is ordered by level, such that learnt[0] is the UIP
	 *  - returns level of learnt[1] (or 0 if learnt is unit). This is the
	 *    appropriate level to jump back to
	 */
	int analyzeConflict(std::vector<Lit> &learnt);

	/** compute glue, i.e. number of distinct decision levels of clause */
	uint8_t calcGlue(util::span<const Lit> cl) const;

	/** for debugging */
	void printTrail() const;
};

inline util::span<const Lit> PropEngine::trail() const { return trail_; }

inline util::span<const Lit> PropEngine::trail(int l) const
{
	assert(0 <= l && l <= level());
	auto t = trail();
	if (l == 0 && level() == 0)
		return t;
	else if (l == 0)
		return t.slice(0, mark_[0]);
	else if (l == level())
		return t.slice(mark_[l - 1], t.size());
	else
		return t.slice(mark_[l - 1], mark_[l]);
}

/**
 * Unit propagation without any conflict analysis.
 * This can just check if there is a conflict and then backtrack.
 * Also does not keep statistics on propagations.
 */
class PropEngineLight
{
  public:
	Sat &sat;

  private:
	std::vector<Lit> trail_; // assigned variables
	std::vector<int> mark_;  // indices into trail

  public:
	using watches_t = std::vector<util::small_vector<CRef, 6>>;
	watches_t watches;

  public:
	Assignment assign;
	bool conflict = false;

	/** constructor */
	PropEngineLight(Sat &sat);

	// assign literal and perform unit propagation
	//     - returns number of set propagations (including x)
	//     - does nothing and returns 0 if already set
	//     - returns -1 on conflict
	int propagate(Lit x);

	// propagate the negation of multiple literals.
	int propagate_neg(util::span<const Lit> xs);

	// propagate and immediately backtracks. same return as propagate()
	int probe(Lit x);

	int probe_neg(util::span<const Lit> xs);

	void mark();       // create a new level
	void unroll();     // unrolls one level
	int level() const; // current level (starts at 0)

	util::span<const Lit> trail() const;
	util::span<const Lit> trail(int l) const;
};

/** run unit propagation and remove all fixed variables */
int runUnitPropagation(Sat &sat);

} // namespace dawn
