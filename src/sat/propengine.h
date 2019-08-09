#ifndef SAT_PROPENGINE_H
#define SAT_PROPENGINE_H

#include "sat.h"
#include "sat/activity_heap.h"
#include "util/bitset.h"
#include <cassert>
#include <vector>

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

  private:
	util::bitset seen;         // temporary during conflict analysis
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
	std::vector<bool> assign;
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

	int level() const;                  /** current level */
	void unroll(int l);                 /** unroll */
	void unroll(int l, ActivityHeap &); /** unroll and re-add vars to heap */

	/**
	 *  - analyze conflict up to UIP
	 *  - bumps activity of all involved variables
	 *  - performs otf minimization if enabled in config
	 */
	int analyzeConflict(std::vector<Lit> &learnt, ActivityHeap &activityHeap);

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
		return t.subspan(0, mark_[0]);
	else if (l == level())
		return t.subspan(mark_[l - 1], t.size());
	else
		return t.subspan(mark_[l - 1], mark_[l]);
}

#endif
