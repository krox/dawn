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

  public:
	using watches_t = std::vector<util::small_vector<CRef, 6>>;
	watches_t watches;
	std::vector<Lit> trail;
	std::vector<int> mark;      // indices into trail
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

	/**
	 * Add clause to underlying ClauseSet without propagating.
	 * Watches are set on cl[0] and cl[1] (if cl.size() >= 3)
	 * returns reason with which cl[0] might be propagated
	 */
	Reason addClause(Lit c0, Lit c1);
	Reason addClause(const std::vector<Lit> &cl, bool irred);

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

	/** for debugging */
	void printTrail() const;
};

#endif
