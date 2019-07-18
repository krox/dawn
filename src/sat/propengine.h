#ifndef SAT_PROPENGINE_H
#define SAT_PROPENGINE_H

#include "sat.h"
#include "sat/activity_heap.h"
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
	using watches_t = std::vector<util::small_vector<CRef, 6>>;
	watches_t watches;
	std::vector<Lit> trail;
	std::vector<int> mark;      // indices into trail
	std::vector<Reason> reason; // only valid for assigned vars
	std::vector<int> trailPos;  // ditto

	std::vector<Lit> conflictClause;

	ActivityHeap activityHeap;

	void set(Lit x, Reason r);             // no unit propagation
	void propagateBinary(Lit x, Reason r); // binary unit propagation

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
	Reason addClause(const std::vector<Lit> &cl, bool irred);

	/** propagate x and unrolls immediately. Returns number of propagations or
	 * -1 on conflict */
	int probe(Lit x);

	/**
	 * Probe all unassigned literals and propagate inverse of all failings.
	 * Reuturns most active variable or -2 on conflict or -1 if everything is
	 * set already.
	 */
	int probeFull();

	int unassignedVariable() const; /** -1 if everything is assigned */
	int mostActiveVariable();       /** -1 if everything is assigned */

	int level() const; /** current level */
	void unroll(
	    int l); /** unroll all assignments in levels > l, and set level to l */
	int analyzeConflict(std::vector<Lit> &learnt);

	/** for debugging */
	void printTrail() const;
};

#endif
