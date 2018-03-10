#ifndef PROPENGINE_H
#define PROPENGINE_H

#include <vector>
#include <cassert>
#include "sat.h"

struct Reason
{
	// msb=0 -> binary clause
	// msb=1 -> long clause
	uint32_t _val;

public:
	constexpr Reason()
		: _val(UINT32_MAX)
	{}

	explicit constexpr Reason(Lit a)
		: _val(a)
	{ assert(a.proper()); }

	explicit constexpr Reason(CRef cref)
		: _val(cref | (1u<<31))
	{ assert(cref.proper()); }

	bool isUndef() const
	{
		return _val == UINT32_MAX;
	}

	bool isBinary() const
	{
		return _val != UINT32_MAX && (_val & (1u<<31)) == 0;
	}

	bool isLong() const
	{
		return _val != UINT32_MAX && (_val & (1u<<31)) != 0;
	}

	Lit lit() const
	{
		assert(isBinary());
		return Lit(_val & (UINT32_MAX >> 1));
	}

	CRef cref() const
	{
		assert(isLong());
		return CRef(_val & (UINT32_MAX >> 1));
	}
};

constexpr Reason REASON_UNDEF = Reason();

/**
 * Unit propagation.
 */
class PropEngine
{
	ClauseSet& cs;
	std::vector<std::vector<CRef>> watches;
	std::vector<Lit> trail;
	std::vector<int> mark; // indices into trail
	std::vector<Reason> reason; // only valid for assigned vars
	std::vector<int> trailPos; // ditto

	std::vector<Lit> conflictClause;

	void set(Lit x, Reason r);	// no unit propagation
	void propagateBinary(Lit x, Reason r); // binary unit propagation

public:
	std::vector<bool> assign;
	bool conflict = false;

	/** constructor */
	PropEngine(ClauseSet& cs);

	/** assign a literal and do unit propagation */
	void branch(Lit x); // starts a new level
	void propagateFull(Lit x, Reason r); // stays on current level

	/**
	 * Add clause to underlying ClauseSet without propagating.
	 * Watches are set on cl[0] and cl[1] (if cl.size() >= 3)
	 * returns reason with which cl[0] might be propagated
	 */
	Reason addClause(const std::vector<Lit>& cl);

	/** propagate x and unrolls immediately. Returns number of propagations or -1 on conflict */
	int probe(Lit x);

	/**
	 * Probe all unassigned literals and propagate inverse of all failings.
	 * Reuturns most active variable or -2 on conflict or -1 if everything is set already.
	 */
	int probeFull();

	int unassignedVariable() const; /** -1 if everything is assigned */

	int level() const; /** current level */
	void unroll(int l); /** unroll all assignments in levels > l, and set level to l */
	int analyzeConflict(std::vector<Lit>& learnt) const;

	/** for debugging */
	void printTrail() const;
};

#endif
