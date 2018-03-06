#ifndef PROPENGINE_H
#define PROPENGINE_H

#include <vector>
#include <cassert>
#include "sat.h"

/**
 * Unit propagation.
 */
class PropEngine
{
	ClauseSet& cs;
	std::vector<std::vector<CRef>> watches;
	std::vector<Lit> trail;
	std::vector<size_t> mark;

	void set(Lit x);	// no unit propagation
	void propagateBinary(Lit x); // binary unit propagation

public:
	std::vector<bool> assign;
	bool conflict = false;

	/** constructor */
	PropEngine(ClauseSet& cs);

	/** assign a literal and do unit propagation */
	void branch(Lit x); // starts a new level
	void propagateFull(Lit x); // stays on current level

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
};

#endif
