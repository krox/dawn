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

public:
	std::vector<bool> assign;

	/** constructor */
	PropEngine(ClauseSet& cs);

	/** Set literal x. Does nothing if already set and return false on conflict. */
	bool set(Lit x);	// no unit propagation
	bool propagateBinary(Lit x); // binary unit propagation
	bool propagateFull(Lit x); // full unit propagation

	/** propagate x and unrolls immediately. Returns number of propagations or -1 on conflict */
	int probe(Lit x);

	/**
	 * Probe all unassigned literals and propagate inverse of all failings.
	 * Reuturns most active variable or -2 on conflict or -1 if everything is set already.
	 */
	int probeFull();

	int unassignedVariable() const; /** -1 if everything is assigned */

	int level() const; /** current level */
	void newLevel(); /** start a new level */
	void unrollLevel(int l); /** unroll all assignments in levels > l, and set level to l */


};

#endif
