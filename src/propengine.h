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

	int unassignedVariable() const; /** -1 if everything is assigned */

	int level() const; /** current level */
	void newLevel(); /** start a new level */
	void unrollLevel(int l); /** unroll all assignments in levels > l, and set level to l */
};

#endif
