#ifndef SAT_H
#define SAT_H

#include <vector>
#include <iostream>
#include "clause.h"


/**
 * Sat problem as a basic set of clauses.
 *   - Empty/Unary/Binary clauses are stored seprately from long clauses.
 *   - No watch-lists/occ-lists.
 */
class ClauseSet
{
public:
	/** storage of clauses */
	bool contradiction = false;
	std::vector<Lit> units;
	std::vector<std::vector<Lit>> bins;
	ClauseStorage clauses;

	/** add a new variable */
	uint32_t addVar();
	inline uint32_t varCount() const;

	/** add clause ('inner' numbering, no checking of tautologies and such) */
	CRef addEmpty();
	CRef addUnary(Lit a);
	CRef addBinary(Lit a, Lit b);
	CRef addClause(const std::vector<Lit>& lits);

	friend std::ostream& operator<<(std::ostream& stream, const ClauseSet& cs);
};

inline uint32_t ClauseSet::addVar()
{
	auto i = varCount();
	bins.emplace_back();
	bins.emplace_back();
	return i;
}

inline uint32_t ClauseSet::varCount() const
{
	return (uint32_t)bins.size()/2;
}

inline CRef ClauseSet::addEmpty()
{
	contradiction = true;
	return CRef(-1);
}

inline CRef ClauseSet::addUnary(Lit a)
{
	units.push_back(a);
	return CRef(-1);
}

inline CRef ClauseSet::addBinary(Lit a, Lit b)
{
	bins[a.toInt()].push_back(b);
	bins[b.toInt()].push_back(a);
	return CRef(-1);
}

inline CRef ClauseSet::addClause(const std::vector<Lit>& lits)
{
	if(lits.size() == 0)
		return addEmpty();
	if(lits.size() == 1)
		return addUnary(lits[0]);
	if(lits.size() == 2)
		return addBinary(lits[0], lits[1]);
	return clauses.addClause(lits);
}

#endif
