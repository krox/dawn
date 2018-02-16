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

	/** constructor */
	ClauseSet();
	explicit ClauseSet(int n);

	/** add a new variable */
	uint32_t addVar();
	uint32_t varCount() const;

	/** add clause ('inner' numbering, no checking of tautologies and such) */
	CRef addEmpty();
	CRef addUnary(Lit a);
	CRef addBinary(Lit a, Lit b);
	CRef addClause(const std::vector<Lit>& lits);

	friend std::ostream& operator<<(std::ostream& stream, const ClauseSet& cs);
};

inline ClauseSet::ClauseSet()
{}

inline ClauseSet::ClauseSet(int n)
	: bins(2*n)
{}

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
	return CREF_UNDEF;
}

inline CRef ClauseSet::addUnary(Lit a)
{
	units.push_back(a);
	return CREF_UNDEF;
}

inline CRef ClauseSet::addBinary(Lit a, Lit b)
{
	bins[a].push_back(b);
	bins[b].push_back(a);
	return CREF_UNDEF;
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
