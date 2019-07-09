#ifndef SAT_SAT_H
#define SAT_SAT_H

#include "clause.h"
#include <iostream>
#include <vector>

/**
 * Sat problem in conjunctive normal form, i.e. a set of clauses.
 *   - Empty/Unary/Binary clauses are stored seprately from long clauses.
 *   - No watch-lists/occ-lists.
 */
class Sat
{
  public:
	/** storage of clauses */
	bool contradiction = false;
	std::vector<Lit> units;
	std::vector<std::vector<Lit>> bins;
	ClauseStorage clauses;

	/** constructor */
	Sat();
	explicit Sat(int n);

	Sat(const Sat &) = delete;
	Sat(const Sat &&) = delete;

	/** add a new variable */
	uint32_t addVar();
	uint32_t varCount() const;

	/** add clause ('inner' numbering, no checking of tautologies and such) */
	void addEmpty();
	void addUnary(Lit a);
	void addBinary(Lit a, Lit b);
	CRef addLong(span<const Lit> lits);
	void addClause(span<const Lit> lits);

	/** number of clauses */
	size_t unaryCount() const;
	size_t binaryCount() const;
	size_t longCount() const;
	size_t clauseCount() const;

	/**
	 * - Remove fixed variables from clauses (keeps unit clauses itself)
	 * - Remove (some) duplicate clauses
	 * - invalidates all CRefs
	 */
	void cleanup();

	friend std::ostream &operator<<(std::ostream &stream, const Sat &cs);
};

inline Sat::Sat() {}

inline Sat::Sat(int n) : bins(2 * n) {}

inline uint32_t Sat::addVar()
{
	auto i = varCount();
	bins.emplace_back();
	bins.emplace_back();
	return i;
}

inline uint32_t Sat::varCount() const { return (uint32_t)bins.size() / 2; }

inline void Sat::addEmpty() { contradiction = true; }

inline void Sat::addUnary(Lit a) { units.push_back(a); }

inline void Sat::addBinary(Lit a, Lit b)
{
	bins[a].push_back(b);
	bins[b].push_back(a);
}

inline CRef Sat::addLong(span<const Lit> lits)
{
	return clauses.addClause(lits);
}

inline void Sat::addClause(span<const Lit> lits)
{
	if (lits.size() == 0)
		addEmpty();
	else if (lits.size() == 1)
		addUnary(lits[0]);
	else if (lits.size() == 2)
		addBinary(lits[0], lits[1]);
	else
		addLong(lits);
}

inline size_t Sat::unaryCount() const { return units.size(); }

inline size_t Sat::binaryCount() const
{
	size_t r = 0;
	for (auto &b : bins)
		r += b.size();
	return r / 2;
}

inline size_t Sat::longCount() const
{
	size_t r = 0;
	for (auto _ [[maybe_unused]] : clauses)
		++r;
	return r;
}

inline size_t Sat::clauseCount() const
{
	return unaryCount() + binaryCount() + longCount();
}

#endif
