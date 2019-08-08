#ifndef SAT_SAT_H
#define SAT_SAT_H

#include "sat/clause.h"
#include "sat/stats.h"
#include "util/small_vector.h"
#include <cassert>
#include <iostream>
#include <vector>

/**
 * Sat problem in conjunctive normal form, i.e. a set of clauses.
 *   - Empty/Unary/Binary clauses are stored seprately from long clauses.
 *   - No watch-lists/occ-lists.
 */
class Sat
{
  private:
	std::vector<Lit> outerToInner_; // outer variable -> inner literal
	std::vector<Lit> buf_;          // temporary

  public:
	Stats stats;

	/** storage of clauses */
	bool contradiction = false;
	std::vector<Lit> units;
	using bins_t = std::vector<util::small_vector<Lit, 6>>;
	bins_t bins;
	ClauseStorage clauses;

	/** constructor */
	Sat();
	explicit Sat(int n);

	Sat(const Sat &) = delete;
	Sat(const Sat &&) = delete;

	/** translate outer to inner (can return Lit::zero()/Lit::one() for fixed)*/
	Lit outerToInner(Lit a) const;

	/** add/count variables in the 'inner' problem */
	int addVar();
	int varCount() const;

	/** add/count variables in the 'outer problem */
	int addVarOuter();
	int varCountOuter() const;

	/** add clause ('inner' numbering, no checking of tautologies and such) */
	void addEmpty();
	void addUnary(Lit a);
	void addBinary(Lit a, Lit b);
	CRef addLong(span<const Lit> lits, bool irred);
	void addClause(span<const Lit> lits, bool irred);

	/** add clause ('outer' numbering, normalizes clause) */
	void addClauseOuter(span<const Lit> lits);

	/** number of clauses */
	size_t unaryCount() const;
	size_t binaryCount() const;
	size_t longCount() const;
	size_t clauseCount() const;
	size_t longCountIrred() const;
	size_t longCountRed() const;

	/**
	 * - Remove fixed variables from clauses (keeps unit clauses itself)
	 * - Remove (some) duplicate clauses
	 * - invalidates all CRefs
	 */
	void cleanup();

	/**
	 * - Renumber variables allowing for fixed and equivalent vars
	 * - invalidates all CRefs
	 */
	void renumber(span<const Lit> trans, int newVarCount);

	/** tracking of variable activity and polarity */
	std::vector<double> activity;
	std::vector<bool> polarity;
	double activityInc = 1.0;
	void bumpVariableActivity(int i);
	void decayVariableActivity();

	friend std::ostream &operator<<(std::ostream &stream, const Sat &cs);
};

void shuffleVariables(Sat &sat);

inline Sat::Sat() {}

inline Sat::Sat(int n)
    : outerToInner_(n), bins(2 * n), activity(n, 0.0), polarity(n, false)
{
	for (int i = 0; i < n; ++i)
		outerToInner_[i] = Lit(i, false);
}

inline Lit Sat::outerToInner(Lit a) const
{
	if (!a.proper())
		return a;
	assert(a.var() < varCountOuter());
	return outerToInner_[a.var()] ^ a.sign();
}

inline int Sat::addVar()
{
	auto i = varCount();
	bins.emplace_back();
	bins.emplace_back();
	activity.push_back(0.0);
	polarity.push_back(false);
	return i;
}

inline int Sat::varCount() const { return (int)bins.size() / 2; }

inline int Sat::addVarOuter()
{
	auto i = varCountOuter();
	outerToInner_.push_back(Lit(addVar(), false));
	return i;
}

inline int Sat::varCountOuter() const { return (uint32_t)outerToInner_.size(); }

inline void Sat::addEmpty() { contradiction = true; }

inline void Sat::addUnary(Lit a)
{
	assert(a.proper());
	assert(a.var() < varCount());

	units.push_back(a);
}

inline void Sat::addBinary(Lit a, Lit b)
{
	assert(a.proper());
	assert(a.var() < varCount());
	assert(b.proper());
	assert(b.var() < varCount());
	assert(a.var() != b.var());

	bins[a].push_back(b);
	bins[b].push_back(a);
}

inline CRef Sat::addLong(span<const Lit> lits, bool irred)
{
	for (size_t i = 0; i < lits.size(); ++i)
	{
		assert(lits[i].proper());
		assert(lits[i].var() < varCount());
	}
	for (size_t i = 0; i < lits.size(); ++i)
		for (size_t j = 0; j < i; ++j)
			assert(lits[i].var() != lits[j].var());

	return clauses.addClause(lits, irred);
}

inline void Sat::addClause(span<const Lit> lits, bool irred)
{
	if (lits.size() == 0)
		addEmpty();
	else if (lits.size() == 1)
		addUnary(lits[0]);
	else if (lits.size() == 2)
		addBinary(lits[0], lits[1]);
	else
		addLong(lits, irred);
}

inline void Sat::addClauseOuter(span<const Lit> lits)
{
	assert(buf_.size() == 0);
	for (auto a : lits)
		buf_.push_back(outerToInner(a));
	int s = normalizeClause(buf_);
	if (s != -1)
	{
		buf_.resize(s);
		addClause(buf_, true);
	}
	buf_.resize(0);
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

inline size_t Sat::longCountIrred() const
{
	size_t r = 0;
	for (auto [_, cl] : clauses)
		if ((void)_, cl.irred())
			++r;
	return r;
}

inline size_t Sat::longCountRed() const
{
	size_t r = 0;
	for (auto [_, cl] : clauses)
		if ((void)_, !cl.irred())
			++r;
	return r;
}

inline size_t Sat::clauseCount() const
{
	return unaryCount() + binaryCount() + longCount();
}

inline void Sat::bumpVariableActivity(int i) { activity[i] += activityInc; }

inline void Sat::decayVariableActivity()
{
	activityInc *= 1.05;

	// scale everything down if neccessary
	if (activityInc > 1e100)
	{
		activityInc /= 1e100;
		for (int i = 0; i < varCount(); ++i)
			activity[i] /= 1e100;
	}
}

#endif
