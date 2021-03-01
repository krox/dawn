#pragma once

#include "sat/clause.h"
#include "sat/stats.h"
#include "util/small_vector.h"
#include <cassert>
#include <vector>

namespace dawn {

/**
 * Sat problem in conjunctive normal form, i.e. a set of clauses.
 *   - Empty/Unary/Binary clauses are stored seprately from long clauses.
 *   - No watch-lists/occ-lists.
 */
class Sat
{
  private:
	std::vector<Lit> outer_to_inner_; // outer variable -> inner literal
	std::vector<Lit> inner_to_outer_;

	std::vector<Lit> buf_; // temporary

  public:
	Stats stats;
	util::xoshiro256 rng;

	/** storage of clauses ('inner' variable numbers) */
	bool contradiction = false;
	std::vector<Lit> units;
	using bins_t = std::vector<util::small_vector<Lit, 6>>;
	bins_t bins;
	ClauseStorage clauses;

	/**
	 * clauses needed to extend solution to full problem if variable
	 * elimination was performed
	 *   - 'outer' variable numbering
	 *   - can contain small clauses (i.e. no implicit binaries)
	 */
	ClauseStorage extension_clauses;
	std::vector<int> removed_vars; // consider in reverse when extending sol

	/** constructor */
	Sat();
	explicit Sat(int n, ClauseStorage clauses_ = {});

	Sat(const Sat &) = delete;
	Sat(const Sat &&) = delete;

	/** translate outer to inner (can return Lit::zero()/Lit::one() for fixed)*/
	Lit outerToInner(Lit a) const;
	Lit innerToOuter(Lit a) const;

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
	CRef addLong(util::span<const Lit> lits, bool irred);
	CRef addClause(util::span<const Lit> lits, bool irred);

	/** add clause ('outer' numbering, normalizes clause) */
	void addClauseOuter(util::span<const Lit> lits);

	/** number of clauses */
	size_t unaryCount() const;
	size_t binaryCount() const;
	size_t longCount() const;
	size_t clauseCount() const;
	size_t longCountIrred() const;
	size_t longCountRed() const;

	/**
	 * - renumber variables allowing for fixed and equivalent vars
	 * - invalidates all CRefs
	 * - suggested to call clauses.compacitfy() afterwards
	 * - if trans[v] is Lit::elim(), the variable v may not appear in any clause
	 */
	void renumber(util::span<const Lit> trans, int newVarCount);

	/** tracking of variable activity and polarity */
	std::vector<double> activity;
	std::vector<bool> polarity;
	double activityInc = 1.0;
	void bumpVariableActivity(int i);
	void decayVariableActivity();

	size_t memory_usage() const;
};

void shuffleVariables(Sat &sat);

inline Sat::Sat() {}

inline Sat::Sat(int n, ClauseStorage clauses_)
    : outer_to_inner_(n), inner_to_outer_(n), bins(2 * n),
      clauses(std::move(clauses_)), activity(n, 0.0), polarity(n, false)
{
	for (int i = 0; i < n; ++i)
	{
		outer_to_inner_[i] = Lit(i, false);
		inner_to_outer_[i] = Lit(i, false);
	}

	for (auto [ci, cl] : clauses)
	{
		(void)ci;
		cl.normalize();
		if (cl.size() >= 3)
			continue;
		if (cl.size() == 0)
			addEmpty();
		else if (cl.size() == 1)
			addUnary(cl[0]);
		else if (cl.size() == 2)
			addBinary(cl[0], cl[1]);
		else
			assert(false);
		cl.remove();
	}
}

inline Lit Sat::outerToInner(Lit a) const
{
	if (!a.proper())
		return a;
	assert(a.var() < varCountOuter());
	if (outer_to_inner_[a.var()] == Lit::elim())
		return Lit::elim();
	return outer_to_inner_[a.var()] ^ a.sign();
}

inline Lit Sat::innerToOuter(Lit a) const
{
	if (!a.proper())
		return a;
	assert(a.var() < varCount());
	return inner_to_outer_[a.var()] ^ a.sign();
}

inline int Sat::varCount() const { return (int)inner_to_outer_.size(); }
inline int Sat::varCountOuter() const { return (int)outer_to_inner_.size(); }

inline int Sat::addVar()
{
	int inner = varCount();
	int outer = varCountOuter();
	bins.emplace_back();
	bins.emplace_back();
	activity.push_back(0.0);
	polarity.push_back(false);
	outer_to_inner_.push_back(Lit(inner, false));
	inner_to_outer_.push_back(Lit(outer, false));
	return inner;
}

inline int Sat::addVarOuter()
{
	int i = addVar();
	return inner_to_outer_[i].var();
}

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

inline CRef Sat::addLong(util::span<const Lit> lits, bool irred)
{
	for (size_t i = 0; i < lits.size(); ++i)
	{
		assert(lits[i].proper());
		assert(lits[i].var() < varCount());
	}
	for (size_t i = 0; i < lits.size(); ++i)
		for (size_t j = 0; j < i; ++j)
			assert(lits[i].var() != lits[j].var());
	assert(lits.size() >= 3);

	return clauses.addClause(lits, irred);
}

inline CRef Sat::addClause(util::span<const Lit> lits, bool irred)
{
	if (lits.size() >= 3)
		return addLong(lits, irred);

	if (lits.size() == 0)
		addEmpty();
	else if (lits.size() == 1)
		addUnary(lits[0]);
	else if (lits.size() == 2)
		addBinary(lits[0], lits[1]);
	else
		assert(false);
	return CRef::undef();
}

inline void Sat::addClauseOuter(util::span<const Lit> lits)
{
	assert(buf_.size() == 0);
	for (auto a : lits)
	{
		auto b = outerToInner(a);
		assert(b.proper() || b.fixed());
		buf_.push_back(b);
	}
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

inline size_t Sat::longCount() const { return clauses.count(); }

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
	return unaryCount() + binaryCount() + longCount() + contradiction;
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

void dump(Sat const &sat);
void dumpOuter(std::string const &filename, Sat const &sat);

} // namespace dawn
