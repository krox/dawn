#pragma once

#include "sat/clause.h"
#include "sat/extender.h"
#include "sat/stats.h"
#include "util/bit_vector.h"
#include "util/small_vector.h"
#include <cassert>
#include <iterator>
#include <sstream>
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
	std::vector<Lit> to_outer_; // inner variable -> outer literal

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

	// Rules needed to extend solution to original problem.
	// 'outer' variable numbering.
	Extender extender;

	// constructors
	Sat() noexcept;
	explicit Sat(int n, ClauseStorage clauses_ = {});

	// would work fine, just never used so we disallow copies to prevent bugs
	Sat(Sat const &) = delete;
	Sat &operator=(Sat const &) = delete;

	/** translate inner to outer (can return Lit::zero()/Lit::one() for fixed)*/
	Lit to_outer(Lit a) const;

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

	// add clause ('inner' numbering, normalizes clause)
	void add_clause_safe(util::span<const Lit> lits);
	void add_clause_safe(std::string_view lits);

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
	util::bit_vector polarity;
	double activityInc = 1.0;
	void bumpVariableActivity(int i);
	void decayVariableActivity();

	size_t memory_usage() const;
};

void shuffleVariables(Sat &sat);

inline Sat::Sat() noexcept : Sat(0) {}

inline Sat::Sat(int n, ClauseStorage clauses_)
    : to_outer_(n), bins(2 * n), clauses(std::move(clauses_)), extender(n),
      activity(n, 0.0), polarity(n)
{
	for (int i = 0; i < n; ++i)
		to_outer_[i] = Lit(i, false);

	for (auto [ci, cl] : clauses)
	{
		(void)ci;
		cl.normalize();
		if (cl.isRemoved() || cl.size() >= 3)
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

inline Lit Sat::to_outer(Lit a) const
{
	if (!a.proper())
		return a;
	assert(a.var() < varCount());
	return to_outer_[a.var()] ^ a.sign();
}

inline int Sat::varCount() const { return (int)to_outer_.size(); }
inline int Sat::varCountOuter() const { return extender.var_count(); }

inline int Sat::addVar()
{
	int inner = varCount();
	int outer = extender.add_var();
	bins.emplace_back();
	bins.emplace_back();
	activity.push_back(0.0);
	polarity.push_back(false);
	to_outer_.push_back(Lit(outer, false));
	return inner;
}

inline int Sat::addVarOuter()
{
	int i = addVar();
	return to_outer_[i].var();
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

inline void Sat::add_clause_safe(util::span<const Lit> lits)
{
	assert(buf_.size() == 0);
	for (auto a : lits)
	{
		assert(a.proper() || a.fixed());
		buf_.push_back(a);
	}
	int s = normalizeClause(buf_);
	if (s != -1)
	{
		buf_.resize(s);
		addClause(buf_, true);
	}
	buf_.resize(0);
}

inline void Sat::add_clause_safe(std::string_view cl)
{
	std::vector<Lit> lits;
	std::istringstream iss{std::string{cl}};
	for (auto it = std::istream_iterator<std::string>(iss),
	          end = std::istream_iterator<std::string>();
	     it != end; ++it)
		lits.push_back(Lit::fromDimacs(std::stoi(*it)));
	add_clause_safe(lits);
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

// create list of all clauses (active and extension) in outer numbering
ClauseStorage getAllClausesOuter(Sat const &sat);

void dump(Sat const &sat);
void dumpOuter(std::string const &filename, Sat const &sat);

/**
 * run unit propagation + SCC until fixed point.
 * returns number of removed variables.
 */
int cleanup(Sat &sat);

} // namespace dawn

template <> struct fmt::formatter<dawn::Sat>
{
	constexpr auto parse(format_parse_context &ctx) { return ctx.begin(); }

	template <typename FormatContext>
	auto format(dawn::Sat const &sat, FormatContext &ctx)
	{
		auto clauses = getAllClausesOuter(sat);
		auto it = format_to(ctx.out(), "p cnf {} {}\n", sat.varCountOuter(),
		                    clauses.count());
		for (auto [ci, cl] : clauses)
		{
			(void)ci;
			it = format_to(it, "{} 0\n", cl);
		}
		return it;
	}
};
