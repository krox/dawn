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

// Sat problem in conjunctive normal form, i.e. a set of clauses
//   - clauses of lenght <= 2 are stored seprately from long clauses
//   - does not contain watches or occurence lists
class Sat
{
  private:
	std::vector<Lit> to_outer_; // inner variable -> outer literal
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
	explicit Sat(int n, ClauseStorage clauses_ = {});
	Sat() noexcept : Sat(0) {}

	// would work fine, just never used so we disallow copies to prevent bugs
	Sat(Sat const &) = delete;
	Sat &operator=(Sat const &) = delete;

	// translate inner to outer (can return Lit::zero()/Lit::one() for fixed)
	Lit to_outer(Lit a) const;

	// add/count variables
	int add_var();
	int var_count() const;

	// add/count variables in the 'outer problem
	int add_var_outer();
	int var_count_outer() const;

	// add clause (no checking of tautologies and such)
	void add_empty();
	void add_unary(Lit a);
	void add_binary(Lit a, Lit b);
	CRef add_long(util::span<const Lit> lits, bool irred);
	CRef add_clause(util::span<const Lit> lits, bool irred);

	// add clause (normalizes clause)
	void add_clause_safe(util::span<const Lit> lits);
	void add_clause_safe(std::string_view lits);

	// number of clauses
	size_t unary_count() const;
	size_t binary_count() const;
	size_t long_count() const;
	size_t clause_count() const;
	size_t long_count_irred() const;
	size_t long_count_red() const;
	size_t lit_count_irred() const;

	// ranges for convenient iteration
	auto all_vars() const { return util::iota_view(0, var_count()); }
	auto all_lits() const
	{
		return util::transform(util::iota_view(0, 2 * var_count()),
		                       [](int i) { return Lit(i); });
	}

	/**
	 * - renumber variables allowing for fixed and equivalent vars
	 * - invalidates all CRefs
	 * - suggested to call clauses.compacitfy() afterwards
	 * - if trans[v] is Lit::elim(), the variable v may not appear in any clause
	 */
	void renumber(util::span<const Lit> trans, int newVarCount);

	// tracking of variable activity and polarity
	std::vector<double> activity;
	util::bit_vector polarity;
	double activityInc = 1.0;
	void bump_variable_activity(int i);
	void decay_variable_activity();

	// sort clauses and literals in clauses. Invalidates all CRefs, just
	// intended for nicer human-readable output
	void sort_clauses();

	size_t memory_usage() const;
};

void shuffleVariables(Sat &sat);

inline Sat::Sat(int n, ClauseStorage clauses_)
    : to_outer_(n), bins(2 * n), clauses(std::move(clauses_)), extender(n),
      activity(n, 0.0), polarity(n)
{
	for (int i = 0; i < n; ++i)
		to_outer_[i] = Lit(i, false);

	for (auto &cl : clauses.all())
	{
		cl.normalize();
		if (cl.isRemoved() || cl.size() >= 3)
			continue;
		if (cl.size() == 0)
			add_empty();
		else if (cl.size() == 1)
			add_unary(cl[0]);
		else if (cl.size() == 2)
			add_binary(cl[0], cl[1]);
		else
			assert(false);
		cl.remove();
	}
}

inline Lit Sat::to_outer(Lit a) const
{
	if (!a.proper())
		return a;
	assert(a.var() < var_count());
	return to_outer_[a.var()] ^ a.sign();
}

inline int Sat::var_count() const { return (int)to_outer_.size(); }
inline int Sat::var_count_outer() const { return extender.var_count(); }

inline int Sat::add_var()
{
	int inner = var_count();
	int outer = extender.add_var();
	bins.emplace_back();
	bins.emplace_back();
	activity.push_back(0.0);
	polarity.push_back(false);
	to_outer_.push_back(Lit(outer, false));
	return inner;
}

inline int Sat::add_var_outer()
{
	int i = add_var();
	return to_outer_[i].var();
}

inline void Sat::add_empty() { contradiction = true; }

inline void Sat::add_unary(Lit a)
{
	assert(a.proper());
	assert(a.var() < var_count());

	units.push_back(a);
}

inline void Sat::add_binary(Lit a, Lit b)
{
	assert(a.proper());
	assert(a.var() < var_count());
	assert(b.proper());
	assert(b.var() < var_count());
	assert(a.var() != b.var());

	bins[a].push_back(b);
	bins[b].push_back(a);
}

inline CRef Sat::add_long(util::span<const Lit> lits, bool irred)
{
	for (size_t i = 0; i < lits.size(); ++i)
	{
		assert(lits[i].proper());
		assert(lits[i].var() < var_count());
	}
	for (size_t i = 0; i < lits.size(); ++i)
		for (size_t j = 0; j < i; ++j)
			assert(lits[i].var() != lits[j].var());
	assert(lits.size() >= 3);

	return clauses.addClause(lits, irred);
}

inline CRef Sat::add_clause(util::span<const Lit> lits, bool irred)
{
	if (lits.size() >= 3)
		return add_long(lits, irred);

	if (lits.size() == 0)
		add_empty();
	else if (lits.size() == 1)
		add_unary(lits[0]);
	else if (lits.size() == 2)
		add_binary(lits[0], lits[1]);
	else
		assert(false);
	return CRef::undef();
}

inline void Sat::add_clause_safe(util::span<const Lit> lits)
{
	util::small_vector<Lit, 16> buf;
	for (auto a : lits)
	{
		assert(a.proper() || a.fixed());
		buf.push_back(a);
	}
	int s = normalizeClause({buf.begin(), buf.end()});
	if (s != -1)
	{
		buf.resize(s);
		add_clause({buf.begin(), buf.end()}, true);
	}
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

inline size_t Sat::unary_count() const { return units.size(); }

inline size_t Sat::binary_count() const
{
	size_t r = 0;
	for (auto &b : bins)
		r += b.size();
	return r / 2;
}

inline size_t Sat::long_count() const { return clauses.count(); }

inline size_t Sat::long_count_irred() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (cl.irred())
			++r;
	return r;
}

inline size_t Sat::long_count_red() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (!cl.irred())
			++r;
	return r;
}

inline size_t Sat::lit_count_irred() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (cl.irred())
			r += cl.size();
	return r;
}

inline size_t Sat::clause_count() const
{
	return unary_count() + binary_count() + long_count() + contradiction;
}

inline void Sat::bump_variable_activity(int i) { activity[i] += activityInc; }

inline void Sat::decay_variable_activity()
{
	activityInc *= 1.05;

	// scale everything down if neccessary
	if (activityInc > 1e100)
	{
		activityInc /= 1e100;
		for (int i : all_vars())
			activity[i] /= 1e100;
	}
}

// create list of all clauses (active and extension) in outer numbering
ClauseStorage getAllClausesOuter(Sat const &sat);
ClauseStorage getAllClauses(Sat const &sat);

/**
 * run unit propagation + SCC until fixed point.
 * returns number of removed variables.
 */
int cleanup(Sat &sat);

// check that
//     * no contradiction
//     * no unit clauses
//     * no equivalent variables
bool is_normal_form(Sat const &sat);

} // namespace dawn

template <> struct fmt::formatter<dawn::Sat>
{
	constexpr auto parse(format_parse_context &ctx) { return ctx.begin(); }

	template <typename FormatContext>
	auto format(dawn::Sat const &sat, FormatContext &ctx)
	{
		using namespace dawn;
		auto it = format_to(ctx.out(), "p cnf {} {}\n", sat.var_count(),
		                    sat.clause_count());

		// empty clause
		if (sat.contradiction)
			it = format_to(it, "0\n");

		// unary clauses
		auto units = sat.units;
		std::sort(units.begin(), units.end());
		for (auto a : units)
			it = format_to(it, "{} 0\n", a);

		// binary clauses
		for (Lit l : sat.all_lits())
		{
			auto tmp = sat.bins[l];
			std::sort(tmp.begin(), tmp.end());
			for (auto b : tmp)
				if (l <= b)
					it = format_to(it, "{} {} 0\n", l, b);
		}

		// long clauses
		auto crefs =
		    std::vector(sat.clauses.crefs().begin(), sat.clauses.crefs().end());
		std::sort(crefs.begin(), crefs.end(), [&sat](CRef i, CRef j) {
			auto &a = sat.clauses[i];
			auto &b = sat.clauses[j];
			if (a.size() != b.size())
				return a.size() < b.size();
			else
				return std::lexicographical_compare(a.begin(), a.end(),
				                                    b.begin(), b.end());
		});
		for (auto i : crefs)
			it = format_to(it, "{} 0\n", sat.clauses[i]);

		return it;
	}
};
