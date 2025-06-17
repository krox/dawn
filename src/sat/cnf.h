#pragma once

#include "sat/clause.h"
#include "sat/reconstruction.h"
#include "sat/stats.h"
#include "util/bit_vector.h"
#include "util/iterator.h"
#include "util/logging.h"
#include "util/stats.h"
#include "util/vector.h"
#include <cassert>
#include <string_view>
#include <vector>

namespace dawn {

// Sat problem in conjunctive normal form, i.e. a set of clauses
//   - clauses of lenght <= 2 are stored seprately from long clauses
//   - does not contain watches or occurence lists or anything advanced
class Cnf
{
	Reconstruction recon_;

  public:
	util::xoshiro256 rng;

	bool contradiction = false;
	std::vector<Lit> units;
	using bins_t = std::vector<util::small_vector<Lit, 7>>;
	bins_t bins;
	ClauseStorage clauses;

	// constructors
	explicit Cnf(int n, ClauseStorage clauses_ = {});
	Cnf() noexcept : Cnf(0) {}

	// would work fine, just never used so we disallow copies to prevent bugs
	Cnf(Cnf const &) = delete;
	Cnf &operator=(Cnf const &) = delete;

	// add/count variables
	int add_var();
	int var_count() const;

	// ranges for convenient iteration
	auto all_vars() const { return util::iota_view(0, var_count()); }
	auto all_lits() const
	{
		return util::transform(util::iota_view(0, 2 * var_count()),
		                       [](int i) { return Lit(i); });
	}

	// add clause (no checking of tautologies and such)
	void add_empty();
	void add_unary(Lit a);
	void add_binary(Lit a, Lit b);
	CRef add_ternary(Lit a, Lit b, Lit c, Color color);
	CRef add_long(std::span<const Lit> lits, Color color);
	CRef add_clause(std::span<const Lit> lits, Color color);

	// add clause (normalizes clause)
	void add_clause_safe(std::span<const Lit> lits);
	void add_clause_safe(std::string_view lits);

	// add gates (normalizes clauses)
	void add_and_clause_safe(Lit a, Lit b, Lit c);           // a = b & c
	void add_or_clause_safe(Lit a, Lit b, Lit c);            // a = b | c
	void add_xor_clause_safe(Lit a, Lit b, Lit c);           // a = b ^ c
	void add_xor_clause_safe(Lit a, Lit b, Lit c, Lit d);    // a = b ^ c ^ d
	void add_maj_clause_safe(Lit a, Lit b, Lit c, Lit d);    // a = b+c+d >= 2
	void add_choose_clause_safe(Lit a, Lit b, Lit c, Lit d); // a = b ? c : d

	// number of clauses
	size_t unary_count() const;
	size_t binary_count() const;
	size_t long_count() const;
	size_t clause_count() const;
	size_t long_count_irred() const;
	size_t long_count_red() const;
	size_t lit_count_irred() const;
	util::IntHistogram clause_histogram() const;

	// solution reconstruction for non-equivalent transformations
	void add_rule(std::span<const Lit> cl);
	void add_rule(std::span<const Lit> cl, Lit pivot);
	Assignment reconstruct_solution(Assignment const &a) const;

	// renumber variables allowing for fixed and equivalent vars
	//     - invalidates all CRefs
	//     - suggested to call clauses.compacitfy() afterwards
	//     - if trans[v] is Lit::elim(), v may not appear in any clause
	void renumber(std::span<const Lit> trans, int newVarCount);

	size_t memory_usage() const;
};

inline int Cnf::var_count() const { return (int)bins.size() / 2; }

inline int Cnf::add_var()
{
	int inner = var_count();
	bins.emplace_back();
	bins.emplace_back();
	return inner;
}

inline void Cnf::add_empty() { contradiction = true; }

inline void Cnf::add_unary(Lit a)
{
	assert(a.proper());
	assert(a.var() < var_count());

	units.push_back(a);
}

inline void Cnf::add_binary(Lit a, Lit b)
{
	assert(a.proper());
	assert(a.var() < var_count());
	assert(b.proper());
	assert(b.var() < var_count());
	assert(a.var() != b.var());

	bins[a].push_back(b);
	bins[b].push_back(a);
}

inline CRef Cnf::add_ternary(Lit a, Lit b, Lit c, Color color)
{
	assert(a.proper() && a.var() < var_count());
	assert(b.proper() && b.var() < var_count());
	assert(c.proper() && c.var() < var_count());
	assert(a.var() != b.var() && a.var() != c.var() && b.var() != c.var());

	return clauses.add_clause({{a, b, c}}, color);
}

inline CRef Cnf::add_long(std::span<const Lit> lits, Color color)
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

	return clauses.add_clause(lits, color);
}

inline CRef Cnf::add_clause(std::span<const Lit> lits, Color color)
{
	if (lits.size() >= 3)
		return add_long(lits, color);

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

// cheap simplifications that should probably be run before and after any more
// serious searches
//   * runs until fixed point:
//       * unit propagation
//       * equivalent literal substitution
//       * failed literal probing
//       * hyper binary resolution
//       * transitive binary reduction
//       * compactify clause storage
//   * TODO:
//       * pure literal elimination
//       * disconnected components?
void cleanup(Cnf &);

// check that
//     * no contradiction
//     * no unit clauses
//     * no equivalent variables
bool is_normal_form(Cnf const &);

void shuffleVariables(Cnf &d);

// simple statistics (clause-size histograms and such)
void print_stats(Cnf const &cnf);

} // namespace dawn

template <> struct fmt::formatter<dawn::Cnf>
{
	constexpr auto parse(format_parse_context &ctx) { return ctx.begin(); }

	template <typename FormatContext>
	auto format(dawn::Cnf const &sat, FormatContext &ctx) const
	{
		using namespace dawn;
		auto it = fmt::format_to(ctx.out(), "p cnf {} {}\n", sat.var_count(),
		                         sat.clause_count());

		// empty clause
		if (sat.contradiction)
			it = fmt::format_to(it, "0\n");

		// unary clauses
		auto units = sat.units;
		std::sort(units.begin(), units.end());
		for (auto a : units)
			it = fmt::format_to(it, "{} 0\n", a);

		// binary clauses
		for (Lit l : sat.all_lits())
		{
			auto tmp = sat.bins[l];
			std::sort(tmp.begin(), tmp.end());
			for (auto b : tmp)
				if (l <= b)
					it = fmt::format_to(it, "{} {} 0\n", l, b);
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
			it = fmt::format_to(it, "{} 0\n", sat.clauses[i]);

		return it;
	}
};
