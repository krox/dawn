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
	BinaryGraph bins;
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

	// add clause (no normalization)
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
	void add_and_clause_safe(Lit a, Lit b, Lit c);        // a = b & c
	void add_or_clause_safe(Lit a, Lit b, Lit c);         // a = b | c
	void add_xor_clause_safe(Lit a, Lit b, Lit c);        // a = b ^ c
	void add_xor_clause_safe(Lit a, Lit b, Lit c, Lit d); // a = b ^ c ^ d
	void add_maj_clause_safe(Lit a, Lit b, Lit c, Lit d); // a = b+c+d >= 2
	void add_ite_clause_safe(Lit a, Lit b, Lit c, Lit d); // a = b ? c : d

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

// Topological order of all literals, i.e., an order such that all binary
// implications go 'from left to right'. If there are cycles in the graph
// (indicated by valid=false), no strict topological order exists, but the
// computed order is still some approximation thereof (namely a "post-order in
// the reversed graph), which might still be useful heuristically.
struct TopOrder
{
	std::vector<Lit> lits;  // literals in order
	std::vector<int> order; // position of each lit
	bool valid;             // false if there are cycles

	TopOrder(BinaryGraph const &);
};

// propagate unit clauses until fixed-point
int run_unit_propagation(Cnf &);

// Find and replace equivalent variables.
//    - Very fast (linear in problem size)
//    - Returns number of equivalences found (cnf is unchanged if zero)
//    - Replacing lits in long clauses can lead to new binary clauses and
//    thus
//      equivalences. Therefore this function needs to be iterated in
//      order to guarantee acyclicity of the binary graph.
int run_scc(Cnf &);

// remove redundant binary clauses
//   - fails if there are cycles in the binary implication graph
//   - O(n^2) in principle, but very fast in practice
//   - as a side effect, binaries in cnf.bins are sorted in topological
//   order
//     (which is useful for some heuristic arguments)
void run_binary_reduction(Cnf &);

// runs cheap simplifications until fixed-point. This should usually be run
// before and after any more serious searches and transformations. Includes:
//   * unit propagation
//   * equivalent literal substitution
//   * failed literal probing with full hyper binary resolution
//   * transitive binary reduction
//   * compactify clause storage
//   * TODO:
//       * pure literal elimination
//       * disconnected components?
void cleanup(Cnf &);

// check that
//     * no contradiction
//     * no unit clauses
//     * no equivalent variables
bool is_normal_form(Cnf const &);

// randomly shuffle variable numbers and signs
void shuffle_variables(Cnf &d);

// print some stats about the binary implication graph
void print_binary_stats(BinaryGraph const &g);

// simple statistics (clause-size histograms and such)
void print_stats(Cnf const &cnf);

inline int Cnf::add_var() { return bins.add_var(); }

inline int Cnf::var_count() const { return bins.var_count(); }

inline void Cnf::add_empty() { contradiction = true; }

inline void Cnf::add_unary(Lit a)
{
	assert(a.proper() && a.var() < var_count());
	units.push_back(a);
}

inline void Cnf::add_binary(Lit a, Lit b) { bins.add(a, b); }

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
