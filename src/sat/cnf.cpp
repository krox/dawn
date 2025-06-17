#include "sat/cnf.h"

// TODO: move the 'cleanup' function somewhere else. Having it here creates
// (weak) cycles in the modules (cnf.cpp -> probing.h -> cnf.h)

#include "fmt/format.h"
#include "sat/binary.h"
#include "sat/probing.h"
#include "sat/propengine.h"
#include "util/logging.h"
#include "util/stats.h"
#include <algorithm>
#include <cassert>
#include <random>
#include <sstream>

namespace dawn {

Cnf::Cnf(int n, ClauseStorage clauses_)
    : recon_(n), bins(2 * n), clauses(std::move(clauses_))
{
	for (auto &cl : clauses.all())
	{
		cl.normalize();
		if (cl.color() == Color::black || cl.size() >= 3)
			continue;
		if (cl.size() == 0)
			add_empty();
		else if (cl.size() == 1)
			add_unary(cl[0]);
		else if (cl.size() == 2)
			add_binary(cl[0], cl[1]);
		else
			assert(false);
		cl.set_color(Color::black);
	}
	clauses.prune_black();
}

void Cnf::add_clause_safe(std::span<const Lit> lits)
{
	util::small_vector<Lit, 16> buf;
	for (auto a : lits)
	{
		assert(a.proper() || a.fixed());
		buf.push_back(a);
	}
	int s = normalize_clause({buf.begin(), buf.end()});
	if (s != -1)
	{
		buf.resize(s);
		add_clause({buf.begin(), buf.end()}, Color::blue);
	}
}

void Cnf::add_clause_safe(std::string_view cl)
{
	std::vector<Lit> lits;
	std::istringstream iss{std::string{cl}};
	for (auto it = std::istream_iterator<std::string>(iss),
	          end = std::istream_iterator<std::string>();
	     it != end; ++it)
		lits.push_back(Lit::fromDimacs(std::stoi(*it)));
	add_clause_safe(lits);
}

void Cnf::add_and_clause_safe(Lit a, Lit b, Lit c)
{
	add_clause_safe({{a, b.neg(), c.neg()}});
	add_clause_safe({{a.neg(), b}});
	add_clause_safe({{a.neg(), c}});
}

void Cnf::add_or_clause_safe(Lit a, Lit b, Lit c)
{
	add_and_clause_safe(a.neg(), b.neg(), c.neg());
}

void Cnf::add_xor_clause_safe(Lit a, Lit b, Lit c)
{
	add_clause_safe({{a, b, c.neg()}});
	add_clause_safe({{a, b.neg(), c}});
	add_clause_safe({{a.neg(), b, c}});
	add_clause_safe({{a.neg(), b.neg(), c.neg()}});
}

void Cnf::add_xor_clause_safe(Lit a, Lit b, Lit c, Lit d)
{
	add_clause_safe({{a, b, c, d.neg()}});
	add_clause_safe({{a, b, c.neg(), d}});
	add_clause_safe({{a, b.neg(), c, d}});
	add_clause_safe({{a.neg(), b, c, d}});
	add_clause_safe({{a, b.neg(), c.neg(), d.neg()}});
	add_clause_safe({{a.neg(), b, c.neg(), d.neg()}});
	add_clause_safe({{a.neg(), b.neg(), c, d.neg()}});
	add_clause_safe({{a.neg(), b.neg(), c.neg(), d}});
}

void Cnf::add_maj_clause_safe(Lit a, Lit b, Lit c, Lit d)
{
	add_clause_safe({{a.neg(), b, c}});
	add_clause_safe({{a.neg(), b, d}});
	add_clause_safe({{a.neg(), c, d}});
	add_clause_safe({{a, b.neg(), c.neg()}});
	add_clause_safe({{a, b.neg(), d.neg()}});
	add_clause_safe({{a, c.neg(), d.neg()}});
}

void Cnf::add_choose_clause_safe(Lit a, Lit b, Lit c, Lit d)
{
	add_clause_safe({{a, b.neg(), c.neg()}});
	add_clause_safe({{a, b, d.neg()}});
	add_clause_safe({{a.neg(), b.neg(), c}});
	add_clause_safe({{a.neg(), b, d}});

	// redundant clauses
	add_clause_safe({{a, c.neg(), d.neg()}});
	add_clause_safe({{a.neg(), c, d}});
}

void Cnf::renumber(std::span<const Lit> trans, int newVarCount)
{
	// check input
	assert(trans.size() == (size_t)var_count());
	for (Lit l : trans)
		assert(l.fixed() || l == Lit::elim() ||
		       (l.proper() && l.var() < newVarCount));

	recon_.renumber(trans, newVarCount);

	// renumber units
	{
		auto units_old = std::move(units);
		units.clear();
		for (Lit a : units_old)
		{
			a = trans[a.var()] ^ a.sign();
			if (a == Lit::one())
				continue;
			else if (a == Lit::zero())
				add_empty();
			else if (a.proper())
				add_unary(a);
			else
				assert(false); // disallows elim
		}
	}

	// renumber binaries
	{
		bins_t binsOld(newVarCount * 2);
		std::swap(bins, binsOld);

		for (int i = 0; i < (int)binsOld.size(); ++i)
		{
			const auto a = Lit(i);

			for (Lit b : binsOld[a])
			{
				assert(a.var() != b.var());
				if (a.var() < b.var())
					continue;

				// translate both literals
				Lit c = trans[a.var()] ^ a.sign();
				Lit d = trans[b.var()] ^ b.sign();

				if (c == Lit::elim() || c == Lit::undef() || d == Lit::elim() ||
				    d == Lit::undef())
					throw std::runtime_error(
					    "invalid renumbering: elim/undef in binary clause");

				// (true, x), (x, -x) -> tautology
				if (c == Lit::one() || d == Lit::one() || c == d.neg())
					continue;

				// (false, false) -> ()
				else if (c == Lit::zero() && d == Lit::zero())
					add_empty();

				// (false, x), (x, x) -> (x)
				else if (c == Lit::zero())
					add_unary(d);
				else if (d == Lit::zero())
					add_unary(c);
				else if (c == d)
					add_unary(c);

				// actual binary clause left
				else
					add_binary(c, d);
			}
		}
	}

	// renumber long clauses
	for (auto &cl : clauses.all())
	{
		if (cl.color() == Color::black)
			continue;
		for (Lit &a : cl.lits())
			a = trans[a.var()] ^ a.sign();
		cl.normalize();
		if (cl.color() == Color::black)
			continue;
		if (cl.size() == 0)
			add_empty();
		if (cl.size() == 1)
			add_unary(cl[0]);
		if (cl.size() == 2)
			add_binary(cl[0], cl[1]);
		if (cl.size() <= 2)
			cl.set_color(Color::black);
	}
	clauses.prune_black();
}

namespace {

int runUnitPropagation(Cnf &sat)
{
	// early out if no units
	if (!sat.contradiction && sat.units.empty())
		return 0;

	// the PropEngine constructor already does all the UP we want
	auto p = PropEngineLight(sat);

	// conflict -> add empty clause and remove everything else
	if (p.conflict)
	{
		sat.add_empty();
		sat.units.resize(0);
		for (int i = 0; i < sat.var_count() * 2; ++i)
			sat.bins[i].resize(0);
		sat.clauses.clear();
		int n = sat.var_count();
		sat.renumber(std::vector<Lit>(n, Lit::elim()), 0);
		return n;
	}

	assert(p.trail().size() != 0);

	auto trans = std::vector<Lit>(sat.var_count(), Lit::undef());
	for (Lit u : p.trail())
	{
		assert(trans[u.var()] != Lit::fixed(u.sign()).neg());
		trans[u.var()] = Lit::fixed(u.sign());
	}
	int newVarCount = 0;
	for (int i : sat.all_vars())
	{
		if (trans[i] == Lit::undef())
			trans[i] = Lit(newVarCount++, false);
	}

	// NOTE: this renumber() changes sat and thus invalidates p
	sat.renumber(trans, newVarCount);
	assert(sat.units.empty());

	return (int)p.trail().size();
}
} // namespace

void cleanup(Cnf &sat)
{
	auto log = util::Logger("cleanup");

	// NOTE: Theoretically, this loop could become quadratic. But in practice,
	// I never saw more than a few iterations, so we dont bother capping it.
	while (true)
	{
		runUnitPropagation(sat);
		if (run_scc(sat))
			continue;
		if (run_probing(sat))
			continue;
		break;
	}
	run_binary_reduction(sat);
	sat.clauses.prune_black();
	log.debug("now at {} vars, {} bins, {} irred, {} learnt", sat.var_count(),
	          sat.binary_count(), sat.long_count_irred(), sat.long_count_red());
}

bool is_normal_form(Cnf const &cnf)
{
	if (cnf.contradiction && cnf.var_count() != 0)
		return false;
	if (!cnf.units.empty())
		return false;
	if (auto top = TopOrder(cnf); !top.valid)
		return false;
	return true;
}

void shuffleVariables(Cnf &sat)
{
	auto trans = std::vector<Lit>(sat.var_count());
	for (int i : sat.all_vars())
	{
		trans[i] = Lit(i, std::bernoulli_distribution(0.5)(sat.rng));
		int j = std::uniform_int_distribution<int>(0, i)(sat.rng);
		std::swap(trans[i], trans[j]);
	}
	sat.renumber(trans, sat.var_count());
}

size_t Cnf::memory_usage() const
{
	size_t r = 0;
	r += units.capacity() * sizeof(Lit);
	for (auto &b : bins)
		r += b.capacity() * sizeof(Lit);
	r += clauses.memory_usage();
	return r;
}

size_t Cnf::unary_count() const { return units.size(); }

size_t Cnf::binary_count() const
{
	size_t r = 0;
	for (auto &b : bins)
		r += b.size();
	return r / 2;
}

size_t Cnf::long_count() const { return clauses.count(); }

size_t Cnf::long_count_irred() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (cl.color() == Color::blue)
			++r;
	return r;
}

size_t Cnf::long_count_red() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (cl.color() != Color::blue && cl.color() != Color::black)
			++r;
	return r;
}

size_t Cnf::lit_count_irred() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (cl.color() == Color::blue)
			r += cl.size();
	return r;
}

size_t Cnf::clause_count() const
{
	return unary_count() + binary_count() + long_count() + contradiction;
}

util::IntHistogram Cnf::clause_histogram() const
{
	util::IntHistogram r;
	r.add(0, contradiction ? 1 : 0);
	r.add(1, unary_count());
	r.add(2, binary_count());
	for (auto &cl : clauses.all())
		r.add(cl.size());
	return r;
}

void print_stats(Cnf const &cnf)
{
	util::IntHistogram blue, red;
	blue.add(0, cnf.contradiction ? 1 : 0);
	blue.add(1, cnf.unary_count());
	blue.add(2, cnf.binary_count());
	for (auto &cl : cnf.clauses.all())
		if (cl.color() == Color::blue)
			blue.add(cl.size());
		else
			red.add(cl.size());
	auto log = util::Logger("stats");
	log.info("nvars = {}", cnf.var_count());
	for (int k = 0; k <= std::max(blue.max(), red.max()); ++k)
		if (blue.bin(k) || red.bin(k))
			log.info("nclauses[{:3}] = {:5} + {:5}", k, blue.bin(k),
			         red.bin(k));
	log.info("nclauses[all] = {:5} + {:5}", blue.count(), red.count());
}

void Cnf::add_rule(std::span<const Lit> cl) { recon_.add_rule(cl); }
void Cnf::add_rule(std::span<const Lit> cl, Lit pivot)
{
	recon_.add_rule(cl, pivot);
}
Assignment Cnf::reconstruct_solution(Assignment const &a) const
{
	return recon_(a);
}

} // namespace dawn
