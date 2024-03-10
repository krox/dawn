#include "sat/cnf.h"

#include "fmt/format.h"
#include "util/stats.h"
#include <algorithm>
#include <cassert>
#include <random>
#include <sstream>

namespace dawn {

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

void Cnf::renumber(std::span<const Lit> trans, int newVarCount)
{
	// check input
	assert(trans.size() == (size_t)var_count());
	for (Lit l : trans)
		assert(l.fixed() || l == Lit::elim() ||
		       (l.proper() && l.var() < newVarCount));

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
		for (Lit &a : cl.lits())
			a = trans[a.var()] ^ a.sign();
		cl.normalize();
		if (cl.removed())
			continue;
		if (cl.size() == 0)
			add_empty();
		if (cl.size() == 1)
			add_unary(cl[0]);
		if (cl.size() == 2)
			add_binary(cl[0], cl[1]);
		if (cl.size() <= 2)
			cl.set_removed();
	}
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
		if (cl.irred())
			++r;
	return r;
}

size_t Cnf::long_count_red() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (!cl.irred())
			++r;
	return r;
}

size_t Cnf::lit_count_irred() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (cl.irred())
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
} // namespace dawn
