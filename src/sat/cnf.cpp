#include "sat/cnf.h"

#include "fmt/format.h"
#include <algorithm>
#include <cassert>
#include <random>
#include <sstream>

namespace dawn {

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

void Cnf::renumber(util::span<const Lit> trans, int newVarCount)
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
		if (cl.isRemoved())
			continue;
		if (cl.size() == 0)
			add_empty();
		if (cl.size() == 1)
			add_unary(cl[0]);
		if (cl.size() == 2)
			add_binary(cl[0], cl[1]);
		if (cl.size() <= 2)
			cl.remove();
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

} // namespace dawn
