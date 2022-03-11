#include "sat/sat.h"

#include "fmt/format.h"
#include "fmt/os.h"
#include <algorithm>
#include <cassert>
#include <random>

namespace dawn {

void Sat::renumber(util::span<const Lit> trans, int newVarCount)
{
	// check input
	assert(trans.size() == (size_t)varCount());
	for (Lit l : trans)
		assert(l.fixed() || l == Lit::elim() ||
		       (l.proper() && l.var() < newVarCount));

	// renumber units
	{
		std::vector<Lit> unitsOld;
		std::swap(units, unitsOld);

		for (Lit a : unitsOld)
		{
			a = trans[a.var()] ^ a.sign();
			if (a == Lit::one())
				continue;
			else if (a == Lit::zero())
				addEmpty();
			else if (a.proper())
				addUnary(a);
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
					addEmpty();

				// (false, x), (x, x) -> (x)
				else if (c == Lit::zero())
					addUnary(d);
				else if (d == Lit::zero())
					addUnary(c);
				else if (c == d)
					addUnary(c);

				// actual binary clause left
				else
					addBinary(c, d);
			}
		}
	}

	// renumber long clauses
	for (auto [_, cl] : clauses)
	{
		(void)_;
		for (Lit &a : cl.lits())
			a = trans[a.var()] ^ a.sign();
		cl.normalize();
		if (cl.isRemoved())
			continue;
		if (cl.size() == 0)
			addEmpty();
		if (cl.size() == 1)
			addUnary(cl[0]);
		if (cl.size() == 2)
			addBinary(cl[0], cl[1]);
		if (cl.size() <= 2)
			cl.remove();
	}

	// renumber activity array
	{
		std::vector<double> activityOld(newVarCount, 0.0);
		std::swap(activity, activityOld);

		for (int i = 0; i < (int)activityOld.size(); ++i)
			if (trans[i].proper())
			{
				int j = trans[i].var();

				// when multiple old variables are mapped to a single new one,
				// we take the maximum of the two activities
				activity[j] = std::max(activity[j], activityOld[i]);
			}
	}

	// renumber polarity array
	{
		// when multiple old variables are mapped to a single new one, take
		// arbitrary polarity (should be the same in most cases anyway)
		util::bit_vector polarityOld(newVarCount);
		std::swap(polarity, polarityOld);
		for (int i = 0; i < (int)polarityOld.size(); ++i)
			if (trans[i].proper())
			{
				int j = trans[i].var();
				polarity[j] = polarityOld[i] ^ trans[i].sign();
			}
	}

	// renumber translation arrays
	for (int outer = 0; outer < (int)varCountOuter(); ++outer)
	{
		Lit inner = outer_to_inner_[outer];

		// outer was already elim/fixed -> do nothing
		if (!inner.proper())
			continue;

		// variable is to be removed right now
		if (trans[inner.var()] == Lit::elim())
		{
			// if outer was previously removed by equivalence
			if (inner_to_outer_[inner.var()].var() != outer)
			{
				Lit outer2 = inner_to_outer_[inner.var()] ^ inner.sign();
				extender.set_equivalence(Lit(outer, false), outer2);
			}

			outer_to_inner_[outer] = Lit::elim();
			continue;
		}

		// variable is to be fixed or still active
		assert(trans[inner.var()].proper() || trans[inner.var()].fixed());
		outer_to_inner_[outer] = trans[inner.var()] ^ inner.sign();
	}

	inner_to_outer_.resize(0);
	inner_to_outer_.resize(newVarCount, Lit::undef());
	for (int outer = 0; outer < (int)varCountOuter(); ++outer)
	{
		Lit inner = outer_to_inner_[outer];
		if (!inner.proper())
			continue;
		if (inner_to_outer_[inner.var()] != Lit::undef())
			continue;
		inner_to_outer_[inner.var()] = Lit(outer, inner.sign());
	}
	for (Lit a : inner_to_outer_)
		assert(a.proper());
}

size_t Sat::memory_usage() const
{
	size_t r = 0;
	r += outer_to_inner_.capacity() * sizeof(Lit);
	r += units.capacity() * sizeof(Lit);
	for (int i = 0; i < varCount() * 2; ++i)
		r += bins[i].capacity() * sizeof(Lit);
	r += clauses.memory_usage();
	r += extender.memory_usage();
	return r;
}

void shuffleVariables(Sat &sat)
{
	auto trans = std::vector<Lit>(sat.varCount());
	for (int i = 0; i < sat.varCount(); ++i)
	{
		trans[i] = Lit(i, std::bernoulli_distribution(0.5)(sat.rng));
		int j = std::uniform_int_distribution<int>(0, i)(sat.rng);
		std::swap(trans[i], trans[j]);
	}
	sat.renumber(trans, sat.varCount());
}

void dump(Sat const &sat)
{
	fmt::print("p cnf {} {}\n", sat.varCount(), sat.clauseCount());

	// empty clause
	if (sat.contradiction)
		fmt::print("0\n");

	// unary clauses
	for (auto a : sat.units)
		fmt::print("{} 0\n", a);

	// binary clauses
	for (int l = 0; l < 2 * sat.varCount(); ++l)
		for (auto b : sat.bins[l])
			if (l <= b)
				fmt::print("{} {} 0\n", Lit(l), b);

	// long clauses
	for (auto [ci, cl] : sat.clauses)
	{
		(void)ci;
		fmt::print("{} 0\n", cl);
	}
}

ClauseStorage getAllClausesOuter(Sat const &sat)
{
	ClauseStorage r;

	// get inner->outer translation and list removed outer vars
	std::vector<Lit> fixed_lits; // outer vars that are fixed
	std::vector<std::pair<Lit, Lit>> equ_lits;
	auto innerToOuter = std::vector<Lit>(sat.varCount(), Lit::undef());
	for (int i = 0; i < sat.varCountOuter(); ++i)
	{
		Lit a = sat.outerToInner(Lit(i, false));
		if (a == Lit::elim())
			continue;
		assert(a.fixed() || a.proper());
		if (a.fixed())
			fixed_lits.push_back(Lit(i, a.sign()));
		else if (innerToOuter[a.var()] == Lit::undef())
			innerToOuter[a.var()] = Lit(i, a.sign());
		else
			equ_lits.push_back({innerToOuter[a.var()], Lit(i, a.sign())});
	}

	// consistency check
	for (Lit a : innerToOuter)
		assert(a.proper());

	// empty clause
	if (sat.contradiction)
		r.addClause({}, true);

	// unit clauses
	for (Lit a : fixed_lits)
		r.addClause({a}, true);
	for (Lit a : sat.units)
		r.addClause({innerToOuter[a.var()] ^ a.sign()}, true);

	// binary clauses
	for (auto [a, b] : equ_lits)
	{
		r.addClause({a, b.neg()}, true);
		r.addClause({b, a.neg()}, true);
	}
	for (int i = 0; i < sat.varCount() * 2; ++i)
		for (Lit b : sat.bins[i])
		{
			Lit a = Lit(i);
			a = innerToOuter[a.var()] ^ a.sign();
			b = innerToOuter[b.var()] ^ b.sign();
			r.addClause({a, b}, true);
		}

	// long clauses
	for (auto [ci, cl] : sat.clauses)
	{
		util::small_vector<Lit, 16> tmp;
		(void)ci;
		for (Lit a : cl.lits())
			tmp.push_back(innerToOuter[a.var()] ^ a.sign());
		r.addClause({tmp.begin(), tmp.end()}, cl.irred());
	}

	// extension clauses (can be of any size)
	for (auto [ci, cl] : sat.extender.clauses_)
	{
		(void)ci;
		r.addClause(cl.lits(), true);
	}

	return r;
}

int runUnitPropagation(Sat &sat);
int runSCC(Sat &sat);

int cleanup(Sat &sat)
{
	util::StopwatchGuard swg(sat.stats.swCleanup);

	// util::Stopwatch sw;
	// sw.start();

	int totalUP = 0;
	int totalSCC = 0;
	int iter = 0;

	// NOTE: Theoretically, this loop could become quadratic. But in practice,
	// I never saw more than a few iterations, so we dont bother capping it.
	for (;; ++iter)
	{
		if (int nFound = runUnitPropagation(sat); nFound)
			totalUP += nFound;
		if (int nFound = runSCC(sat); nFound)
			totalSCC += nFound;
		else
			break;
	}

	// fmt::print("c [UP/SCC x{:2}   {:#6.2f}] removed {} + {} vars\n", iter,
	//            sw.secs(), totalUP, totalSCC);

	return totalUP + totalSCC;
}

} // namespace dawn
