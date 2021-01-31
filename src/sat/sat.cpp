#include "sat/sat.h"

#include <algorithm>
#include <cassert>
#include <fmt/format.h>
#include <fmt/os.h>
#include <iostream>
#include <random>

void Sat::cleanup()
{
	StopwatchGuard swg(stats.swCleanup);

	// empty clause -> remove everything
	if (contradiction)
	{
		units.resize(0);
		for (int i = 0; i < 2 * varCount(); ++i)
			bins[i].resize(0);
		for (auto [ci, cl] : clauses)
		{
			(void)ci;
			cl.remove();
		}
		return;
	}

	// if there are units -> renumber
	if (!units.empty())
	{
		auto trans = std::vector<Lit>(varCount(), Lit::undef());
		for (Lit u : units)
		{
			assert(trans[u.var()] != Lit::fixed(u.sign()).neg());
			trans[u.var()] = Lit::fixed(u.sign());
		}
		int newVarCount = 0;
		for (int i = 0; i < varCount(); ++i)
		{
			if (trans[i] == Lit::undef())
				trans[i] = Lit(newVarCount++, false);
		}
		renumber(trans, newVarCount);
	}

	// remove duplicate unary clauses
	std::sort(units.begin(), units.end());
	units.erase(std::unique(units.begin(), units.end()), units.end());

	// remove duplicate binary clauses
	for (int i = 0; i < 2 * varCount(); ++i)
	{
		auto &v = bins[Lit(i)];
		std::sort(v.begin(), v.end());
		v.erase(std::unique(v.begin(), v.end()), v.end());
	}
}

void Sat::renumber(span<const Lit> trans, int newVarCount)
{
	// check input
	assert(trans.size() == (size_t)varCount());
	for (Lit l : trans)
		if (!l.fixed())
		{
			assert(l.proper());
			assert(l.var() < newVarCount);
		}

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
			else
				addUnary(a);
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

				// tautologies -> remove clause
				if (c == Lit::one() || d == Lit::one() || c == d.neg())
					continue;

				// false false clause -> add
				else if (c == Lit::zero() && d == Lit::zero())
					addEmpty();

				// unit claus
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
		std::vector<bool> polarityOld(newVarCount, false);
		std::swap(polarity, polarityOld);
		for (int i = 0; i < (int)polarityOld.size(); ++i)
			if (trans[i].proper())
			{
				int j = trans[i].var();
				polarity[j] = polarityOld[i] ^ trans[i].sign();
			}
	}

	// renumber translation array
	for (int i = 0; i < (int)varCountOuter(); ++i)
		if (outerToInner_[i].proper())
			outerToInner_[i] =
			    trans[outerToInner_[i].var()] ^ outerToInner_[i].sign();

	// compactify storage of long clauses
	clauses.compactify();
}

std::ostream &operator<<(std::ostream &stream, const Sat &sat)
{
	// empty clause
	if (sat.contradiction)
		stream << "0\n";

	// unary clauses
	for (auto a : sat.units)
		stream << a << " 0\n";

	// binary clauses
	for (int l = 0; l < 2 * sat.varCount(); ++l)
		for (auto b : sat.bins[l])
			if (l <= b)
				stream << Lit(l) << " " << b << " 0\n";

	// long clauses
	stream << sat.clauses;

	return stream;
}

void shuffleVariables(Sat &sat)
{
	auto trans = std::vector<Lit>(sat.varCount());
	for (int i = 0; i < sat.varCount(); ++i)
	{
		trans[i] = Lit(i, std::bernoulli_distribution(0.5)(sat.stats.rng));
		int j = std::uniform_int_distribution<int>(0, i)(sat.stats.rng);
		std::swap(trans[i], trans[j]);
	}
	sat.renumber(trans, sat.varCount());
}

void dumpOuter(std::string const &filename, Sat const &sat)
{
	// get inner->outer translation and list removed outer vars
	std::vector<Lit> fixed_lits; // outer vars that are fixed
	std::vector<std::pair<Lit, Lit>> equ_lits;
	auto innerToOuter = std::vector<Lit>(sat.varCount(), Lit::undef());
	for (int i = 0; i < sat.varCountOuter(); ++i)
	{
		Lit a = sat.outerToInner(Lit(i, false));
		assert(a.fixed() || a.proper());
		if (a.fixed())
			fixed_lits.push_back(Lit(i, a.sign()));
		else if (innerToOuter[a.var()] == Lit::undef())
			innerToOuter[a.var()] = Lit(i, a.sign());
		else
			equ_lits.push_back({innerToOuter[a.var()], Lit(i, a.sign())});
	}

	auto file = fmt::output_file(filename);
	file.print("p cnf {} {}\n", sat.varCountOuter(),
	           sat.clauseCount() + fixed_lits.size() + 2 * equ_lits.size());

	// consistency check
	for (Lit a : innerToOuter)
		assert(a.proper());

	// write empty clause
	if (sat.contradiction)
		file.print("0\n");

	// write unit clauses
	for (Lit a : fixed_lits)
		file.print("{} 0\n", a.toDimacs());
	for (Lit a : sat.units)
		file.print("{} 0\n", (innerToOuter[a.var()] ^ a.sign()).toDimacs());

	// write binary clauses
	for (auto [a, b] : equ_lits)
	{
		file.print("{} {} 0\n", a.toDimacs(), b.neg().toDimacs());
		file.print("{} {} 0\n", b.toDimacs(), a.neg().toDimacs());
	}
	for (int i = 0; i < sat.varCount() * 2; ++i)
		for (Lit b : sat.bins[i])
		{
			Lit a = Lit(i);
			a = innerToOuter[a.var()] ^ a.sign();
			b = innerToOuter[b.var()] ^ b.sign();
			file.print("{} {}\n", a.toDimacs(), b.toDimacs());
		}

	// write long clauses
	for (auto [ci, cl] : sat.clauses)
	{
		(void)ci;
		for (Lit a : cl.lits())
			file.print("{} ", (innerToOuter[a.var()] ^ a.sign()).toDimacs());
		file.print("0\n");
	}
}
