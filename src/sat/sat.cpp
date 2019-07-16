#include "sat/sat.h"

#include <algorithm>
#include <cassert>
#include <fmt/format.h>
#include <iostream>

void Sat::cleanup()
{
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

	// compactify storage of long clauses
	// clauses.compactify(); // TODO
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
		std::vector<std::vector<Lit>> binsOld(newVarCount * 2);
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

	// renumber translation array
	for (int i = 0; i < (int)varCountOuter(); ++i)
		if (outerToInner_[i].proper())
			outerToInner_[i] =
			    trans[outerToInner_[i].var()] ^ outerToInner_[i].sign();
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
