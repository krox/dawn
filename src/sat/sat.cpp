#include "sat/sat.h"

#include "fmt/format.h"
#include "fmt/os.h"
#include "sat/binary.h"
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
		auto units_old = std::move(units);
		units.clear();
		for (Lit a : units_old)
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
	for (auto &cl : clauses.all())
	{
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
	auto to_outer_old = std::move(to_outer_);
	to_outer_ = std::vector<Lit>(newVarCount, Lit::undef());
	for (int i = 0; i < (int)trans.size(); ++i)
	{
		if (trans[i].fixed())
		{
			extender.set_literal(to_outer_old[i] ^ trans[i].sign());
		}
		else if (trans[i] == Lit::elim())
		{}
		else if (trans[i].proper())
		{
			if (to_outer_[trans[i].var()] == Lit::undef())
				to_outer_[trans[i].var()] = to_outer_old[i] ^ trans[i].sign();
			else
				// equivalence. just push the information to the extender
				extender.set_equivalence(to_outer_old[i] ^ trans[i].sign(),
				                         to_outer_[trans[i].var()]);
		}
		else
			assert(false);
	}
	for (Lit a : to_outer_)
		assert(a.proper());
}

size_t Sat::memory_usage() const
{
	size_t r = 0;
	r += to_outer_.capacity() * sizeof(Lit);
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

bool is_normal_form(Sat const &sat)
{
	if (sat.contradiction)
		return false;
	if (!sat.units.empty())
		return false;
	if (auto top = TopOrder(sat); !top.valid())
		return false;
	return true;
}

} // namespace dawn
