#include "sat/sat.h"

#include "fmt/format.h"
#include "fmt/os.h"
#include "sat/binary.h"
#include <algorithm>
#include <cassert>
#include <random>

namespace dawn {

void Sat::renumber(std::span<const Lit> trans, int newVarCount)
{
	// checks input and renumbers actual clauses
	Cnf::renumber(trans, newVarCount);

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
		{
		}
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
	size_t r = Cnf::memory_usage();
	r += to_outer_.capacity() * sizeof(Lit);
	r += extender.memory_usage();
	return r;
}

void shuffleVariables(Sat &sat)
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

int runUnitPropagation(Sat &sat);

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
		if (int nFound = run_scc(sat); nFound)
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
	if (sat.contradiction && sat.var_count() != 0)
		return false;
	if (!sat.units.empty())
		return false;
	if (auto top = TopOrder(sat); !top.valid)
		return false;
	return true;
}

} // namespace dawn
