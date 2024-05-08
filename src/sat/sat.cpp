#include "sat/sat.h"

#include "fmt/format.h"
#include "fmt/os.h"
#include "sat/binary.h"
#include "sat/probing.h"
#include "sat/propengine.h"
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

Assignment Sat::to_outer(Assignment const &a) const
{
	assert(a.var_count() == var_count());
	auto r = Assignment(var_count_outer());
	for (int i = 0; i < var_count(); ++i)
	{
		if (a(i) == ltrue)
			r.set(to_outer_[i]);
		else if (a(i) == lfalse)
			r.set(to_outer_[i].neg());
	}
	return r;
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

namespace {

int runUnitPropagation(Sat &sat)
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

void cleanup(Sat &sat)
{
	util::StopwatchGuard swg(sat.stats.swCleanup);
	auto log = Logger("cleanup");

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
	log.info("now at {} vars, {} bins, {} irred, {} learnt", sat.var_count(),
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

} // namespace dawn
