#include "sat/reconstruction.h"

#include <cassert>

using namespace dawn;

Lit dawn::Reconstruction::to_outer(Lit a)
{
	assert(a.proper());
	assert(a.var() < (1 << 27)); // sanity check, arbitrary limit

	while (a.var() >= (int)to_outer_.size())
		to_outer_.push_back(Lit(outer_var_count_++, false));
	assert(to_outer_[a.var()].proper());
	assert(to_outer_[a.var()].var() < outer_var_count_);
	return to_outer_[a.var()] ^ a.sign();
}

dawn::Reconstruction::Reconstruction(int n) noexcept
    : outer_var_count_(n), orig_var_count_(n), to_outer_(n)
{
	for (int i = 0; i < n; ++i)
		to_outer_[i] = Lit(i, false);
}

void dawn::Reconstruction::add_rule(std::span<const Lit> cl)
{
	assert(cl.size() >= 1);
	CRef i = rules_.add_clause(cl, Color::blue);
	for (Lit &a : rules_[i])
		a = to_outer(a);
}

void dawn::Reconstruction::add_rule(std::span<const Lit> cl, Lit pivot)
{
	assert(cl.size() >= 1);
	CRef i = rules_.add_clause(cl, Color::blue);
	for (Lit &a : rules_[i])
	{
		if (a == pivot)
		{
			a = to_outer(a);
			std::swap(a, rules_[i][0]);
		}
		else
			a = to_outer(a);
	}
}

void dawn::Reconstruction::add_unit(Lit a) { add_rule({{a}}); }

void dawn::Reconstruction::add_equivalence(Lit a, Lit b)
{
	assert(a.var() != b.var());
	add_rule({{a, b.neg()}});
	add_rule({{a.neg(), b}});
}

void Reconstruction::renumber(std::span<const Lit> trans, int newVarCount)
{
	assert(trans.size() >= to_outer_.size());

	auto to_outer_new_ = std::vector<Lit>(newVarCount, Lit::undef());
	for (int i = 0; i < (int)trans.size(); ++i)
	{
		if (trans[i] == Lit::elim())
			continue;

		if (trans[i].fixed())
		{
			add_unit(Lit(i, trans[i].sign()));
			continue;
		}

		assert(trans[i].proper() && trans[i].var() < newVarCount);

		if (to_outer_new_[trans[i].var()] == Lit::undef())
			to_outer_new_[trans[i].var()] = to_outer(Lit(i, trans[i].sign()));
		else
		{
			Lit a = to_outer(Lit(i, trans[i].sign()));
			Lit b = to_outer_new_[trans[i].var()];
			rules_.add_binary(a, b.neg());
			rules_.add_binary(a.neg(), b);
		}
	}
	for (Lit a : to_outer_new_)
		assert(a.proper());
	to_outer_ = std::move(to_outer_new_);
}

Assignment dawn::Reconstruction::operator()(Assignment const &a) const
{
	assert(a.var_count() >= (int)to_outer_.size());

	auto r = Assignment(outer_var_count_);
	for (int i = 0; i < (int)to_outer_.size() * 2; ++i)
		if (Lit x = Lit(i); a[x])
			r.set(to_outer_[x.var()] ^ x.sign());
	r.fix_unassigned();

	std::vector<CRef> crefs;
	for (CRef i : rules_.crefs())
		crefs.push_back(i);
	for (CRef i : std::views::reverse(crefs))
		if (!r.satisfied(rules_[i]))
			r.force_set(rules_[i][0]);
	return r;
}

size_t Reconstruction::memory_usage() const
{
	return rules_.memory_usage() + sizeof(Lit) * to_outer_.capacity();
}
