#include "sat/clause.h"

#include <cassert>
#include <cstring>

using namespace dawn;

bool dawn::is_resolvent_tautological(std::span<const Lit> a,
                                     std::span<const Lit> b)
{
	int count = 0; // number of shared variables with opposite sign

	for (size_t i = 0, j = 0; i < a.size() && j < b.size();)
	{
		if (a[i].var() < b[j].var())
			++i;
		else if (a[i].var() > b[j].var())
			++j;
		else
		{
			if (a[i] == b[j].neg())
				if (++count >= 2)
					return true;
			++i;
			++j;
		}
	}

	assert(count == 1);
	return false;
}

bool dawn::is_resolvent_tautological_unsorted(std::span<const Lit> a,
                                              std::span<const Lit> b)
{
	// NOTE: This is O(n^2). Copying the clauses to temporary storage and
	// sorting would give O(n log n), but my hunch is this is still better in
	// practice. If this becomes a bottleneck, some SIMD should be used.
	int count = 0; // number of shared variables with opposite sign
	for (Lit x : a)
		for (Lit y : b)
		{
			if (x == y.neg())
				if (++count >= 2)
					return true;
		}
	assert(count == 1);
	return false;
}

void dawn::ClauseStorage::prune(util::function_view<bool(Clause const &)> f)
{

	uint32_t pos = 0;

	for (Clause *it = &*begin(), *e = &*end(); it != e;)
	{
		auto next = it->next();
		auto size = it->size();

		if (!f(*it))
		{
			it->shrink_unsafe();
			std::memmove((void *)&store_[pos], (void *)it,
			             size * sizeof(Lit) + sizeof(Clause));
			pos += size + sizeof(Clause) / sizeof(Lit);
		}
		it = next;
	}

	store_.resize(pos);
}

void dawn::ClauseStorage::prune_black()
{
	prune([](Clause const &cl) { return cl.color() == Color::black; });
}

void dawn::ClauseStorage::clear() { store_.resize(0); }

void dawn::ImplCache::add_implied(Lit a) noexcept
{
	assert(a.proper());
	assert(stack_.empty());
	for (Lit b : g_[a.neg()])
		if (seen_.add(b))
			stack_.push_back(b);
	while (!stack_.empty())
		for (Lit b : g_[stack_.pop_back().neg()])
			if (seen_.add(b))
				stack_.push_back(b);
}

// add lits implied by 'a', but not 'a' itself (unless there is a cycle)
void dawn::ImplCache::add(Lit a) noexcept
{
	assert(a.proper());
	assert(stack_.empty());
	if (!seen_.add(a))
		return;
	stack_.push_back(a);
	while (!stack_.empty())
		for (Lit b : g_[stack_.pop_back().neg()])
			if (seen_.add(b))
				stack_.push_back(b);
}

bool dawn::ImplCache::contains(Lit a) const noexcept
{
	assert(a.proper());
	return seen_[a];
}

void dawn::ImplCache::clear() noexcept
{
	stack_.clear();
	seen_.clear();
}

void dawn::ImplCache::normalize(Clause &cl)
{
	clear();
	if (cl.color() == Color::black)
		return;

	for (Lit a : cl)
		add_implied(a.neg());
	bool might_shorten = false;
	for (Lit a : cl)
	{
		if (contains(a))
		{
			cl.set_color(Color::black);
			return;
		}
		if (contains(a.neg()))
			might_shorten = true;
	}

	if (!might_shorten)
		return;

	// If the graph is acyclic, we could have already done the shortening by
	// this point. Cycles destroy that logic so we need the following exact
	// checks. Could still be optimized, but unlikely to be a bottleneck, so we
	// keep the following clean approach (which produces exact results despite
	// arbitrary cycles or failed literals)
	for (int i = 0; i < cl.size(); ++i)
	{
		clear();
		add_implied(cl[i]);
		for (int j = 0; j < cl.size(); ++j)
			if (j != i && contains(cl[j]))
			{
				cl.remove_literal(cl[i]);
				--i;
				break;
			}
	}
}

bool dawn::ImplCache::is_subsumed(std::span<const Lit> cl)
{
	clear();
	for (Lit a : cl)
		add_implied(a.neg());
	for (Lit a : cl)
		if (contains(a))
			return true;
	return false;
}

bool dawn::ImplCache::is_resolvent_tautological(std::span<const Lit> a,
                                                std::span<const Lit> b,
                                                Lit pivot)
{
	clear();
	bool foundA = false, foundB = false;
	for (Lit x : a)
		if (x.var() != pivot.var())
			add(x.neg());
		else
			foundA = true;
	for (Lit x : b)
		if (x.var() != pivot.var())
		{
			if (contains(x))
				return true;
		}
		else
			foundB = true;
	assert(foundA && foundB);
	return false;
}
