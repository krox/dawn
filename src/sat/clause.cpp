#include "sat/clause.h"

#include <cassert>
#include <cstring>

namespace dawn {

bool is_resolvent_tautological(std::span<const Lit> a, std::span<const Lit> b)
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

bool is_resolvent_tautological_unsorted(std::span<const Lit> a,
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

void ClauseStorage::prune(util::function_view<bool(Clause const &)> f)
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

void ClauseStorage::prune_black()
{
	prune([](Clause const &cl) { return cl.color() == Color::black; });
}

void ClauseStorage::clear() { store_.resize(0); }

} // namespace dawn
