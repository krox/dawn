#include "sat/clause.h"

#include <cassert>
#include <cstring>

namespace dawn {

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
