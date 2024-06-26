#include "sat/clause.h"

#include <cassert>
#include <cstring>

namespace dawn {

void ClauseStorage::prune(util::function_view<bool(Clause const &)> f)
{
	size_t ii = 0;
	uint32_t pos = 0;
	for (size_t i = 0; i < clauses_.size(); ++i)
	{
		Clause &cl = (*this)[clauses_[i]];
		if (f(cl))
			continue;

		auto size = cl.size();

		// NOTE: the memmove() might invalidate cl
		std::memmove((void *)&store_[pos], (void *)&cl,
		             size * sizeof(Lit) + sizeof(Clause));
		clauses_[ii++] = CRef(pos);
		pos += size + sizeof(Clause) / sizeof(Lit);
	}

	clauses_.resize(ii);
	store_.resize(pos);
}

void ClauseStorage::prune_black()
{
	prune([](Clause const &cl) { return cl.color == Color::black; });
}

void ClauseStorage::clear()
{
	store_.resize(0);
	clauses_.resize(0);
}

} // namespace dawn
