#include "sat/clause.h"

#include <cassert>
#include <cstring>

namespace dawn {

void ClauseStorage::compactify()
{
	size_t ii = 0;
	uint32_t pos = 0;
	for (size_t i = 0; i < clauses_.size(); ++i)
	{
		Clause &cl = (*this)[clauses_[i]];
		if (cl.isRemoved())
			continue;

		auto size = cl.size();

		// NOTE: the memmove() might invalidate cl
		std::memmove(&store[pos], &cl, size * sizeof(Lit) + sizeof(Clause));
		clauses_[ii++] = CRef(pos);
		pos += size + sizeof(Clause) / sizeof(Lit);
	}

	clauses_.resize(ii);
	store.resize(pos);
}

void ClauseStorage::clear()
{
	clauses_.resize(0);
	store.resize(0);
}

} // namespace dawn
