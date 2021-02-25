#include "sat/clause.h"

#include <cassert>
#include <cstring>
#include <iostream>

namespace dawn {

std::ostream &operator<<(std::ostream &stream, Lit l)
{
	if (l.proper())
		stream << l.toDimacs();
	else if (l == Lit::undef())
		stream << "undef";
	else if (l == Lit::one())
		stream << "true";
	else if (l == Lit::zero())
		stream << "false";
	else if (l == Lit::elim())
		stream << "elim";
	else if (l == Lit::elim().neg())
		stream << "-elim"; // should never exist, just for debugging
	else if (l == Lit::undef().neg())
		stream << "-undef"; // ditto
	else
		assert(false);
	return stream;
}

std::ostream &operator<<(std::ostream &stream, const Clause &cl)
{
	for (int j = 0; j < cl.size(); ++j)
	{
		if (j > 0)
			stream << " ";
		stream << cl[j];
	}
	return stream;
}

std::ostream &operator<<(std::ostream &stream, const ClauseStorage &clauses)
{
	for (auto [_, c] : clauses)
	{
		(void)_;
		stream << c << " 0\n";
	}
	stream << std::flush;
	return stream;
}

void ClauseStorage::compactify()
{
	size_t ii = 0;
	uint32_t pos = 0;
	for (size_t i = 0; i < clauses.size(); ++i)
	{
		Clause &cl = (*this)[clauses[i]];
		if (cl.isRemoved())
			continue;

		auto size = cl.size();

		// NOTE: the memmove() might invalidate cl
		std::memmove(&store[pos], &cl, size * sizeof(Lit) + sizeof(Clause));
		clauses[ii++] = CRef(pos);
		pos += size + sizeof(Clause) / sizeof(Lit);
	}

	clauses.resize(ii);
	store.resize(pos);
}

void ClauseStorage::clear()
{
	clauses.resize(0);
	store.resize(0);
}

} // namespace dawn
