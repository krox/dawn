#include "sat/clause.h"

#include <cassert>
#include <iostream>

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
		stream << c << " 0\n";
	stream << std::flush;
	return stream;
}
