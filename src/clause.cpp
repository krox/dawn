#include "clause.h"
#include <iostream>
#include <cassert>

std::ostream& operator<<(std::ostream& stream, Lit l)
{
	if(l.proper())
		stream << l.toDimacs();
	else if(l == LIT_UNDEF)
		stream << "undef";
	else if(l == LIT_ONE)
		stream << "true";
	else if(l == LIT_ZERO)
		stream << "false";
	else if(l == LIT_ELIM)
		stream << "elim";
	else
		assert(false);
	return stream;
}

std::ostream& operator<<(std::ostream& stream, const Clause& cl)
{
	for(int j = 0; j < cl.size(); ++j)
	{
		if(j > 0)
			stream << " ";
		stream << cl[j];
	}
	return stream;
}

std::ostream& operator<<(std::ostream& stream, const ClauseStorage& clauses)
{
	for(auto [_ ,c] : clauses)
		stream << c << " 0\n";
	stream << std::flush;
	return stream;
}
