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

std::ostream& operator<<(std::ostream& stream, const ClauseStorage& clauses)
{
	for(auto [_ ,c] : clauses)
	{
		for(int j = 0; j < c.size(); ++j)
			stream << c[j].toDimacs() << " ";
		stream << "0\n";
	};
	stream << std::flush;
	return stream;
}
