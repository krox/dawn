#include "clause.h"
#include <iostream>
#include <cassert>

std::ostream& operator<<(std::ostream& stream, Lit l)
{
	if(l.proper())
		stream << l.toDimacs();
	else if(l == undef)
		stream << "undef";
	else if(l == one)
		stream << "true";
	else if(l == zero)
		stream << "false";
	else if(l == elim)
		stream << "elim";
	else
		assert(false);
	return stream;
}

std::ostream& operator<<(std::ostream& stream, const ClauseStorage& clauses)
{
	for(auto i : clauses.clauses)
	{
		for(int j = 0; j < clauses[i].size(); ++j)
			stream << clauses[i].lits[j].toDimacs() << " ";
		stream << "0\n";
	}
	stream << std::flush;
	return stream;
}
