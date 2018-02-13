#include <iostream>
#include "sat.h"

std::ostream& operator<<(std::ostream& stream, const ClauseSet& cs)
{
	// empty clause
	if(cs.contradiction)
		stream << "0\n";

	// unary clauses
	for(auto a : cs.units)
		stream << a << " 0\n";

	// binary clauses
	for(uint32_t l = 0; l < 2*cs.varCount(); ++l)
		for(auto b : cs.bins[l])
			if(l <= b.toInt())
				stream << Lit(l) << " " << b << " 0\n";

	// long clauses
	stream << cs.clauses;

	return stream;
}
