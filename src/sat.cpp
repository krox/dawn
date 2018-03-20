#include "sat.h"
#include <iostream>
#include <cassert>
#include <algorithm>

void Sat::cleanup()
{
	// empty clause -> remove everything
	if(contradiction)
	{
		units.resize(0);
		for(uint32_t i = 0; i < 2*varCount(); ++i)
			bins[i].resize(0);
		for(auto [ci,cl] : clauses)
			cl.remove();
		return;
	}

	// get assignment
	std::vector<bool> assign(varCount()*2, false);
	for(Lit u : units)
	{
		assert(!assign[u.neg()]);
		assign[u] = true;
	}

	// remove assigned variables from long clauses
	for(auto [ci,cl] : clauses)
	{
		for(int i = 0; i < cl.size(); ++i)
		{
			if(assign[cl[i]])
			{
				cl.remove();
				break;
			}
			if(assign[cl[i].neg()])
			{
				cl[i] = cl[cl.size()-1];
				cl._size -= 1;
				--i;
			}
		}

		if(cl.isRemoved() || cl.size() > 2)
			continue;

		if(cl.size() == 0)
			assert(false);
		else if(cl.size() == 1)
			assert(assign[cl[0]]);
		else if(cl.size() == 2)
			addBinary(cl[0],cl[1]);
		else assert(false);

		cl.remove();
	}
	//clauses.compactify(); // TODO

	// remove assigned variables from binary clauses
	for(uint32_t i = 0; i < 2*varCount(); ++i)
	{
		Lit a(i);

		if(assign[a]) // (x or 1)
		{
			bins[a].resize(0);
		}
		else if(assign[a.neg()]) // (x or 0)
		{
			for(Lit b : bins[a])
				assert(assign[b]);
			bins[a].resize(0);
		}
		else
		{
			std::sort(bins[a].begin(), bins[a].end());
			bins[a].erase(std::unique(bins[a].begin(), bins[a].end()), bins[a].end());
		}
	}

	std::sort(units.begin(), units.end());
	units.erase(std::unique(units.begin(), units.end()), units.end());
}

std::ostream& operator<<(std::ostream& stream, const Sat& sat)
{
	// empty clause
	if(sat.contradiction)
		stream << "0\n";

	// unary clauses
	for(auto a : sat.units)
		stream << a << " 0\n";

	// binary clauses
	for(uint32_t l = 0; l < 2*sat.varCount(); ++l)
		for(auto b : sat.bins[l])
			if(l <= b)
				stream << Lit(l) << " " << b << " 0\n";

	// long clauses
	stream << sat.clauses;

	return stream;
}
