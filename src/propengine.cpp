#include "propengine.h"
#include <cassert>

PropEngine::PropEngine(ClauseSet& cs)
	: cs(cs), watches(cs.varCount()*2), assign(cs.varCount()*2)
{
	// empty clause -> don't bother doing anything
	if(cs.contradiction)
		return;

	// attach long clauses
	for(auto [i,c] : cs.clauses)
	{
		assert(c.size() >= 2);
		watches[c[0]].push_back(i);
		watches[c[1]].push_back(i);
	}

	// propagate unary clauses
	for(auto l : cs.units)
		if(!propagateFull(l))
		{
			cs.addEmpty();
			return;
		}
}

bool PropEngine::set(Lit x)
{
	if(assign[x])
		return true;
	if(assign[x.neg()])
		return false;
	assign[x] = true;
	trail.push_back(x);
	return true;
}

bool PropEngine::propagateBinary(Lit x)
{
	size_t pos = trail.size();
	if(!set(x))
		return false;

	while(pos != trail.size())
	{
		Lit y = trail[pos++];
		for(Lit z : cs.bins[y.neg()])
			if(!set(z))
				return false;
	}
	return true;
}

bool PropEngine::propagateFull(Lit x)
{
	size_t pos = trail.size();
	if(!propagateBinary(x))
		return false;

	while(pos != trail.size())
	{
		Lit y = trail[pos++];
		std::vector<CRef>& ws = watches[y.neg()];
		for(size_t wi = 0; wi < ws.size(); ++wi)
		{
			Clause& c = cs.clauses[ws[wi]];

			// move y to c[1] (so that c[0] is the potentially propagated one)
			if(c[0] == y.neg())
				std::swap(c[0], c[1]);
			assert(c[1] == y.neg());

			// other watched lit is satisfied -> do nothing
			if(assign[c[0]])
				continue;

			// check the tail of the clause
			for(size_t i = 2; i < c.size(); ++i)
				if(!assign[c[i].neg()]) // literal satisfied or undef -> move watch
				{
					std::swap(c[1], c[i]);
					watches[c[1]].push_back(ws[wi]);

					ws[wi] = ws.back();
					--wi;
					ws.pop_back();
					goto next_watch;
				}

			// tail is all assigned false -> propagate or conflict
			if(!propagateBinary(c[0]))
				return false;

			next_watch:;
		}
	}
	return true;
}

int PropEngine::unassignedVariable() const
{
	for(int i = 0; i < (int)cs.varCount(); ++i)
		if(!assign[Lit(i,false)] && !assign[Lit(i,true)])
			return i;
	return -1;
}

int PropEngine::level() const
{
	return (int)mark.size();
}

void PropEngine::newLevel()
{
	mark.push_back(trail.size());
}

void PropEngine::unrollLevel(int l)
{
	if(l == level())
		return;
	assert(l < level());
	while(trail.size() > mark[l])
	{
		Lit lit = trail.back();
		trail.pop_back();
		assign[lit] = false;
	}
	mark.resize(l);
}
