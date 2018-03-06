#include "propengine.h"
#include <cassert>

PropEngine::PropEngine(ClauseSet& cs)
	: cs(cs), watches(cs.varCount()*2), assign(cs.varCount()*2)
{
	// empty clause -> don't bother doing anything
	if(cs.contradiction)
	{
		conflict = true;
		return;
	}

	// attach long clauses
	for(auto [i,c] : cs.clauses)
	{
		assert(c.size() >= 2);
		watches[c[0]].push_back(i);
		watches[c[1]].push_back(i);
	}

	// propagate unary clauses
	for(auto l : cs.units)
	{
		propagateFull(l);
		if(conflict)
			return;
	}
}

void PropEngine::set(Lit x)
{
	assert(!conflict);
	assert(!assign[x] && !assign[x.neg()]);
	assign[x] = true;
	trail.push_back(x);
}

void PropEngine::propagateBinary(Lit x)
{
	size_t pos = trail.size();
	set(x);

	while(pos != trail.size())
	{
		Lit y = trail[pos++];
		for(Lit z : cs.bins[y.neg()])
		{
			if(assign[z]) // already assigned true -> do nothing
				continue;

			if(assign[z.neg()]) // already assigned false -> conflict
			{
				conflict = true;
				return;
			}

			set(z); // else -> propagate
		}
	}
}

void PropEngine::propagateFull(Lit x)
{
	size_t pos = trail.size();
	propagateBinary(x);
	if(conflict)
		return;

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
			if(assign[c[0].neg()])
			{
				conflict = true;
				return;
			}
			else
			{
				propagateBinary(c[0]);
				if(conflict)
					return;
			}

			next_watch:;
		}
	}
}

int PropEngine::probe(Lit x)
{
	size_t pos = trail.size();
	mark.push_back(trail.size());
	propagateFull(x);

	if(conflict)
	{
		unroll(level()-1);
		return -1;
	}
	else
	{
		int r = (int)(trail.size()-pos);
		unroll(level()-1);
		return r;
	}
}

int PropEngine::probeFull()
{
	int best = -1;
	int bestScore = -1;
	for(int i = 0; i < (int)cs.varCount(); ++i)
	{
		Lit a = Lit(i,false);
		Lit b = Lit(i,true);
		if(assign[a] || assign[b])
			continue;

		int scoreA = probe(a);
		int scoreB = probe(b);

		if(scoreA == -1 && scoreB == -1)
			return -2;
		else if(scoreA == -1)
			propagateFull(b);
		else if(scoreB == -1)
			propagateFull(a);
		else if(scoreA + scoreB > bestScore)
		{
			best = i;
			bestScore = scoreA + scoreB;
		}
		assert(!conflict);
	}
	return best;
}

void PropEngine::branch(Lit x)
{
	assert(!conflict);
	assert(!assign[x] && !assign[x.neg()]);
	mark.push_back(trail.size());
	propagateFull(x);
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


void PropEngine::unroll(int l)
{
	assert(l < level());
	conflict = false;
	while(trail.size() > mark[l])
	{
		Lit lit = trail.back();
		trail.pop_back();
		assign[lit] = false;
	}
	mark.resize(l);
}
