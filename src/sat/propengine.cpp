#include "sat/propengine.h"

#include <cassert>
#include <iostream>
#include <queue>

PropEngine::PropEngine(Sat &sat)
    : sat(sat), watches(sat.varCount() * 2), reason(sat.varCount()),
      trailPos(sat.varCount()), activityHeap(sat), assign(sat.varCount() * 2)
{
	// empty clause -> don't bother doing anything
	if (sat.contradiction)
	{
		conflict = true;
		return;
	}

	// attach long clauses
	for (auto [i, c] : sat.clauses)
	{
		assert(c.size() >= 2);
		watches[c[0]].push_back(i);
		watches[c[1]].push_back(i);
	}

	// propagate unary clauses
	for (auto l : sat.units)
	{
		if (assign[l])
			continue;
		if (assign[l.neg()])
		{
			conflict = true;
			return;
		}
		propagateFull(l, Reason::undef());
		if (conflict)
			return;
	}

	// add everything to the activity-activity heap
	for (int i = 0; i < sat.varCount(); ++i)
		activityHeap.push(i);
}

void PropEngine::set(Lit x, Reason r)
{
	assert(!conflict);
	assert(!assign[x] && !assign[x.neg()]);
	assign[x] = true;
	reason[x.var()] = r;
	trailPos[x.var()] = (int)trail.size();
	trail.push_back(x);
}

void PropEngine::propagateBinary(Lit x, Reason r)
{
	size_t pos = trail.size();
	set(x, r);

	while (pos != trail.size())
	{
		Lit y = trail[pos++];
		for (Lit z : sat.bins[y.neg()])
		{
			if (assign[z]) // already assigned true -> do nothing
				continue;

			if (assign[z.neg()]) // already assigned false -> conflict
			{
				assert(conflictClause.empty());
				conflictClause.push_back(y.neg());
				conflictClause.push_back(z);
				conflict = true;
				return;
			}

			set(z, Reason(y.neg())); // else -> propagate
		}
	}
}

void PropEngine::propagateFull(Lit x, Reason r)
{
	size_t pos = trail.size();
	propagateBinary(x, r);
	if (conflict)
		return;

	while (pos != trail.size())
	{
		Lit y = trail[pos++];
		auto &ws = watches[y.neg()];
		for (size_t wi = 0; wi < ws.size(); ++wi)
		{
			CRef ci = ws[wi];
			Clause &c = sat.clauses[ci];

			// move y to c[1] (so that c[0] is the potentially propagated one)
			if (c[0] == y.neg())
				std::swap(c[0], c[1]);
			assert(c[1] == y.neg());

			// other watched lit is satisfied -> do nothing
			if (assign[c[0]])
				continue;

			// check the tail of the clause
			for (size_t i = 2; i < c.size(); ++i)
				if (!assign[c[i].neg()]) // literal satisfied or undef -> move
				                         // watch
				{
					std::swap(c[1], c[i]);
					watches[c[1]].push_back(ws[wi]);

					ws[wi] = ws.back();
					--wi;
					ws.pop_back();
					goto next_watch;
				}

			// tail is all assigned false -> propagate or conflict
			if (assign[c[0].neg()])
			{
				conflict = true;
				assert(conflictClause.empty());
				for (Lit l : c.lits())
					conflictClause.push_back(l);
				return;
			}
			else
			{
				propagateBinary(c[0], Reason(ci));
				if (conflict)
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
	propagateFull(x, Reason::undef());

	if (conflict)
	{
		unroll(level() - 1);
		return -1;
	}
	else
	{
		int r = (int)(trail.size() - pos);
		unroll(level() - 1);
		return r;
	}
}

int PropEngine::probeFull()
{
	int best = -1;
	int bestScore = -1;
	for (int i = 0; i < sat.varCount(); ++i)
	{
		Lit a = Lit(i, false);
		Lit b = Lit(i, true);
		if (assign[a] || assign[b])
			continue;

		int scoreA = probe(a);
		int scoreB = probe(b);

		if (scoreA == -1 && scoreB == -1)
			return -2;
		else if (scoreA == -1)
			propagateFull(b, Reason::undef());
		else if (scoreB == -1)
			propagateFull(a, Reason::undef());
		else if (scoreA + scoreB > bestScore)
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
	propagateFull(x, Reason::undef());
}

Reason PropEngine::addClause(const std::vector<Lit> &cl)
{
	switch (cl.size())
	{
	case 0:
		sat.addEmpty();
		conflict = true;
		return Reason::undef();
	case 1:
		sat.addUnary(cl[0]);
		return Reason::undef();
	case 2:
		sat.addBinary(cl[0], cl[1]);
		return Reason(cl[1]);
	default:
		CRef cref = sat.addLong(cl);
		watches[cl[0]].push_back(cref);
		watches[cl[1]].push_back(cref);
		return Reason(cref);
	}
}

int PropEngine::unassignedVariable() const
{
	for (int i = 0; i < sat.varCount(); ++i)
		if (!assign[Lit(i, false)] && !assign[Lit(i, true)])
			return i;
	return -1;
}

int PropEngine::mostActiveVariable()
{
	while (!activityHeap.empty())
	{
		int v = activityHeap.pop();
		if (assign[Lit(v, false)] || assign[Lit(v, true)])
			continue;

		// check the heap(very expensive, debug only)
		// for (int i = 0; i < sat.varCount(); ++i)
		//	assert(assign[Lit(i, false)] || assign[Lit(i, true)] ||
		//	       sat.activity[i] <= sat.activity[v]);

		return v;
	}
	return -1;
}

int PropEngine::level() const { return (int)mark.size(); }

void PropEngine::unroll(int l)
{
	assert(l < level());
	conflict = false;
	conflictClause.resize(0);

	while ((int)trail.size() > mark[l])
	{
		Lit lit = trail.back();
		trail.pop_back();
		// assert(assign[lit] && !assign[lit.neg()]);
		// reason[lit.var()] = Reason::undef();
		// trailPos[lit.var()] = -1;
		assign[lit] = false;
		activityHeap.push(lit.var());
	}
	mark.resize(l);
}

/** returns level to which to backtrack */
int PropEngine::analyzeConflict(std::vector<Lit> &learnt)
{
	assert(learnt.empty());
	assert(conflict);
	assert(!conflictClause.empty());
	assert(level() > 0);

	std::priority_queue<std::pair<int, Lit>> todo;

	for (Lit l : conflictClause)
	{
		// assert(assign[l.neg()]);
		todo.emplace(trailPos[l.var()], l);
	}

	while (!todo.empty())
	{
		// next literal
		Lit l = todo.top().second;
		todo.pop();
		// assert(assign[l.neg()]);

		// remove duplicates from queue
		while (!todo.empty() && todo.top().second == l)
			todo.pop();

		sat.bumpVariableActivity(l.var());
		activityHeap.update(l.var());

		// next one is reason side
		//   -> this one is reason side or UIP
		//   -> add this one to learnt clause
		if (todo.empty() || todo.top().first < mark.back())
		{
			if (trailPos[l.var()] >= mark[0]) // skip level 0 assignments
				learnt.push_back(l);
		}
		else // otherwise resolve
		{
			Reason r = reason[l.var()];
			if (r.isBinary())
			{
				todo.emplace(trailPos[r.lit().var()], r.lit());
			}
			else if (r.isLong())
			{
				const Clause &cl = sat.clauses[r.cref()];
				// assert(cl[0] == l.neg());
				for (int i = 1; i < cl.size(); ++i)
					todo.emplace(trailPos[cl[i].var()], cl[i]);
			}
			else
				assert(false);
		}
	}

	sat.decayVariableActivity();

	// determine backtrack level
	assert(!learnt.empty());
	if (learnt.size() == 1)
		return 0;
	int i = level() - 1;
	while (mark[i] > trailPos[learnt[1].var()])
		i -= 1;
	return i + 1;
}

void PropEngine::printTrail() const
{
	for (int l = 0; l <= level(); ++l)
	{
		std::cout << "=== level " << l << " ===" << std::endl;
		int low = l == 0 ? 0 : mark[l - 1];
		int high = l == (int)mark.size() ? (int)trail.size() : mark[l];
		for (int i = low; i < high; ++i)
		{
			std::cout << trail[i] << " <= ";
			Reason r = reason[trail[i].var()];
			if (r == Reason::undef())
				std::cout << "()" << std::endl;
			else if (r.isBinary())
				std::cout << "bin (" << r.lit() << ")" << std::endl;
			else if (r.isLong())
				std::cout << "long (" << sat.clauses[r.cref()] << ")"
				          << std::endl;
			else
				assert(false);
		}
	}
}
