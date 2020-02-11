#include "sat/propengine.h"

#include "fmt/format.h"
#include <cassert>
#include <iostream>
#include <queue>

PropEngine::PropEngine(Sat &sat)
    : sat(sat), seen(sat.varCount()), watches(sat.varCount() * 2),
      reason(sat.varCount()), binDom(sat.varCount()), trailPos(sat.varCount()),
      assign(sat.varCount() * 2)
{
	StopwatchGuard swg(sat.stats.swSearchInit);

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
}

void PropEngine::set(Lit x, Reason r)
{
	assert(!conflict);
	assert(!assign[x] && !assign[x.neg()]);
	assign[x] = true;
	reason[x.var()] = r;
	if (r.isBinary())
		binDom[x.var()] = binDom[r.lit().var()];
	else
		binDom[x.var()] = x;
	trailPos[x.var()] = (int)trail_.size();
	trail_.push_back(x);
}

void PropEngine::propagateBinary(Lit x, Reason r)
{
	size_t pos = trail_.size();
	set(x, r);

	while (pos != trail_.size())
	{
		Lit y = trail_[pos++];
		sat.stats.binHistogram.add((int)sat.bins[y.neg()].size());
		for (Lit z : sat.bins[y.neg()])
		{
			if (assign[z]) // already assigned true -> do nothing
			{
				sat.stats.nBinSatisfied += 1;
				continue;
			}

			if (assign[z.neg()]) // already assigned false -> conflict
			{
				sat.stats.nBinConfls += 1;
				assert(conflictClause.empty());
				conflictClause.push_back(y.neg());
				conflictClause.push_back(z);
				conflict = true;
				return;
			}

			sat.stats.nBinProps += 1;
			set(z, Reason(y.neg())); // else -> propagate
		}
	}
}

void PropEngine::propagateFull(Lit x, Reason r)
{
	size_t pos = trail_.size();
	propagateBinary(x, r);
	if (conflict)
		return;

	while (pos != trail_.size())
	{
		Lit y = trail_[pos++];
		auto &ws = watches[y.neg()];
		sat.stats.watchHistogram.add((int)ws.size());
		for (size_t wi = 0; wi < ws.size(); ++wi)
		{
			CRef ci = ws[wi];
			Clause &c = sat.clauses[ci];
			sat.stats.clauseSizeHistogram.add((int)c.size());

			// move y to c[1] (so that c[0] is the potentially propagated one)
			if (c[0] == y.neg())
				std::swap(c[0], c[1]);
			assert(c[1] == y.neg());

			// other watched lit is satisfied -> do nothing
			if (assign[c[0]])
			{
				sat.stats.nLongSatisfied += 1;
				continue;
			}

			// check the tail of the clause
			for (size_t i = 2; i < c.size(); ++i)
				if (!assign[c[i].neg()]) // literal satisfied or undef -> move
				                         // watch
				{
					sat.stats.nLongShifts += 1;
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
				sat.stats.nLongConfls += 1;
				conflict = true;
				assert(conflictClause.empty());
				for (Lit l : c.lits())
					conflictClause.push_back(l);
				return;
			}
			else
			{
				sat.stats.nLongProps += 1;
				Reason r2 = Reason(ci);

				// lazy hyper-binary resolution
				if (sat.stats.lhbr)
					if (Lit dom = analyzeBin(c.lits().subspan(1, c.size()));
					    dom != Lit::undef())
					{
						sat.stats.nLhbr += 1;

						// learn new binary clause and use it
						assert(assign[dom.neg()]);
						r2 = addLearntClause(c[0], dom);
					}

				propagateBinary(c[0], r2);
				if (conflict)
					return;
			}

		next_watch:;
		}
	}
}

void PropEngine::branch(Lit x)
{
	assert(!conflict);
	assert(!assign[x] && !assign[x.neg()]);
	mark_.push_back(trail_.size());
	propagateFull(x, Reason::undef());
}

Reason PropEngine::addLearntClause(Lit c0, Lit c1)
{
	assert(c0.var() != c1.var());
	sat.addBinary(c0, c1);
	return Reason(c1);
}

Reason PropEngine::addLearntClause(const std::vector<Lit> &cl, uint8_t glue)
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
		CRef cref = sat.addLong(cl, false);
		watches[cl[0]].push_back(cref);
		watches[cl[1]].push_back(cref);
		assert(2 <= glue && glue <= cl.size());
		sat.clauses[cref].glue = glue;
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

int PropEngine::level() const { return (int)mark_.size(); }

void PropEngine::unroll(int l)
{
	assert(l < level());
	conflict = false;
	conflictClause.resize(0);

	while ((int)trail_.size() > mark_[l])
	{
		Lit lit = trail_.back();
		trail_.pop_back();
		assign[lit] = false;
	}
	mark_.resize(l);
}

void PropEngine::unroll_and_activate(int l, ActivityHeap &activityHeap)
{
	assert(l < level());
	for (int i = mark_[l]; i < (int)trail_.size(); ++i)
		activityHeap.push(trail_[i].var());
	unroll(l);
}

/** similar to analyzeConflict, but for lhbr */
Lit PropEngine::analyzeBin(util::span<const Lit> tail)
{
	if (level() == 0)
		return Lit::undef();
	assert(level() > 0);
	std::priority_queue<std::pair<int, Lit>> todo;

	Lit dom = binDom[tail[0].var()];

	for (Lit l : tail)
	{
		assert(assign[l.neg()]);
		if (trailPos[l.var()] < mark_[0])
			continue;
		if (binDom[l.var()] != dom)
			return Lit::undef();
		todo.emplace(trailPos[l.var()], l);
	}

	while (true)
	{
		// next literal
		assert(!todo.empty());
		Lit l = todo.top().second;
		todo.pop();
		assert(assign[l.neg()]);

		// remove duplicates from queue
		while (!todo.empty() && todo.top().second == l)
			todo.pop();

		// nothing else -> we found UIP
		if (todo.empty())
			return l;

		// otherwise resolve
		Reason r = reason[l.var()];
		assert(r.isBinary());
		todo.emplace(trailPos[r.lit().var()], r.lit());
	}
}

// helper for OTF strengthening
bool PropEngine::isRedundant(Lit lit)
{
	assert(lit.proper());

	Reason r = reason[lit.var()];

	if (r.isUndef()) // descision variable -> cannot be removed
		return false;

	if (r.isBinary())
	{
		return seen[r.lit().var()] ||
		       (sat.stats.otf >= 2 && isRedundant(r.lit()));
	}

	assert(r.isLong());
	{
		Clause &cl = sat.clauses[r.cref()];
		for (Lit l : cl.lits())
			if (l != lit && !seen[l.var()] &&
			    !(sat.stats.otf >= 2 && isRedundant(l)))
				return false;
		seen[lit.var()] = true; // shortcut other calls to isRedundant
		return true;
	}
}

uint8_t PropEngine::calcGlue(util::span<const Lit> cl) const
{
	int glue = 1;
	for (int lev = 1; lev < level(); ++lev)
		for (Lit l : cl)
		{
			assert(assign[l.neg()]);
			if (mark_[lev - 1] <= trailPos[l.var()] &&
			    trailPos[l.var()] < mark_[lev])
			{
				glue += 1;
				break;
			}
		}
	if (glue > 255)
		return 255;
	return (uint8_t)glue;
}

void PropEngine::printTrail() const
{
	for (int l = 0; l <= level(); ++l)
	{
		std::cout << "=== level " << l << " ===" << std::endl;
		int low = l == 0 ? 0 : mark_[l - 1];
		int high = l == (int)mark_.size() ? (int)trail_.size() : mark_[l];
		for (int i = low; i < high; ++i)
		{
			std::cout << trail_[i] << " <= ";
			Reason r = reason[trail_[i].var()];
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
