#include "sat/propengine.h"

#include "fmt/format.h"
#include <cassert>
#include <optional>
#include <queue>

namespace dawn {

PropEngine::PropEngine(Cnf const &cnf)
    : seen(cnf.var_count()), watches(cnf.var_count() * 2),
      reason(cnf.var_count()), trailPos(cnf.var_count()),
      assign(cnf.var_count())
{
	// util::StopwatchGuard swg(sat.stats.swSearchInit); // TODO

	// empty clause -> don't bother doing anything
	if (cnf.contradiction)
	{
		conflict = true;
		return;
	}

	clauses = cnf.clauses;
	bins = cnf.bins;

	// attach long clauses
	for (auto [i, c] : clauses.enumerate())
	{
		assert(c.size() >= 2);
		watches[c[0]].push_back(i);
		watches[c[1]].push_back(i);
	}

	// propagate unary clauses
	for (auto l : cnf.units)
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
	assign.set(x);
	reason[x.var()] = r;
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
		stats.binHistogram.add((int)bins[y.neg()].size());
		for (Lit z : bins[y.neg()])
		{
			if (assign[z]) // already assigned true -> do nothing
			{
				stats.nBinSatisfied += 1;
				continue;
			}

			if (assign[z.neg()]) // already assigned false -> conflict
			{
				stats.nBinConfls += 1;
				assert(conflictClause.empty());
				conflictClause.push_back(y.neg());
				conflictClause.push_back(z);
				conflict = true;
				return;
			}

			stats.nBinProps += 1;
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
		stats.watchHistogram.add((int)ws.size());
		for (size_t wi = 0; wi < ws.size(); ++wi)
		{
			CRef ci = ws[wi];
			Clause &c = clauses[ci];
			stats.clauseSizeHistogram.add((int)c.size());

			// move y to c[1] (so that c[0] is the potentially propagated one)
			if (c[0] == y.neg())
				std::swap(c[0], c[1]);
			assert(c[1] == y.neg());

			// other watched lit is satisfied -> do nothing
			if (assign[c[0]])
			{
				stats.nLongSatisfied += 1;
				continue;
			}

			// check the tail of the clause
			for (size_t i = 2; i < c.size(); ++i)
				if (!assign[c[i].neg()]) // literal satisfied or undef -> move
				                         // watch
				{
					stats.nLongShifts += 1;
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
				stats.nLongConfls += 1;
				conflict = true;
				assert(conflictClause.empty());
				for (Lit l : c.lits())
					conflictClause.push_back(l);
				return;
			}
			else
			{
				stats.nLongProps += 1;
				// This is the point where we previously did LHBR. But we
				// already do hyper binaries in top-level in-tree probing, so it
				// is not worth the complexity here.
				propagateBinary(c[0], Reason(ci));
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

Reason PropEngine::add_learnt_clause(Lit c0, Lit c1)
{
	assert(c0.var() != c1.var());
	bins[c0].push_back(c1);
	bins[c1].push_back(c0);
	return Reason(c1);
}

Reason PropEngine::add_learnt_clause(const std::vector<Lit> &cl, uint8_t glue)
{
	assert(cl.size() >= 2);

	if (cl.size() == 2)
		return add_learnt_clause(cl[0], cl[1]);

	CRef cref = clauses.add_clause(cl, false);
	clauses[cref].glue = glue;
	watches[cl[0]].push_back(cref);
	watches[cl[1]].push_back(cref);
	assert(2 <= glue && glue <= cl.size());
	return Reason(cref);
}

int PropEngine::unassignedVariable() const
{
	for (int i = 0; i < var_count(); ++i)
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
		assign.unset(lit);
	}
	mark_.resize(l);
}

void PropEngine::unroll(int l, ActivityHeap &activity_heap)
{
	assert(l < level());
	for (int i = mark_[l]; i < (int)trail_.size(); ++i)
		activity_heap.push(trail_[i].var());
	unroll(l);
}

void PropEngine::analyze_conflict(std::vector<Lit> &learnt,
                                  ActivityHeap *activity_heap)
{
	assert(learnt.empty());
	assert(conflict);
	assert(!conflictClause.empty());
	assert(level() > 0);
	seen.clear();

	std::priority_queue<std::pair<int, Lit>> todo;

	for (Lit l : conflictClause)
	{
		// assert(assign[l.neg()]);
		seen[l.var()] = true;
		todo.emplace(trailPos[l.var()], l);
	}
	int lev = (int)mark_.size() - 1;
	while (!todo.empty())
	{
		// next literal
		Lit l = todo.top().second;
		todo.pop();
		// assert(assign[l.neg()]);

		// remove duplicates from queue
		while (!todo.empty() && todo.top().second == l)
			todo.pop();

		if (activity_heap)
			activity_heap->bump_variable_activity(l.var());

		// next one is reason side
		//   -> this one is reason side or UIP
		//   -> add this one to learnt clause
		/*if (todo.empty() ||
		    (!config_.full_resolution && todo.top().first < mark_.back()) ||
		    (config_.full_resolution && todo.top().first < mark_[lev]))*/
		if (todo.empty() || todo.top().first < mark_.back())
		{
			if (trailPos[l.var()] >= mark_[0]) // skip level 0 assignments
			{
				learnt.push_back(l);
				while (!todo.empty() && todo.top().first < mark_[lev])
					lev--;
			}
		}
		else // otherwise resolve
		{
			Reason r = reason[l.var()];
			if (r.isBinary())
			{
				todo.emplace(trailPos[r.lit().var()], r.lit());
				seen[r.lit().var()] = true;
			}
			else if (r.isLong())
			{
				const Clause &cl = clauses[r.cref()];
				// assert(cl[0] == l.neg());
				for (int i = 1; i < cl.size(); ++i)
				{
					todo.emplace(trailPos[cl[i].var()], cl[i]);
					seen[cl[i].var()] = true;
				}
			}
			else
				assert(false);
		}
	}
}

int PropEngine::backtrack_level(std::span<const Lit> learnt) const
{
	assert(!learnt.empty());
	if (learnt.size() == 1)
		return 0;
	int i = level() - 1;
	while (mark_[i] > trailPos[learnt[1].var()])
		i -= 1;

	return i + 1;
}

void PropEngine::shorten_learnt(std::vector<Lit> &learnt, bool recursive)
{
	int j = 1;
	for (int i = 1; i < (int)learnt.size(); ++i)
		if (is_redundant(learnt[i], recursive))
			stats.nLitsOtfRemoved += 1;
		else
			learnt[j++] = learnt[i];
	learnt.resize(j);
}

// helper for OTF strengthening
bool PropEngine::is_redundant(Lit lit, bool recursive)
{
	assert(lit.proper());

	Reason r = reason[lit.var()];

	if (r.isUndef()) // descision variable -> cannot be removed
		return false;

	if (r.isBinary())
	{
		return seen[r.lit().var()] ||
		       (recursive && is_redundant(r.lit(), recursive));
	}

	assert(r.isLong());
	{
		Clause &cl = clauses[r.cref()];
		for (Lit l : cl.lits())
			if (l != lit && !seen[l.var()] &&
			    !(recursive && is_redundant(l, recursive)))
				return false;

		seen[lit.var()] = true; // shortcut other calls to isRedundant
		return true;
	}
}

uint8_t PropEngine::calcGlue(std::span<const Lit> cl) const
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
		fmt::print("=== level {} ===\n", l);
		int low = l == 0 ? 0 : mark_[l - 1];
		int high = l == (int)mark_.size() ? (int)trail_.size() : mark_[l];
		for (int i = low; i < high; ++i)
		{
			fmt::print("{} <= ", trail_[i]);
			Reason r = reason[trail_[i].var()];
			if (r == Reason::undef())
				fmt::print("()\n");
			else if (r.isBinary())
				fmt::print("bin ({})\n", r.lit());
			else if (r.isLong())
				fmt::print("long ({})\n", clauses[r.cref()]);
			else
				assert(false);
		}
	}
}

// simple RAII class that calls a function when it goes out of scope
template <typename F> struct Guard
{
	F f;
	Guard(F f) : f(f) {}
	~Guard() { f(); }
};

PropEngineLight::PropEngineLight(Cnf &cnf)
    : cnf(cnf), watches(cnf.var_count() * 2), assign(cnf.var_count())
{
	// empty clause -> don't bother doing anything
	if (cnf.contradiction)
	{
		conflict = true;
		return;
	}

	// attach long clauses
	for (auto [i, c] : cnf.clauses.enumerate())
	{
		assert(c.size() >= 3);
		watches[c[0]].push_back(i);
		watches[c[1]].push_back(i);
	}

	// propagate unary clauses
	for (auto l : cnf.units)
	{
		if (assign[l])
			continue;
		if (assign[l.neg()])
		{
			conflict = true;
			return;
		}
		propagate(l);
		if (conflict)
			return;
	}
}

void PropEngineLight::propagate_binary(Lit x)
{
	assert(!conflict);
	assert(x.proper() && !assign[x] && !assign[x.neg()]);

	size_t pos = trail_.size();
	assign.set(x);
	trail_.push_back(x);

	while (pos != trail_.size())
	{
		Lit y = trail_[pos++];

		for (Lit z : cnf.bins[y.neg()])
		{
			if (assign[z])
				continue;

			if (assign[z.neg()])
			{
				conflict = true;
				return;
			}

			// else -> propagate
			assign.set(z);
			trail_.push_back(z);
		}
	}
}

int PropEngineLight::propagate_impl(Lit x, bool with_hbr)
{
	assert(!conflict);
	assert(x.proper());

	// propagating an already-assigned variable is allowed (and does nothing)
	if (assign[x])
		return 0;
	if (assign[x.neg()])
	{
		conflict = true;
		return -1;
	}

	size_t pos = trail_.size();
	int trail_old = (int)trail_.size();

	propagate_binary(x);
	if (conflict)
		return -1;

	while (pos != trail_.size())
	{
		Lit y = trail_[pos++];

		// propagate long clauses
		auto &ws = watches[y.neg()];
		for (size_t wi = 0; wi < ws.size(); ++wi)
		{
			CRef ci = ws[wi];
			Clause &c = cnf.clauses[ci];

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
				return -1;
			}
			else
			{
				if (with_hbr)
				{
					nHbr += 1;
					cnf.add_binary(c[0], x.neg());
				}
				propagate_binary(c[0]);
				if (conflict)
					return -1;
			}

		next_watch:;
		}
	}
	return (int)trail_.size() - trail_old;
}

int PropEngineLight::propagate(Lit x) { return propagate_impl(x, false); }

int PropEngineLight::propagate_with_hbr(Lit x)
{
	return propagate_impl(x, true);
}

int PropEngineLight::propagate_neg(std::span<const Lit> xs)
{
	int r = 0;
	for (Lit x : xs)
		if (int s = propagate(x.neg()); s == -1)
			return -1;
		else
			r += s;
	return r;
}

void PropEngineLight::mark()
{
	assert(!conflict);
	mark_.push_back(trail_.size());
}

int PropEngineLight::level() const { return (int)mark_.size(); }

void PropEngineLight::unroll()
{
	assert(!mark_.empty());
	conflict = false;
	while ((int)trail_.size() > mark_.back())
	{
		Lit lit = trail_.back();
		trail_.pop_back();
		assign.unset(lit);
	}
	mark_.pop_back();
}

int PropEngineLight::probe(Lit a)
{
	assert(!conflict);
	mark();
	int r = propagate(a);
	unroll();
	return r;
}

int PropEngineLight::probe_neg(std::span<const Lit> xs)
{
	assert(!conflict);
	mark();
	int r = propagate_neg(xs);
	unroll();
	return r;
}

std::span<const Lit> PropEngineLight::trail() const { return trail_; }

std::span<const Lit> PropEngineLight::trail(int l) const
{
	assert(0 <= l && l <= level());
	auto t = trail();
	if (l == 0 && level() == 0)
		return t;
	else if (l == 0)
		return t.subspan(0, mark_[0]);
	else if (l == level())
		return t.subspan(mark_[l - 1]);
	else
		return t.subspan(mark_[l - 1], mark_[l] - mark_[l - 1]);
}

int runUnitPropagation(Sat &sat)
{
	// early out if no units
	if (!sat.contradiction && sat.units.empty())
		return 0;

	// the PropEngine constructor already does all the UP we want
	auto p = PropEngineLight(sat);

	// conflict -> add empty clause and remove everything else
	if (p.conflict)
	{
		sat.add_empty();
		sat.units.resize(0);
		for (int i = 0; i < sat.var_count() * 2; ++i)
			sat.bins[i].resize(0);
		sat.clauses.clear();
		int n = sat.var_count();
		sat.renumber(std::vector<Lit>(n, Lit::elim()), 0);
		return n;
	}

	assert(p.trail().size() != 0);

	auto trans = std::vector<Lit>(sat.var_count(), Lit::undef());
	for (Lit u : p.trail())
	{
		assert(trans[u.var()] != Lit::fixed(u.sign()).neg());
		trans[u.var()] = Lit::fixed(u.sign());
	}
	int newVarCount = 0;
	for (int i : sat.all_vars())
	{
		if (trans[i] == Lit::undef())
			trans[i] = Lit(newVarCount++, false);
	}

	// NOTE: this renumber() changes sat and thus invalidates p
	sat.renumber(trans, newVarCount);
	assert(sat.units.empty());

	return (int)p.trail().size();
}

} // namespace dawn
