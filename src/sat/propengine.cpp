#include "sat/propengine.h"

#include "fmt/format.h"
#include <cassert>
#include <optional>
#include <queue>

using namespace dawn;

bool dawn::PropEngine::is_redundant(Lit lit, bool recursive)
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

		seen.add(lit.var()); // shortcut other calls to is_redundant
		return true;
	}
}

void dawn::PropEngine::propagate_binary(Lit x, Reason r)
{
	assert(!conflict);
	assert(!assign[x] && !assign[x.neg()]);

	size_t pos = trail_.size();

	assign.set(x);
	trail_.push_back(x);
	assign_level[x.var()] = (int)mark_.size();
	reason[x.var()] = r;

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

			else if (assign[z.neg()]) // already assigned false -> conflict
			{
				stats.nBinConfls += 1;
				assert(conflict_clause.empty());
				conflict_clause.push_back(y.neg());
				conflict_clause.push_back(z);
				conflict = true;
				return;
			}

			else // else -> propagate
			{
				assign.set(z);
				trail_.push_back(z);
				assign_level[z.var()] = (int)mark_.size();
				reason[z.var()] = Reason(y.neg());
				stats.nBinProps += 1;
			}
		}
	}
}

dawn::PropEngine::PropEngine(Cnf const &cnf)
    : watches(cnf.var_count() * 2), reason(cnf.var_count()),
      assign_level(cnf.var_count()), assign(cnf.var_count())
{
	// empty clause -> don't bother doing anything
	if (cnf.contradiction)
	{
		conflict = true;
		return;
	}

	// copy clause data
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
		if (propagate(l) == -1)
			return;
}

int dawn::PropEngine::propagate(Lit x, Reason r)
{
	assert(!conflict);
	if (assign[x])
		return 0;
	if (assign[x.neg()])
	{
		// mathematically, it would make sense to set 'conflictClause' to
		// {x, x.neg()} here, but it is not used anywhere, so we dont.
		conflict = true;
		return -1;
	}

	int pos = (int)trail_.size();
	int startPos = pos;
	propagate_binary(x, r);
	if (conflict)
		return -1;

	while (pos != (int)trail_.size())
	{
		Lit y = trail_[pos++];
		auto &ws = watches[y.neg()];
		stats.watchHistogram.add((int)ws.size());
		for (size_t wi = 0; wi < ws.size(); ++wi)
		{
			CRef ci = ws[wi];
			Clause &c = clauses[ci];
			stats.clauseSizeHistogram.add((int)c.size());

			// lazy-removed clause -> detach and do nothing
			if (c.color() == Color::black)
			{
				ws[wi] = ws.back();
				--wi;
				ws.pop_back();
				goto next_watch;
			}

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
				assert(conflict_clause.empty());
				conflict_clause.assign(c.begin(), c.end());
				return -1;
			}
			else
			{
				stats.nLongProps += 1;
				// This is the point where we previously did LHBR. But we
				// already do hyper binaries in top-level in-tree probing, so it
				// is not worth the complexity here.
				propagate_binary(c[0], Reason(ci));
				if (conflict)
					return -1;
			}

		next_watch:;
		}
	}
	return (int)trail_.size() - startPos;
}

int dawn::PropEngine::propagate_neg(std::span<const Lit> xs)
{
	int start_pos = (int)trail_.size();
	for (Lit x : xs)
		if (propagate(x.neg()) == -1)
			return -1;
	return (int)trail_.size() - start_pos;
}

int dawn::PropEngine::propagate_neg(std::span<const Lit> xs, Lit pivot)
{
	int start_pos = (int)trail_.size();
	for (Lit x : xs)
		if (x != pivot && propagate(x.neg()) == -1)
			return -1;
	if (propagate(pivot) == -1)
		return -1;
	return (int)trail_.size() - start_pos;
}

int PropEngine::branch(Lit x)
{
	mark();
	return propagate(x);
}

int PropEngine::probe(Lit x)
{
	mark();
	int res = propagate(x);
	unroll(level() - 1);
	return res;
}

int PropEngine::probe_neg(std::span<const Lit> xs)
{
	mark();
	int res = propagate_neg(xs);
	unroll(level() - 1);
	return res;
}

int PropEngine::probe_neg(std::span<const Lit> xs, Lit pivot)
{
	mark();
	int res = propagate_neg(xs, pivot);
	unroll(level() - 1);
	return res;
}

void PropEngine::analyze_conflict(std::vector<Lit> &learnt,
                                  ActivityHeap *activity_heap, int otf)
{
	assert(conflict);
	assert(!conflict_clause.empty());
	assert(level() > 0);
	seen.clear();
	learnt.resize(0);
	int pending = 0; // number of pending resolutions

	// NOTE: On the reason side, 'seen' marks variables that are already
	//       present in the learnt clause, to avoid duplicates. On the conflict
	//       side, it marks variables that will be or have been resolved.

	auto handle = [&](Lit l) {
		assert(assign[l] && !assign[l.neg()]);

		if (!seen.add(l.var()) || assign_level[l.var()] == 0)
			return;

		if (activity_heap)
			activity_heap->bump_variable_activity(l.var());
		if (assign_level[l.var()] == level())
			pending += 1;
		else
			learnt.push_back(l.neg());
	};

	for (Lit l : conflict_clause)
		handle(l.neg());
	assert(pending >= 2);

	for (auto it = trail_.rbegin();; ++it)
	{
		if (!seen[it->var()])
			continue;
		Lit a = *it;
		assert(assign_level[a.var()] == level());
		assert(assign[a] && !assign[a.neg()]);

		// found UIP -> stop
		if (pending == 1)
		{
			learnt.push_back(a.neg());
			break;
		}

		// otherwise -> resolve
		Reason r = reason[a.var()];
		pending -= 1;

		if (r.isBinary())
		{
			handle(r.lit().neg());
		}
		else if (r.isLong())
		{
			const Clause &cl = clauses[r.cref()];
			assert(cl[0] == a);
			for (int i = 1; i < cl.size(); ++i)
				handle(cl[i].neg());
		}
		else
			assert(false);
	}

	if (activity_heap)
		activity_heap->decay_variable_activity();

	std::sort(learnt.begin(), learnt.end(), [&](Lit a, Lit b) {
		return assign_level[a.var()] > assign_level[b.var()];
	});
	if (otf >= 1)
		shorten_learnt(learnt, otf >= 2);

	stats.nLitsLearnt += learnt.size();
	stats.learn_events.push_back(
	    {.depth = level(), .size = (int)learnt.size()});
}

void dawn::PropEngine::shorten_learnt(std::vector<Lit> &learnt, bool recursive)
{
	int j = 1;
	for (int i = 1; i < (int)learnt.size(); ++i)
		if (is_redundant(learnt[i], recursive))
			stats.nLitsOtfRemoved += 1;
		else
			learnt[j++] = learnt[i];
	learnt.resize(j);
}

int dawn::PropEngine::backtrack_level(std::span<const Lit> learnt) const
{
	assert(!learnt.empty());
	if (learnt.size() == 1)
		return 0;
	assert(assign_level[learnt[0].var()] > assign_level[learnt[1].var()]);
	return assign_level[learnt[1].var()];
}

void dawn::PropEngine::print_trail() const
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

Reason dawn::PropEngine::add_clause(Lit c0, Lit c1)
{
	assert(c0.var() != c1.var());
	bins[c0].push_back(c1);
	bins[c1].push_back(c0);
	return Reason(c1);
}

Reason dawn::PropEngine::add_clause(const std::vector<Lit> &cl, Color color)
{
	assert(cl.size() >= 2);

	if (cl.size() == 2)
		return add_clause(cl[0], cl[1]);

	CRef cref = clauses.add_clause(cl, color);
	watches[cl[0]].push_back(cref);
	watches[cl[1]].push_back(cref);
	return Reason(cref);
}

PropEngineLight::PropEngineLight(Cnf &cnf, bool attach_clauses)
    : cnf(cnf), watches(cnf.var_count() * 2), assign(cnf.var_count())
{
	// empty clause -> don't bother doing anything
	if (cnf.contradiction)
	{
		conflict = true;
		return;
	}

	// attach long clauses
	if (attach_clauses)
		for (auto [i, c] : cnf.clauses.enumerate())
		{
			if (c.color() == Color::black)
				continue;
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

void PropEngineLight::attach_clause(CRef cref)
{
	assert(cref.proper());
	Clause const &cl = cnf.clauses[cref];
	assert(cl.size() >= 2);
	assert(cl.color() != Color::black);
	assert(!assign[cl[0]] && !assign[cl[0].neg()]);
	assert(!assign[cl[1]] && !assign[cl[1].neg()]);
	watches[cl[0]].push_back(cref);
	watches[cl[1]].push_back(cref);
}

void PropEngineLight::detach_clause(CRef cref)
{
	assert(cref.proper());
	Clause const &cl = cnf.clauses[cref];
	assert(cl.size() >= 2);
	assert(cl.color() != Color::black);
	assert(!assign[cl[0]] && !assign[cl[0].neg()]);
	assert(!assign[cl[1]] && !assign[cl[1].neg()]);

	auto &ws0 = watches[cl[0]];
	auto &ws1 = watches[cl[1]];
	ws0.erase(std::remove(ws0.begin(), ws0.end(), cref), ws0.end());
	ws1.erase(std::remove(ws1.begin(), ws1.end(), cref), ws1.end());
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
	assert(x.proper());

	if (conflict)
		return -1;
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

			// lazy-removed clause -> detach and do nothing
			if (c.color() == Color::black)
			{
				ws[wi] = ws.back();
				--wi;
				ws.pop_back();
				continue;
			}

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

int PropEngineLight::propagate_neg(std::span<const Lit> xs, Lit a)
{
	int r = 0;
	for (Lit x : xs)
		if (int s = propagate(x.neg() ^ (x == a)); s == -1)
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

int PropEngineLight::probe_neg(std::span<const Lit> xs, Lit pivot)
{
	assert(!conflict);
	mark();
	int r = propagate_neg(xs, pivot);
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
