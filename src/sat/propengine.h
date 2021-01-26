#ifndef SAT_PROPENGINE_H
#define SAT_PROPENGINE_H

#include "sat.h"
#include "sat/activity_heap.h"
#include "util/bitset.h"
#include <cassert>
#include <queue>
#include <vector>

struct Reason
{
	// val_=UINT32_MAX -> undef
	// msb=0 && lit2  = Lit::undef() -> binary clause
	// msb=0 && lit2 != Lit::undef() -> ternary clause
	// msb=1 -> long clause (lit2 unused)
  private:
	uint32_t val_;
	Lit lit2_;

  public:
	constexpr Reason() : val_(UINT32_MAX) {}

	explicit constexpr Reason(Lit a) : val_(a), lit2_(Lit::undef())
	{
		assert(a.proper());
	}

	explicit constexpr Reason(Lit a, Lit b) : val_(a), lit2_(b)
	{
		assert(a.proper() && b.proper());
	}

	explicit constexpr Reason(CRef cref) : val_(cref | (1u << 31))
	{
		assert(cref.proper());
	}

	static constexpr Reason undef() { return Reason(); }

	bool isBinary() const
	{
		return val_ != UINT32_MAX && (val_ & (1u << 31)) == 0 &&
		       lit2_ == Lit::undef();
	}

	bool isTernary() const
	{
		return val_ != UINT32_MAX && (val_ & (1u << 31)) == 0 &&
		       lit2_ != Lit::undef();
	}

	bool isLong() const
	{
		return val_ != UINT32_MAX && (val_ & (1u << 31)) != 0;
	}

	bool isUndef() const { return val_ == UINT32_MAX; }

	Lit lit() const
	{
		assert(isBinary() || isTernary());
		return Lit(val_ & (UINT32_MAX >> 1));
	}

	Lit lit2() const
	{
		assert(isTernary());
		return lit2_;
	}

	CRef cref() const
	{
		assert(isLong());
		return CRef(val_ & (UINT32_MAX >> 1));
	}

	constexpr bool operator==(Reason b) const { return val_ == b.val_; }
};

struct Watch
{
	// msb=0 -> ternary clause (lit2 is other literal)
	// msb=1 -> long clause (lit2 is blocking literal)
  private:
	uint32_t val_;
	Lit lit2_;

  public:
	// something like 'Watch::undef()' is never used, but being
	// default-constructible is still nice
	Watch() = default;

	/** create watch for (implicit) ternary clause */
	explicit constexpr Watch(Lit a, Lit b) : val_(a), lit2_(b)
	{
		assert(a.proper() && b.proper());
	}

	/** create watch for long clause (with blocking literal) */
	explicit constexpr Watch(CRef cref, Lit blocking)
	    : val_(cref | (1u << 31)), lit2_(blocking)
	{
		assert(cref.proper() && blocking.proper());
	}

	bool isTernary() const { return (val_ & (1u << 31)) == 0; }

	bool isLong() const { return (val_ & (1u << 31)) != 0; }

	Lit lit() const
	{
		assert(isTernary());
		return Lit(val_ & (UINT32_MAX >> 1));
	}

	/** either last literal of ternary, or blocking literal of long clause */
	Lit lit2() const { return lit2_; }
	Lit &lit2() { return lit2_; }

	CRef cref() const
	{
		assert(isLong());
		return CRef(val_ & (UINT32_MAX >> 1));
	}
};

/**
 * Unit propagation.
 */
class PropEngine
{
  public:
	Sat &sat;

  private:
	util::bitset seen;         // temporary during conflict analysis
	bool isRedundant(Lit lit); // helper for OTF strengthening

	std::vector<Lit> trail_; // assigned variables
	std::vector<int> mark_;  // indices into trail

  public:
	using watches_t = std::vector<util::small_vector<Watch, 7>>;
	watches_t watches;

	std::vector<Reason> reason; // only valid for assigned vars
	std::vector<Lit> binDom;    // ditto
	std::vector<int> trailPos;  // ditto

	std::vector<Lit> conflictClause;

	void set(Lit x, Reason r);             // no unit propagation
	void propagateBinary(Lit x, Reason r); // binary unit propagation

	Lit analyzeBin(util::span<const Lit> reason); // helper for LHBR
	Lit analyzeBin(Lit a, Lit b);                 // same as analyzeBin({a,b})

  public:
	std::vector<bool> assign;
	bool conflict = false;

	/** constructor */
	PropEngine(Sat &sat);

	/** assign a literal and do unit propagation */
	void branch(Lit x);                  // starts a new level
	void propagateFull(Lit x, Reason r); // stays on current level

	/** read-only view (into trail_) of assignments */
	util::span<const Lit> trail() const;      // all levels
	util::span<const Lit> trail(int l) const; // level l

	/**
	 * Add clause to underlying ClauseSet without propagating.
	 * Watches are set on cl[0] and cl[1] (if cl.size() >= 3)
	 * returns reason with which cl[0] might be propagated
	 */
	Reason addLearntClause(Lit c0, Lit c1);
	Reason addLearntClause(const std::vector<Lit> &cl, uint8_t glue);

	int unassignedVariable() const; /** -1 if everything is assigned */

	int level() const;                               /** current level */
	void unroll(int l);                              /** unroll assignments */
	void unroll_and_activate(int l, ActivityHeap &); /** re-add vars to heap */

	/**
	 *  - analyze conflict up to UIP
	 *  - calls f on all involved literals (intended for activity bumping)
	 *  - performs otf minimization if enabled in config
	 */
	template <typename F> int analyzeConflict(std::vector<Lit> &learnt, F f);
	int analyzeConflict(std::vector<Lit> &learnt);

	/** same, but analyze up to one variable per level */
	template <typename F>
	int analyzeConflictFull(std::vector<Lit> &learnt, F f);
	int analyzeConflictFull(std::vector<Lit> &learnt);

	/** compute glue, i.e. number of distinct decision levels of clause */
	uint8_t calcGlue(util::span<const Lit> cl) const;

	/** for debugging */
	void printTrail() const;
};

inline util::span<const Lit> PropEngine::trail() const { return trail_; }

inline util::span<const Lit> PropEngine::trail(int l) const
{
	assert(0 <= l && l <= level());
	auto t = trail();
	if (l == 0 && level() == 0)
		return t;
	else if (l == 0)
		return t.slice(0, mark_[0]);
	else if (l == level())
		return t.slice(mark_[l - 1], t.size());
	else
		return t.slice(mark_[l - 1], mark_[l]);
}

inline int PropEngine::analyzeConflict(std::vector<Lit> &learnt)
{
	auto callback = [](Lit) {};
	return analyzeConflict<decltype(callback)>(learnt, callback);
}

template <typename F>
inline int PropEngine::analyzeConflict(std::vector<Lit> &learnt, F f)
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

	while (!todo.empty())
	{
		// next literal
		Lit l = todo.top().second;
		todo.pop();
		// assert(assign[l.neg()]);

		// remove duplicates from queue
		while (!todo.empty() && todo.top().second == l)
			todo.pop();

		// callback (probably for tracking variable activity)
		f(l);

		// next one is reason side
		//   -> this one is reason side or UIP
		//   -> add this one to learnt clause
		if (todo.empty() || todo.top().first < mark_.back())
		{
			if (trailPos[l.var()] >= mark_[0]) // skip level 0 assignments
				learnt.push_back(l);
		}
		else // otherwise resolve
		{
			Reason r = reason[l.var()];
			if (r.isBinary())
			{
				todo.emplace(trailPos[r.lit().var()], r.lit());
				seen[r.lit().var()] = true;
			}
			else if (r.isTernary())
			{
				todo.emplace(trailPos[r.lit().var()], r.lit());
				todo.emplace(trailPos[r.lit2().var()], r.lit2());
				seen[r.lit().var()] = true;
				seen[r.lit2().var()] = true;
			}
			else if (r.isLong())
			{
				const Clause &cl = sat.clauses[r.cref()];
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

	// NOTE: at this point, resolution is done and the learnt clause is
	// ordered by decreasing trailPos. In particular, learnt[0] is the UIP

	// strengthen the conflict clause using the reason clauses
	// (NOTE: keep the order of remaining literals the same)
	if (sat.stats.otf >= 1)
	{
		int j = 1;
		for (int i = 1; i < (int)learnt.size(); ++i)
			if (isRedundant(learnt[i]))
				sat.stats.nLitsOtfRemoved += 1;
			else
				learnt[j++] = learnt[i];
		learnt.resize(j);
	}

	// determine backtrack level ( = level of learnt[1])
	assert(!learnt.empty());
	if (learnt.size() == 1)
		return 0;
	int i = level() - 1;
	while (mark_[i] > trailPos[learnt[1].var()])
		i -= 1;

	return i + 1;
}

inline int PropEngine::analyzeConflictFull(std::vector<Lit> &learnt)
{
	auto callback = [](Lit) {};
	return analyzeConflictFull<decltype(callback)>(learnt, callback);
}

template <typename F>
inline int PropEngine::analyzeConflictFull(std::vector<Lit> &learnt, F f)
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

		// callback (probably for tracking variable activity)
		f(l);

		// next one is a level up
		//   -> this one is the last of its level
		//   -> add this one to learnt clause
		if (todo.empty() || todo.top().first < mark_[lev])
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
				const Clause &cl = sat.clauses[r.cref()];
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

	// NOTE: at this point, resolution is done and the learnt clause is
	// ordered by decreasing trailPos. In particular, learnt[0] is the UIP

	// NOTE: we should have only one literal per level,
	//       so otf-strengthening is impossible

	// determine backtrack level ( = level of learnt[1])
	assert(!learnt.empty());
	if (learnt.size() == 1)
		return 0;
	int i = level() - 1;
	while (mark_[i] > trailPos[learnt[1].var()])
		i -= 1;

	return i + 1;
}

#endif
