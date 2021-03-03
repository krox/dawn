#include "sat/elimination.h"

#include "util/bit_vector.h"
#include <algorithm>
#include <queue>
#include <vector>

namespace dawn {

namespace {

/**
 * Check whether the resolvent of two clauses is tautology.
 * NOTE: this method assumes that the lits in both clauses are sorted. If they
 *       are not, it just produces some false-negatives. This means the scoring
 *       will be too pessimistic, but nothing will be broken. Though in the
 *       current implementation, no such thing can happen.
 * TODO: in case the resolvent is not tautological, we could trivially determine
 *       its size. If it is very small, it might me worthwhile to add it as
 *       a learnt clause, even if to variable-elimination takes place.
 */
bool is_resolvent_tautological(util::span<const Lit> a, util::span<const Lit> b)
{
	int count = 0; // number of shared variables with opposite sign

	for (size_t i = 0, j = 0; i < a.size() && j < b.size();)
	{
		if (a[i].var() < b[j].var())
			++i;
		else if (a[i].var() > b[j].var())
			++j;
		else
		{
			if (a[i] == b[j].neg())
				if (++count >= 2)
					return true;
			++i;
			++j;
		}
	}

	assert(count == 1);
	return false;
}

/**
 * compute resolvent of a and b.
 *   - assumes sorted lits in both clauses
 *   - asserts resolvent not tautological
 *   - produces sorted clause
 */
std::vector<Lit> resolvent(util::span<const Lit> a, util::span<const Lit> b)
{
	for (size_t i = 1; i < a.size(); ++i)
		assert(a[i - 1].var() < a[i].var());
	for (size_t i = 1; i < b.size(); ++i)
		assert(b[i - 1].var() < b[i].var());

	std::vector<Lit> r;
	int count = 0; // number of shared variables with opposite sign

	size_t i = 0, j = 0;
	while (i < a.size() && j < b.size())
	{
		if (a[i].var() < b[j].var())
			r.push_back(a[i++]);
		else if (a[i].var() > b[j].var())
			r.push_back(b[j++]);
		else
		{
			if (a[i] == b[j].neg())
				++count;
			else
				r.push_back(a[i]);
			++i;
			++j;
		}
	}
	while (i < a.size())
		r.push_back(a[i++]);
	while (j < b.size())
		r.push_back(b[j++]);

	// count == 0 -> resolution not valid at all
	// count == 1 -> resolution valid, resolvent is r
	// count >= 2 -> resolution valid, resolvent tautological, r invalid
	assert(count >= 1);
	assert(count == 1);
	return r;
}

/** resolvent of a with the binary clause b,c */
std::vector<Lit> resolvent(util::span<const Lit> a, Lit b, Lit c)
{
	assert(b.var() != c.var());
	if (b.var() > c.var())
		std::swap(b, c);
	return resolvent(a, std::array<Lit, 2>{b, c});
}

struct BVE
{
	/**
	 * NOTE:
	 *   - all irreducible clauses in sat are sorted
	 *     (this property is maintained in the resolvent() functions)
	 *   - occ-lists contain exactly the non-removed irreduble clauses
	 *     (this property is restored after each variable elimination)
	 */
	Sat &sat;
	using occs_t = std::vector<std::vector<CRef>>;
	occs_t occs;
	util::bit_vector eliminated;

	BVE(Sat &sat_)
	    : sat(sat_), occs(2 * sat_.varCount()), eliminated(sat_.varCount())
	{
		// sort lits and create occ-lists
		for (auto [ci, cl] : sat.clauses)
			if (cl.irred())
			{
				std::sort(cl.lits().begin(), cl.lits().end());
				for (Lit a : cl.lits())
					occs[a].push_back(ci);
			}
	}

	/**
	 * Calculate the score of removing variable v. The score is simply the
	 * number of non-tautological resolvents created minus number of removed
	 * clauses, i.e. lower is better.
	 */
	int compute_score(int v)
	{
		// NOTE: only eliminations with negative scores will ever be
		//       implemented. So as an optimization, we abort as soon as the
		//       score becomes positive, without computing a precise number.

		// never eliminate a variable that has a unit clause (could break our
		// implementaion of resolution and would be stupid anyway)
		for (Lit u : sat.units)
			if (u.var() == v)
				return 1000;

		auto pos = Lit(v, false);
		auto neg = Lit(v, true);

		// its not worth scoring variables with many occurences
		if (occs[pos].size() + sat.bins[pos].size() > 10 &&
		    occs[neg].size() + sat.bins[neg].size() > 10)
			return 1000;

		int score = 0;
		score -= (int)occs[pos].size();
		score -= (int)occs[neg].size();
		score -= (int)sat.bins[pos].size();
		score -= (int)sat.bins[neg].size();

		// binary-binary resolvents
		// NOTE: If any of these result in a tautology (or unit clause) there
		//       are equivalent literals or failing literals, which should be
		//       discovered by other (cheaper) inprocessing passes. So here we
		//       just assume that does not happen to save us a little effort.
		score += (int)(sat.bins[pos].size() * sat.bins[neg].size());

		// long-binary resolvents
		// TODO: try an alternative algorithm: compute intersection of
		//       occs[x.neg] and occs[pos] without looking at at the clauses
		//       explicitly. Might be faster, but requires sorted occ-lists.
		for (Lit x : sat.bins[neg])
			for (CRef i : occs[pos])
				if (!sat.clauses[i].contains(x.neg()))
					if (++score > 0)
						return 1000;
		for (Lit x : sat.bins[pos])
			for (CRef i : occs[neg])
				if (!sat.clauses[i].contains(x.neg()))
					if (++score > 0)
						return 1000;

		// long-long resolvents
		for (CRef i : occs[pos])
			for (CRef j : occs[neg])
				if (!is_resolvent_tautological(sat.clauses[i].lits(),
				                               sat.clauses[j].lits()))
					if (++score > 0)
						return 1000;

		return score;
	}

	/** add clause to sat and update occ-lists */
	void add_clause(util::span<const Lit> cl)
	{
		CRef ci = sat.addClause(cl, true);
		if (ci == CRef::undef()) // implicit binary clause (or empty/unary?)
			return;

		for (Lit a : cl)
			occs[a].push_back(ci);
	}

	void eliminate(int v)
	{
		auto pos = Lit(v, false);
		auto neg = Lit(v, true);

		// add binary-binary resolvents
		for (Lit x : sat.bins[pos])
			for (Lit y : sat.bins[neg])
				sat.addBinary(x, y); // might this be a unit or tautology ?
		for (Lit x : sat.bins[neg])
			for (Lit y : sat.bins[pos])
				sat.addBinary(x, y);

		// add long-binary resolvents
		for (CRef i : occs[pos])
			for (Lit x : sat.bins[neg])
				if (!sat.clauses[i].contains(x.neg()))
					add_clause(resolvent(sat.clauses[i].lits(), x, neg));
		for (CRef i : occs[neg])
			for (Lit x : sat.bins[pos])
				if (!sat.clauses[i].contains(x.neg()))
					add_clause(resolvent(sat.clauses[i].lits(), x, pos));

		// add long-long resolvents
		for (CRef i : occs[pos])
			for (CRef j : occs[neg])
				if (!is_resolvent_tautological(sat.clauses[i].lits(),
				                               sat.clauses[j].lits()))
					add_clause(resolvent(sat.clauses[i].lits(),
					                     sat.clauses[j].lits()));

		sat.removed_vars.push_back(sat.innerToOuter(Lit(v, false)).var());

		std::vector<CRef> todo_renumber;
		// move old long clauses from the problem to the solution extender
		for (CRef i : occs[pos])
		{
			Clause &cl = sat.clauses[i];
			assert(cl.irred());
			CRef ci = sat.extension_clauses.addClause(cl.lits(), true);
			todo_renumber.push_back(ci);
			cl.remove();
		}
		for (CRef i : occs[neg])
		{
			Clause &cl = sat.clauses[i];
			assert(cl.irred());
			CRef ci = sat.extension_clauses.addClause(cl.lits(), true);
			todo_renumber.push_back(ci);
			cl.remove();
		}
		occs[pos].resize(0);
		occs[neg].resize(0);

		// move old binary clauses from the problem to the solution extender
		for (Lit b : sat.bins[pos])
		{
			CRef ci = sat.extension_clauses.addBinary(pos, b);
			todo_renumber.push_back(ci);
		}
		for (Lit b : sat.bins[neg])
		{
			CRef ci = sat.extension_clauses.addBinary(neg, b);
			todo_renumber.push_back(ci);
		}
		sat.bins[pos].resize(0);
		sat.bins[neg].resize(0);

		// renumber extension clauses from 'inner' to 'outer'
		for (CRef j : todo_renumber)
		{
			Clause &cl = sat.extension_clauses[j];
			for (Lit &a : cl.lits())
				a = sat.innerToOuter(a);
		}
	}

	/** returns number of removed variables */
	int run()
	{
		int nRemovedVariables = 0;

		// the prio-queue contains (score, variable) pairs. Outdated entries
		// are allowed, so we have to check whenever we are about to
		// implement a proposal
		using PII = std::pair<int, int>;
		std::priority_queue<PII, std::vector<PII>, std::greater<PII>> queue;

		// compute elimination scores of of all variables
		auto score = std::vector<int>(sat.varCount());
		for (int i = 0; i < sat.varCount(); ++i)
		{
			score[i] = compute_score(i);
			if (score[i] <= 0)
				queue.push({score[i], i});
		}

		// early-out if nothing is happening
		if (queue.empty())
			return 0;

		// temporaries
		std::vector<int> todo;
		auto seen = util::bit_vector(sat.varCount());

		while (!queue.empty())
		{
			auto [s, v] = queue.top();
			auto pos = Lit(v, false);
			auto neg = Lit(v, true);
			queue.pop();
			assert(s <= 0); // positive scores should have never

			// outdated proposal -> skip
			if (eliminated[v] || score[v] != s)
				continue;

			// determine other variables whose score will have to be
			// recalculated
			for (Lit x : sat.bins[pos])
				if (seen.add(x.var()))
					todo.push_back(x.var());
			for (Lit x : sat.bins[neg])
				if (seen.add(x.var()))
					todo.push_back(x.var());
			for (CRef k : occs[pos])
				if (sat.clauses[k].irred())
					for (Lit x : sat.clauses[k].lits())
						if (seen.add(x.var()))
							todo.push_back(x.var());
			for (CRef k : occs[neg])
				if (sat.clauses[k].irred())
					for (Lit x : sat.clauses[k].lits())
						if (seen.add(x.var()))
							todo.push_back(x.var());

			// eliminate the variable
			eliminate(v);
			++nRemovedVariables;
			eliminated[v] = true;

			// recalculate scores of affected variables and prune their
			// occ-lists and implicit binaries
			score[v] = 1000;
			for (int j : todo)
			{
				// prune occ-lists
				auto &oPos = occs[Lit(j, false)];
				util::erase_if(oPos, [this](CRef ci) {
					return sat.clauses[ci].isRemoved();
				});
				auto &oNeg = occs[Lit(j, true)];
				util::erase_if(oNeg, [this](CRef ci) {
					return sat.clauses[ci].isRemoved();
				});

				// prune implicit binaries
				auto &bPos = sat.bins[Lit(j, false)];
				util::erase_if(bPos,
				               [v](Lit other) { return other.var() == v; });
				auto &bNeg = sat.bins[Lit(j, true)];
				util::erase_if(bNeg,
				               [v](Lit other) { return other.var() == v; });

				seen[j] = false;
				score[j] = compute_score(j);
			}

			todo.resize(0);
		}

		// remove learnt clauses that contain eliminated variables
		// TODO: maybe it would be worthwhile to keep at least some
		// resolvents
		//       of learnt clauses (need heuristic based on size/glue/...)
		for (auto [ci, cl] : sat.clauses)
		{
			(void)ci;
			assert(!cl.isRemoved());
			bool elim = false;
			for (Lit a : cl.lits())
				if (eliminated[a.var()])
				{
					elim = true;
					break;
				}
			if (elim)
			{
				assert(!cl.irred()); // irred clauses should already be gone
				cl.remove();
			}
		}

		// renumber (inner variables cant stay in eliminated state)
		std::vector<Lit> trans(sat.varCount());
		int newVarCount = 0;
		for (int i = 0; i < sat.varCount(); ++i)
			if (eliminated[i])
				trans[i] = Lit::elim();
			else
				trans[i] = Lit(newVarCount++, false);
		sat.renumber(trans, newVarCount);

		return nRemovedVariables;
	}
};

} // namespace

int run_variable_elimination(Sat &sat)
{
	if (sat.contradiction)
		return 0;

	util::StopwatchGuard swg(sat.stats.swBVE);
	util::Stopwatch sw;
	sw.start();

	auto bve = BVE(sat);
	int nFound = bve.run();
	fmt::print("c [BVE          {:#6.2f}] removed {} vars\n", sw.secs(),
	           nFound);
	return nFound;
}

} // namespace dawn
