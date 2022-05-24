#include "sat/elimination.h"

#include "fmt/format.h"
#include "sat/binary.h"
#include "sat/propengine.h"
#include "util/bit_vector.h"
#include "util/vector.h"
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
 *       its size. If it is very small, it might be worthwhile to add it as
 *       a learnt clause, even if no variable-elimination takes place.
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

bool is_resolvent_tautological(util::span<const Lit> a, util::span<const Lit> b,
                               Stamps const &stamps)
{
	util::static_vector<Lit, 255> r;
	if (a.size() + b.size() > r.max_size())
		return false;

	int count = 0;

	for (size_t i = 0, j = 0; i < a.size() && j < b.size();)
	{
		if (a[i].var() < b[j].var())
			r.push_back(a[i++]);
		else if (a[i].var() > b[j].var())
			r.push_back(b[j++]);
		else
		{
			if (a[i] == b[j].neg())
				if (++count >= 2)
					return true;
			r.push_back(a[i]);
			++i;
			++j;
		}
	}

	for (Lit x : r)
		for (Lit y : r)
			if (x.var() != y.var() && stamps.has_path(x.neg(), y))
				return true;

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
	// score = (non-tautology resolvent) - (removed clauses)
	//       | or one of the special cases
	using Score = int;
	static constexpr Score score_0n = -500'000'000;   // pure/unused variable
	static constexpr Score score_11 = -400'000'000;   // 1+1 occurence
	static constexpr Score score_1n = -300'000'000;   // 1+n occurence
	static constexpr Score score_never = 500'000'000; // never eliminate

	// NOTE:
	//   - all clauses are sorted (only irreds if config.irred_only = true)
	//     (this property is maintained in the resolvent() functions)
	//   - occ-lists only contain non-removed clauses
	//     (this property is restored after each variable elimination)

	Sat &sat;
	EliminationConfig config;
	using occs_t = std::vector<std::vector<CRef>>;
	occs_t occs;
	util::bit_vector eliminated;
	Score cutoff;
	int nEliminated = 0;
	Logger log{"BVE"};

	BVE(Sat &sat_, EliminationConfig const &config_)
	    : sat(sat_), config(config_), occs(2 * sat_.var_count()),
	      eliminated(sat_.var_count())
	{
		cutoff = config.level == 0   ? score_0n
		         : config.level == 1 ? score_11
		         : config.level == 2 ? score_1n
		         : config.level == 5 ? config.growth
		                             : score_never - 1;
		// sort lits and create occ-lists
		for (auto [ci, cl] : sat.clauses.enumerate())
		// if (!config.irred_only || cl.irred())
		{
			assert(cl.irred() && !cl.isRemoved());
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
	int compute_score(int v) const
	{
		// never eliminate a variable that has a unit clause (could break our
		// implementaion of resolution and would be stupid anyway)
		for (Lit u : sat.units)
			if (u.var() == v)
				return score_never;

		auto pos = Lit(v, false);
		auto neg = Lit(v, true);
		auto occsPos = (int)occs[pos].size() + (int)sat.bins[pos].size();
		auto occsNeg = (int)occs[neg].size() + (int)sat.bins[neg].size();

		// priority for extremely nice cases
		if (occsPos == 0 || occsNeg == 0)
			return score_0n;
		if (occsPos == 1 && occsNeg == 1)
			return score_11;
		if (occsPos == 1 || occsNeg == 1)
			return score_1n;

		// its not worth scoring variables with many occurences
		// (this cutoff is suggested in minisat.se/downloads/SatELite.pdf)
		if (occsPos > 10 && occsNeg > 10)
			return score_never;

		int score = -(occsPos + occsNeg);

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
					if (++score > cutoff)
						return score_never;
		for (Lit x : sat.bins[pos])
			for (CRef i : occs[neg])
				if (!sat.clauses[i].contains(x.neg()))
					if (++score > cutoff)
						return score_never;

		// long-long resolvents
		for (CRef i : occs[pos])
			for (CRef j : occs[neg])
				if (!is_resolvent_tautological(sat.clauses[i], sat.clauses[j]))
					if (++score > cutoff)
						return score_never;

		return score;
	}

	// add clause to sat and update occ-lists
	void add_clause(util::span<const Lit> cl, bool irred)
	{
		CRef ci = sat.add_clause(cl, irred);
		if (ci == CRef::undef()) // implicit binary clause (or empty/unary?)
			return;

		for (Lit a : cl)
			occs[a].push_back(ci);
	}

	// add binary clause
	void add_clause(Lit a, Lit b)
	{
		if (a == b)
			sat.add_unary(a);
		else if (a == b.neg())
		{} // tautology
		else
			sat.add_binary(a, b);
	}

	// eliminate a variable (add resolents, move clauses to extender)
	void eliminate(int v)
	{
		++nEliminated;

		auto pos = Lit(v, false);
		auto neg = Lit(v, true);

		// add binary-binary resolvents
		for (Lit x : sat.bins[pos])
			for (Lit y : sat.bins[neg])
				add_clause(x, y);

		// add long-binary resolvents
		for (CRef i : occs[pos])
			for (Lit x : sat.bins[neg])
				if (auto &cl = sat.clauses[i]; !cl.contains(x.neg()))
					add_clause(resolvent(cl, x, neg), cl.irred());
		for (CRef i : occs[neg])
			for (Lit x : sat.bins[pos])
				if (auto &cl = sat.clauses[i]; !cl.contains(x.neg()))
					add_clause(resolvent(cl, x, pos), cl.irred());

		// add long-long resolvents
		for (CRef i : occs[pos])
			for (CRef j : occs[neg])
			{
				auto &a = sat.clauses[i];
				auto &b = sat.clauses[j];
				if (!is_resolvent_tautological(a, b))
					add_clause(resolvent(a, b), a.irred() || b.irred());
			}

		// remove old long clauses from the problem
		std::vector<std::vector<Lit>> removed_clauses;
		for (CRef i : occs[pos])
		{
			Clause &cl = sat.clauses[i];
			assert(cl.irred() && !cl.isRemoved());
			removed_clauses.emplace_back(cl.begin(), cl.end());
			cl.remove();
		}
		for (CRef i : occs[neg])
		{
			Clause &cl = sat.clauses[i];
			assert(cl.irred() && !cl.isRemoved());
			removed_clauses.emplace_back(cl.begin(), cl.end());
			cl.remove();
		}
		occs[pos].resize(0);
		occs[neg].resize(0);

		// remove old binary clauses from the problem
		for (Lit b : sat.bins[pos])
			removed_clauses.push_back({pos, b});
		for (Lit b : sat.bins[neg])
			removed_clauses.push_back({neg, b});
		sat.bins[pos].resize(0);
		sat.bins[neg].resize(0);

		// add removed clauses to the extender
		//     * renumber 'inner' to 'outer'
		//     * move eliminated variable to front
		for (auto &cl : removed_clauses)
		{
			for (Lit &a : cl)
				if (a.var() == v)
					std::swap(a, cl[0]);
			for (Lit &a : cl)
				a = sat.to_outer(a);
			sat.extender.add_rule(cl);
		}
	}

	/** returns number of removed variables */
	void run()
	{
		// the prio-queue contains (score, variable) pairs. Outdated entries
		// are allowed, so we have to check whenever we are about to
		// implement a proposal
		using PII = std::pair<int, int>;
		std::priority_queue<PII, std::vector<PII>, std::greater<PII>> queue;

		// compute elimination scores of of all variables
		auto score = std::vector<int>(sat.var_count());
		for (int i : sat.all_vars())
		{
			score[i] = compute_score(i);
			if (score[i] <= cutoff)
				queue.push({score[i], i});
		}

		// early-out if nothing is happening
		if (queue.empty())
			return;

		// temporaries
		std::vector<int> todo;
		auto seen = util::bit_vector(sat.var_count());

		while (!queue.empty() && nEliminated < config.max_eliminations)
		{
			auto [s, v] = queue.top();
			auto pos = Lit(v, false);
			auto neg = Lit(v, true);
			queue.pop();
			assert(s <= cutoff);

			// outdated proposal -> skip
			if (eliminated[v] || score[v] != s)
				continue;

			assert(score[v] == s && s == compute_score(v));

			// determine other variables whose score will have to be
			// recalculated
			for (Lit x : sat.bins[pos])
				if (seen.add(x.var()))
					todo.push_back(x.var());
			for (Lit x : sat.bins[neg])
				if (seen.add(x.var()))
					todo.push_back(x.var());
			for (CRef k : occs[pos])
				if (!config.irred_only || sat.clauses[k].irred())
					for (Lit x : sat.clauses[k].lits())
						if (seen.add(x.var()))
							todo.push_back(x.var());
			for (CRef k : occs[neg])
				if (!config.irred_only || sat.clauses[k].irred())
					for (Lit x : sat.clauses[k].lits())
						if (seen.add(x.var()))
							todo.push_back(x.var());

			// eliminate the variable
			log.debug("eliminating variable i={}, o={}, score={}",
			          Lit(v, false), sat.to_outer(Lit(v, false)), score[v]);
			eliminate(v);
			eliminated[v] = true;
			score[v] = score_never;

			// recalculate scores of affected variables and prune their
			// occ-lists and implicit binaries

			for (int j : todo)
			{
				// prune occ-lists
				util::erase_if(occs[Lit(j, false)], [this](CRef ci) {
					return sat.clauses[ci].isRemoved();
				});
				util::erase_if(occs[Lit(j, true)], [this](CRef ci) {
					return sat.clauses[ci].isRemoved();
				});

				// prune implicit binaries
				util::erase_if(sat.bins[Lit(j, false)],
				               [v](Lit other) { return other.var() == v; });
				util::erase_if(sat.bins[Lit(j, true)],
				               [v](Lit other) { return other.var() == v; });

				seen[j] = false;
				score[j] = compute_score(j);
			}

			todo.resize(0);
		}

		// remove learnt clauses that contain eliminated variables
		// TODO: maybe it would be worthwhile to keep at least some
		// resolvents as learnt clauses (need heuristic based on size/glue/...)
		for (auto &cl : sat.clauses.all())
		{
			bool elim = false;
			for (Lit a : cl.lits())
				if (eliminated[a.var()])
				{
					elim = true;
					break;
				}
			if (elim)
			{
				// considered clauses should already be gone
				assert(!config.irred_only && !cl.irred());
				cl.remove();
			}
		}

		// renumber (inner variables cant stay in eliminated state)
		std::vector<Lit> trans(sat.var_count());
		int newVarCount = 0;
		for (int i : sat.all_vars())
			if (eliminated[i])
				trans[i] = Lit::elim();
			else
				trans[i] = Lit(newVarCount++, false);
		sat.renumber(trans, newVarCount);
	}
};

struct BCE
{
	/**
	 * NOTE:
	 *   - all irreducible clauses in sat are sorted
	 *     (this property is maintained in the resolvent() functions)
	 *   - occ-lists contain exactly the non-removed irreduble clauses
	 *     (this property is restored after each variable elimination)
	 */
	Sat &sat;
	Stamps stamps;
	using occs_t = std::vector<std::vector<CRef>>;
	occs_t occs;

	BCE(Sat &sat_) : sat(sat_), stamps(sat), occs(2 * sat_.var_count())
	{
		// sort lits and create occ-lists
		for (auto [ci, cl] : sat.clauses.enumerate())
			if (cl.irred())
			{
				std::sort(cl.lits().begin(), cl.lits().end());
				for (Lit a : cl.lits())
					occs[a].push_back(ci);
			}
	}

	int run_on_variable(int v)
	{
		// if there is a unit -> do nothing (could break our
		// implementaion of resolution and would be stupid anyway)
		for (Lit u : sat.units)
			if (u.var() == v)
				return 0;
		int nFound = 0;
		auto pos = Lit(v, false);
		auto neg = Lit(v, true);

		// its not worth trying with variables with many occurences
		if (occs[pos].size() + sat.bins[pos].size() > 10 &&
		    occs[neg].size() + sat.bins[neg].size() > 10)
			return 0;

		for (CRef i : occs[pos]) // try to eliminate i with variable v(pos)
		{
			// already removed (on a different variable)
			if (sat.clauses[i].isRemoved())
				continue;

			// check for (non-)tautologies
			for (Lit x : sat.bins[neg])
				if (!sat.clauses[i].contains(x.neg()))
					goto next;
			for (CRef j : occs[neg])
			{

				if (sat.clauses[j].isRemoved())
					continue;
				if (is_resolvent_tautological(sat.clauses[i].lits(),
				                              sat.clauses[j].lits(), stamps))
					continue;

				// non-tautology found -> no BCE for us :(
				goto next;
			}

			// remove clause and add it to the extender
			{
				nFound += 1;
				auto cl = std::vector<Lit>(sat.clauses[i].begin(),
				                           sat.clauses[i].end());
				sat.clauses[i].remove();

				for (Lit &a : cl)
					if (a.var() == v)
						std::swap(a, cl[0]);
				for (Lit &a : cl)
					a = sat.to_outer(a);
				sat.extender.add_rule(cl);
			}

		next:;
		}

		return nFound;
	}

	// returns number of removed variables
	int run()
	{
		int nFound = 0;
		for (int v : sat.all_vars())
			nFound += run_on_variable(v);
		return nFound;
	}
};

} // namespace

int run_elimination(Sat &sat, EliminationConfig const &config)
{
	// assert(is_normal_form(sat)); // not strictly necessary

	util::StopwatchGuard swg(sat.stats.swBVE);

	auto bve = BVE(sat, config);
	bve.run();
	bve.log.info("removed {} vars", bve.nEliminated);
	return bve.nEliminated;
}

int run_blocked_clause_elimination(Sat &sat)
{
	assert(is_normal_form(sat)); // not strictly necessary...

	util::StopwatchGuard swg(sat.stats.swBCE);
	auto log = Logger("BCE");

	auto bce = BCE(sat);
	int nFound = bce.run();
	if (nFound)
		nFound += bce.run();
	log.info("removed {} clauses", nFound);
	return nFound;
}

int run_blocked_clause_addition(Sat &sat)
{
	assert(is_normal_form(sat));
	auto log = Logger("BCA");

	for (auto &cl : sat.clauses.all())
		if (!cl.irred())
			cl.remove();

	auto p = PropEngineLight(sat);
	auto seen = util::bit_vector(sat.var_count() * 2);
	int nFound = 0;
	bool failing_lit_found = false;
	for (Lit a : sat.all_lits())
	{
		if (p.assign[a] || p.assign[a.neg()])
			continue;

		// skip non-roots. not really sufficint, but some optimization is needed
		// if (sat.bins[a.neg()].empty() || !sat.bins[a].empty())
		//	continue;

		// fmt::print("c propagating {}\n", a);
		p.mark();
		p.propagate(a);
		if (p.conflict)
		{
			// a is a failing literal. we cant do any reason-analysis here, so
			// we just learn '-a' and skip out. Probably should be smarter...
			failing_lit_found = true;
			p.unroll();
			sat.add_unary(a.neg());
			break;
		}

		// mark literals that might eventually need to be set from here
		seen.clear();
		for (auto &cl : sat.clauses.all())
			if (!p.assign.satisfied(cl))
				for (Lit x : cl)
					seen[x] = true;

		for (Lit b : sat.all_lits())
		{
			if (p.assign[b] || p.assign[b.neg()])
				continue;
			if (seen[b])
				continue;

			for (Lit x : sat.bins[b])
				if (!p.assign[x])
					goto next;

			nFound++;
			sat.add_binary(a.neg(), b.neg());
			{
				auto r = p.propagate(b.neg());
				assert(r == 1);
			}
			assert(!p.conflict);

		next:;
		}

		p.unroll();
	}

	log.info("added {} bins{}\n", nFound,
	         failing_lit_found ? " (quit early due to failing literal)" : "");
	return nFound;
}

} // namespace dawn
