#include "sat/elimination.h"

#include "fmt/format.h"
#include "sat/binary.h"
#include "sat/propengine.h"
#include "util/bit_vector.h"
#include "util/vector.h"
#include <algorithm>
#include <queue>
#include <ranges>
#include <vector>

namespace dawn {

namespace {

// TODO:
//   - wider definition of 'tautology':
//       - full binary closure, or at least some stamp-based approximation
//       - resolutions with (same-sign) overlap can be considered strong enough
//         to be added regardless of eliminations, so they dont count in cost
//         estimation
//       - subsumption by existing (short-ish) clauses?
//       - "covered" clauses?
//   - resolve reducible clauses when eliminating variables. Needs cutoff (or
//     better: on-the-fly subsumption) to keep the number of clauses reasonable.

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
bool is_resolvent_tautological(std::span<const Lit> a, std::span<const Lit> b)
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

// same as above, but also considers resolvents tautolical if they are implied
// by the stamps. Rough approximation of full binary-long subsumption.
[[maybe_unused]] bool is_resolvent_tautological(std::span<const Lit> a,
                                                std::span<const Lit> b,
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

// compute resolvent of a and b.
//   - assumes sorted lits in both clauses, result is also sorted
//   - returns false if the resolvent is tautological
bool resolvent(std::vector<Lit> &r, std::span<const Lit> a,
               std::span<const Lit> b)
{
	for (size_t i = 1; i < a.size(); ++i)
		assert(a[i - 1].var() < a[i].var());
	for (size_t i = 1; i < b.size(); ++i)
		assert(b[i - 1].var() < b[i].var());

	r.resize(0);
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

	assert(count >= 1);

	return count == 1;
}

// same, with binary clause (b,c)
bool resolvent(std::vector<Lit> &r, std::span<const Lit> a,
               std::array<Lit, 2> bc)
{
	// TODO: this is slower than necessary
	assert(bc[0].var() != bc[1].var());
	if (bc[0].var() > bc[1].var())
		std::swap(bc[0], bc[1]);
	return resolvent(r, a, std::span<const Lit>(bc));
}

// combined BVE and BCE algorithm.
//   * Blocked clauses are not removed, but only re-colored from blue to green.
//     Actual removal only happens when a variable is eliminated.
struct Elimination
{
	// static constexpr int score_always = -500'000'000; // always eliminate
	static constexpr int score_never = 500'000'000; // never eliminate

	Cnf &cnf;
	std::vector<std::vector<CRef>> occs;
	EliminationConfig config;

	util::bit_vector eliminated;
	int nEliminated = 0;
	ClauseStorage rules;
	int cutoff;
	util::Logger log = util::Logger("elimination");

	Elimination(Cnf &cnf_, EliminationConfig const &config_)
	    : cnf(cnf_), occs(cnf_.var_count() * 2), config(config_),
	      eliminated(cnf_.var_count()), cutoff(config.growth)
	{
		for (auto [ci, cl] : cnf.clauses.enumerate())
		{
			std::ranges::sort(cl.lits());
			for (Lit a : cl.lits())
				occs[a].push_back(ci);
		}
	}

	void add_clause(std::span<const Lit> cl, Color color)
	{
		assert(color != Color::black);
		auto ci = cnf.add_clause(cl, color);
		if (ci != CRef::undef())
			for (Lit a : cl)
				occs[a].push_back(ci);
	}

	void eliminate_clause(Clause &cl, Lit x)
	{
		assert(cl.color() == Color::blue);
		cl.set_color(Color::black);
		CRef ci = rules.add_clause(cl.lits(), Color::blue);
		assert(ci != CRef::undef());
		rules[ci].move_to_front(x);
	}

	// Calculate the score of removing variable v.
	//   - score = #(non-tautological resolvents) - #(removed clauses)
	//   - lower is better
	//   - only considers irreducible clauses in the counting
	//   - also does BCE on the fly
	int compute_score(int v)
	{
		if (eliminated[v])
			return score_never;

		// eliminating fixed variables would break our implementation.
		// Also pointless anyway.
		for (Lit u : cnf.units)
			if (u.var() == v)
				return score_never;

		auto pos = Lit(v, false);
		auto neg = Lit(v, true);

		auto posCount = util::small_vector<int, 32>(occs[pos].size(), 0);
		auto negCount = util::small_vector<int, 32>(occs[neg].size(), 0);
		int totalCount = 0;

		// count all non-tautology blue-blue resolvents
		for (int i = 0; i < (int)occs[pos].size(); ++i)
			if (auto &a = cnf.clauses[occs[pos][i]]; a.color() == Color::blue)
				for (int j = 0; j < (int)occs[neg].size(); ++j)
					if (auto &b = cnf.clauses[occs[neg][j]];
					    b.color() == Color::blue)
						if (!is_resolvent_tautological(a.lits(), b.lits()))
						{
							++posCount[i];
							++negCount[j];
							++totalCount;
						}

		// count non-tautology long-binary resolvents
		for (int i = 0; i < (int)occs[pos].size(); ++i)
			if (auto &cl = cnf.clauses[occs[pos][i]]; cl.color() == Color::blue)
				for (Lit x : cnf.bins[neg])
					if (!cl.contains(x.neg()))
						++posCount[i];
		for (int j = 0; j < (int)occs[neg].size(); ++j)
			if (auto &cl = cnf.clauses[occs[neg][j]]; cl.color() == Color::blue)
				for (Lit x : cnf.bins[pos])
					if (!cl.contains(x.neg()))
						++negCount[j];

		// blocked clause elimination ("BCE"):
		// remove clauses with only tautology resolvents
		for (int i = 0; i < (int)occs[pos].size(); ++i)
			if (auto &cl = cnf.clauses[occs[pos][i]];
			    posCount[i] == 0 && cl.color() == Color::blue)
			{
				log.info("removing blocked clause {}, pivot {}", cl, pos);
				eliminate_clause(cl, pos);
			}
		for (int j = 0; j < (int)occs[neg].size(); ++j)
			if (auto &cl = cnf.clauses[occs[neg][j]];
			    negCount[j] == 0 && cl.color() == Color::blue)
			{
				log.info("removing blocked clause {}, pivot {}", cl, neg);
				eliminate_clause(cl, neg);
			}

		// compute score
		int score = std::accumulate(posCount.begin(), posCount.end(), 0);
		score -= std::count_if(posCount.begin(), posCount.end(),
		                       [](int i) { return i != 0; });
		score -= std::count_if(negCount.begin(), negCount.end(),
		                       [](int i) { return i != 0; });
		score -= (int)cnf.bins[pos].size() + (int)cnf.bins[neg].size();
		score += (int)(cnf.bins[pos].size() * cnf.bins[neg].size());

		log.trace("score({}) = {}", v + 1, score);

		return score;
	}

	// eliminate a variable: add resolvents, move clauses to extender
	void eliminate(int v)
	{
		assert(!eliminated[v]);
		eliminated[v] = true;
		++nEliminated;

		// I think this might happen in a very contrived case?
		for (Lit a : cnf.units)
			if (a.var() == v)
				throw std::runtime_error("eliminating fixed variable");

		auto pos = Lit(v, false);
		auto neg = Lit(v, true);

		std::vector<Lit> tmp;
		ClauseStorage resolvents;

		// add binary-binary resolvents
		for (Lit x : cnf.bins[pos])
			for (Lit y : cnf.bins[neg])
			{
				if (x == y.neg())
					continue;
				else if (x == y)
					cnf.add_unary(x);
				else
					resolvents.add_clause(std::array{x, y}, Color::blue);
			}

		// add long-binary resolvents
		for (CRef i : occs[pos])
			if (Clause const &cl = cnf.clauses[i]; cl.color() != Color::black)
				for (Lit x : cnf.bins[neg])
					if (resolvent(tmp, cl.lits(), {x, neg}))
						resolvents.add_clause(tmp, cl.color());
		for (CRef i : occs[neg])
			if (Clause const &cl = cnf.clauses[i]; cl.color() != Color::black)
				for (Lit x : cnf.bins[pos])
					if (resolvent(tmp, cl.lits(), {x, pos}))
						resolvents.add_clause(tmp, cl.color());

		// add long-long resolvents
		for (CRef i : occs[pos])
			if (Clause const &a = cnf.clauses[i]; a.color() == Color::blue)
				for (CRef j : occs[neg])
					if (Clause const &b = cnf.clauses[j];
					    b.color() == Color::blue)
						if (resolvent(tmp, a.lits(), b.lits()))
							resolvents.add_clause(tmp,
							                      min(a.color(), b.color()));

		// NOTE: the temporary 'resolvents' storage is necessary. Adding the
		// clause during above directly is invalid for memory management
		// reasons.
		for (Clause const &cl : resolvents.all())
			add_clause(cl.lits(), cl.color());

		// remove old long clauses from the problem
		for (CRef i : occs[pos])
			if (Clause &a = cnf.clauses[i]; a.color() == Color::blue)
				eliminate_clause(a, pos);
		for (CRef i : occs[neg])
			if (Clause &a = cnf.clauses[i]; a.color() == Color::blue)
				eliminate_clause(a, neg);
		// NOTE: no need to prune occ-lists. Reducible colors are ignored

		// remove old binary clauses from the problem
		for (Lit b : cnf.bins[pos])
		{
			erase(cnf.bins[b], pos);
			rules.add_binary(pos, b);
		}
		for (Lit b : cnf.bins[neg])
		{
			erase(cnf.bins[b], neg);
			rules.add_binary(neg, b);
		}
		cnf.bins[pos].resize(0);
		cnf.bins[neg].resize(0);
	}

	// returns number of removed variables
	void run()
	{
		// the prio-queue contains (score, variable) pairs. Outdated entries
		// are allowed, so we have to check whenever we are about to
		// implement a proposal
		using PII = std::pair<int, int>;
		std::priority_queue<PII, std::vector<PII>, std::greater<PII>> queue;

		// compute elimination scores of of all variables
		auto score = std::vector<int>(cnf.var_count());
		for (int i : cnf.all_vars())
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
		auto seen = util::bit_vector(cnf.var_count());

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
			// TODO: second check fails. I think it is because BCE does not
			// trigger score recalculation
			assert(score[v] == s /*&& s == compute_score(v)*/);

			// determine other variables whose score will have to be
			// recalculated
			for (Lit x : cnf.bins[pos])
				if (seen.add(x.var()))
					todo.push_back(x.var());
			for (Lit x : cnf.bins[neg])
				if (seen.add(x.var()))
					todo.push_back(x.var());
			for (CRef k : occs[pos])
				if (cnf.clauses[k].color() == Color::blue)
					for (Lit x : cnf.clauses[k].lits())
						if (seen.add(x.var()))
							todo.push_back(x.var());
			for (CRef k : occs[neg])
				if (cnf.clauses[k].color() == Color::blue)
					for (Lit x : cnf.clauses[k].lits())
						if (seen.add(x.var()))
							todo.push_back(x.var());

			// eliminate the variable
			log.debug("eliminating variable inner={}, score={}", Lit(v, false),
			          score[v]);
			eliminate(v);
			score[v] = score_never;

			// recalculate scores of affected variables
			for (int j : todo)
			{
				seen[j] = false;
				score[j] = compute_score(j);
				if (score[j] <= cutoff)
					queue.push({score[j], j});
			}
			todo.resize(0);
		}

		// remove reducible clauses that contain eliminated variables
		for (auto &cl : cnf.clauses.all())
		{
			bool elim = std::any_of(cl.begin(), cl.end(), [this](Lit a) {
				return eliminated[a.var()];
			});
			if (elim)
			{
				assert(cl.color() != Color::blue);
				cl.set_color(Color::black);
			}
		}

		log.info("removed {} vars", nEliminated);
	}
};
} // namespace

int run_elimination(Sat &sat, EliminationConfig const &config)
{
	// assert(is_normal_form(sat)); // not strictly necessary

	auto elim = Elimination(sat, config);
	elim.run();

	// move rules to extender
	for (auto &cl : elim.rules.all())
	{
		for (Lit &a : cl.lits())
			a = sat.to_outer(a);
		sat.extender.add_rule(cl);
	}
	elim.rules.clear();

	// renumber (inner variables cant stay in eliminated state)
	std::vector<Lit> trans(sat.var_count());
	int newVarCount = 0;
	for (int i : sat.all_vars())
		if (elim.eliminated[i])
			trans[i] = Lit::elim();
		else
			trans[i] = Lit(newVarCount++, false);
	sat.renumber(trans, newVarCount);

	return elim.nEliminated;
}

int run_blocked_clause_addition(Sat &sat)
{
	assert(is_normal_form(sat));
	auto log = util::Logger("BCA");

	// TODO: make BVA play nicely with colors
	for (auto &cl : sat.clauses.all())
		if (cl.color() != Color::blue)
			cl.set_color(Color::black);
	sat.clauses.prune_black();

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
