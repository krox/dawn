#include "sat/elimination.h"

#include "fmt/format.h"
#include "sat/clause.h"
#include "sat/propengine.h"
#include "sat/subsumption.h"
#include "util/bit_vector.h"
#include "util/vector.h"
#include <algorithm>
#include <queue>
#include <ranges>
#include <vector>

namespace dawn {

// Todo/Ideas:
//   - Even more on-the-fly reasoning: {binary,long-}subsumption during scoring,
//     more complete BC/RUP/RAT/CCE during clause addition?
//   - in case the resolvent is not tautological, we could trivially determine
//     its size. If it is very small, it might be worthwhile to add it as
//     a learnt clause, even if no variable-elimination takes place.

namespace {

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

} // namespace

// combined BVE and BCE algorithm.
//   * Blocked clauses are not removed, but only re-colored from blue to green.
//     Actual removal only happens when a variable is eliminated.
struct Elimination
{
	// static constexpr int score_always = -500'000'000; // always eliminate
	static constexpr int score_never = 500'000'000; // never eliminate

	Cnf &cnf;
	std::vector<std::vector<CRef>> occs;    // all occurrences
	std::vector<std::vector<CRef>> watches; // one watch per clause
	ImplCache cache;                        // for bin-subsumption/SSR
	EliminationConfig config;

	util::bit_vector eliminated;
	std::vector<int> score;
	int64_t nEliminated = 0, nBCE = 0, nResolvents = 0;
	int64_t nSizeRejected = 0, nBinRejected = 0, nLongRejected = 0;
	int64_t nBinShortened = 0;
	util::Logger log = util::Logger("elimination");
	// the prio-queue contains (score, variable) pairs. Outdated entries
	// are allowed, so we have to check whenever we are about to
	// implement a proposal
	using PII = std::pair<int, int>;
	std::priority_queue<PII, std::vector<PII>, std::greater<PII>> queue;

	util::bit_set dirty; // variables that need to be re-evaluated

	auto occs_all(Lit a)
	{
		return occs[a] | std::views::transform([&](CRef i) -> Clause & {
			       return cnf.clauses[i];
		       }) |
		       std::views::filter(
		           [](Clause const &cl) { return cl.color() != Color::black; });
	}
	auto occs_blue(Lit a)
	{
		return occs[a] | std::views::transform([&](CRef i) -> Clause & {
			       return cnf.clauses[i];
		       }) |
		       std::views::filter(
		           [](Clause const &cl) { return cl.color() == Color::blue; });
	}

	Elimination(Cnf &cnf_, EliminationConfig const &config_)
	    : cnf(cnf_), occs(cnf_.var_count() * 2), watches(cnf_.var_count() * 2),
	      cache(cnf_.bins), config(config_), eliminated(cnf_.var_count()),
	      score(cnf_.var_count())
	{
		for (auto [ci, cl] : cnf.clauses.enumerate())
		{
			assert(cl.size() != 0);
			assert(cl.color() != Color::black);

			std::ranges::sort(cl.lits());
			for (Lit a : cl.lits())
				occs[a].push_back(ci);
			watches[cl[0]].push_back(ci);
		}
	}

	// assumes sorted lits
	static bool is_subset(std::span<const Lit> a, std::span<const Lit> b)
	{
		size_t i = 0, j = 0;
		while (i < a.size() && j < b.size())
		{
			if (a[i] < b[j])
				return false;
			else if (a[i] > b[j])
				++j;
			else
			{
				++i;
				++j;
			}
		}
		return i == a.size();
	}

	// returns true if the clause was actually added. False if it was
	// rejected via subsumption. NOTE: cl might be modified in the process
	bool add_clause(Clause &cl)
	{
		assert(cl.color() != Color::black);

		// hard cutoff for very long reducible clauses
		if (cl.color() != Color::blue && (int)cl.size() > config.green_cutoff)
		{
			nSizeRejected += 1;
			return false;
		}

		// forward subsumption check
		for (Lit a : cl)
			for (CRef i : watches[a])
				if (auto &cl2 = cnf.clauses[i]; cl2.color() != Color::black)
					if (is_subset(cl2.lits(), cl))
					{
						nLongRejected += 1;
						cl2.set_color(max(cl2.color(), cl.color()));
						return false;
					}

		// binary subsumption + binary SSR
		auto s = cl.size();
		cache.normalize(cl);
		if (cl.color() == Color::black)
		{
			nBinRejected += 1;
			return false;
		}
		nBinShortened += s - cl.size();

		// TODO: SSR, (some?) backwards subsumption

		// rare corner case: if a reducible resolvent is binary (or became so
		// after shortening), it will influence scoring (because binaries are
		// implicitly irreducible). This is not captured by the dirtying logic
		// of 'eliminate'. Thus this is handled here.
		if (cl.color() != Color::blue && cl.size() <= 2)
			for (Lit a : cl)
				dirty.add(a.var());

		// actually add the clause
		auto ci = cnf.add_clause(cl.lits(), cl.color());
		if (ci != CRef::undef())
		{
			for (Lit a : cl)
				occs[a].push_back(ci);
			watches[cl[0]].push_back(ci);
		}
		return true;
	}

	// Calculate the score of removing variable v.
	//   - score = #(non-tautological resolvents) - #(removed clauses)
	//   - lower is better
	//   - only considers irreducible clauses in the counting
	//   - also does BCE on the fly
	int compute_score(int v);

	// eliminate a variable: add resolvents, move clauses to extender
	void eliminate(int v);

	// find best variable to eliminate next.
	// returns -1 if no more candidates are available.
	int choose_var();

	// returns number of removed variables
	void run();
};

int Elimination::compute_score(int v)
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
	auto blocked_color = config.discard_blocked ? Color::black : Color::green;

	auto posCount = util::small_vector<int, 32>(occs[pos].size(), 0);
	auto negCount = util::small_vector<int, 32>(occs[neg].size(), 0);
	int totalCount = 0;

	// count all non-tautology blue-blue resolvents
	for (int i = 0; i < (int)occs[pos].size(); ++i)
		if (auto &a = cnf.clauses[occs[pos][i]]; a.color() == Color::blue)
			for (int j = 0; j < (int)occs[neg].size(); ++j)
				if (auto &b = cnf.clauses[occs[neg][j]];
				    b.color() == Color::blue)
					if (!is_resolvent_tautological(a, b))
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
			nBCE++;
			log.debug("removing blocked clause {}, pivot {}", cl, pos);
			for (Lit x : cl)
				dirty.add(x.var());
			cnf.add_rule(cl, pos);
			cl.set_color(blocked_color);
		}
	for (int j = 0; j < (int)occs[neg].size(); ++j)
		if (auto &cl = cnf.clauses[occs[neg][j]];
		    negCount[j] == 0 && cl.color() == Color::blue)
		{
			nBCE++;
			log.debug("removing blocked clause {}, pivot {}", cl, neg);
			for (Lit x : cl)
				dirty.add(x.var());
			cnf.add_rule(cl, neg);
			cl.set_color(blocked_color);
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
void Elimination::eliminate(int v)
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

	log.debug("eliminating variable {} ({}+{} bins, {}+{} occs)", pos,
	          cnf.bins[pos].size(), cnf.bins[neg].size(), occs[pos].size(),
	          occs[neg].size());

	std::vector<Lit> tmp;
	ClauseStorage resolvents;

	// add binary-binary resolvents
	for (Lit x : cnf.bins[pos])
		for (Lit y : cnf.bins[neg])
		{
			if (x == y.neg())
				continue;
			else if (x == y)
				resolvents.add_clause(std::array{x}, Color::blue);
			else
				resolvents.add_clause(std::array{x, y}, Color::blue);
		}

	// add long-binary resolvents
	for (Clause const &cl : occs_all(pos))
		for (Lit x : cnf.bins[neg])
			if (resolvent(tmp, cl.lits(), {x, neg}))
				resolvents.add_clause(tmp, cl.color());
	for (Clause const &cl : occs_all(neg))
		for (Lit x : cnf.bins[pos])
			if (resolvent(tmp, cl.lits(), {x, pos}))
				resolvents.add_clause(tmp, cl.color());

	// add long-long resolvents
	for (Clause const &a : occs_all(pos))
		for (Clause const &b : occs_all(neg))
			if (resolvent(tmp, a.lits(), b.lits()))
				resolvents.add_clause(tmp, min(a.color(), b.color()));

	// remove old long clauses from the problem
	for (Clause &a : occs_all(pos))
	{
		if (a.color() == Color::blue)
			cnf.add_rule(a, pos);
		a.set_color(Color::black);
	}
	for (Clause &a : occs_all(neg))
	{
		if (a.color() == Color::blue)
			cnf.add_rule(a, neg);
		a.set_color(Color::black);
	}

	// remove old binary clauses from the problem
	for (Lit b : cnf.bins[pos])
	{
		erase(cnf.bins[b], pos);
		cnf.add_rule({{pos, b}});
	}
	for (Lit b : cnf.bins[neg])
	{
		erase(cnf.bins[b], neg);
		cnf.add_rule({{neg, b}});
	}
	cnf.bins[pos].resize(0);
	cnf.bins[neg].resize(0);

	// NOTE: Only start adding resolvents after all old clauses are removed.
	// Simplest way to keep the subsumption-logic in add_clause consistent.
	int64_t resolvent_count = 0;
	for (Clause &cl : resolvents.all())
		if (add_clause(cl))
			++resolvent_count;
	nResolvents += resolvent_count;

	log.debug("eliminated variable {}, adding {} resolvents", pos,
	          resolvent_count);
}

// find best variable to eliminate next.
// returns -1 if no more candidates are available.
int Elimination::choose_var()
{
	// recompute all potentially-outdated scores
	// note: this loop effectively does BCE till fixed-point
	while (!dirty.empty())
	{
		int v = dirty.pop();
		score[v] = compute_score(v);
		if (score[v] <= config.growth)
			queue.push({score[v], v});
	}

	while (!queue.empty())
	{
		auto [s, v] = queue.top();
		queue.pop();
		if (!eliminated[v] && score[v] == s)
			return v;
	}
	return -1;
}

// returns number of removed variables
void Elimination::run()
{
	for (int i : cnf.all_vars())
		dirty.add(i);

	while (nEliminated < config.max_eliminations &&
	       nResolvents < config.max_resolvents)
	{
		int v = choose_var();
		if (v == -1)
			break;

		// Consistency check for the scores. Incorrect scores (e.g.
		// forgetting to set the dirty flag) can harm effectiveness a lot
		// without being evident from normal testing.
		// case in point: if a reducible resolvent is binary, that is then
		// considered irreducible (like all binaries), affecting the score.
		assert(score[v] == compute_score(v));

		auto pos = Lit(v, false);
		auto neg = Lit(v, true);

		// determine other variables whose score will have to be
		// recalculated
		for (Lit x : cnf.bins[pos])
			dirty.add(x.var());
		for (Lit x : cnf.bins[neg])
			dirty.add(x.var());
		for (CRef k : occs[pos])
			if (cnf.clauses[k].color() == Color::blue)
				for (Lit x : cnf.clauses[k].lits())
					dirty.add(x.var());
		for (CRef k : occs[neg])
			if (cnf.clauses[k].color() == Color::blue)
				for (Lit x : cnf.clauses[k].lits())
					dirty.add(x.var());

		// eliminate the variable
		eliminate(v);
		score[v] = score_never;
	}

	// remove reducible clauses that contain eliminated variables
	for (auto &cl : cnf.clauses.all())
	{
		bool elim = std::any_of(cl.begin(), cl.end(),
		                        [this](Lit a) { return eliminated[a.var()]; });
		if (elim)
		{
			assert(cl.color() != Color::blue);
			cl.set_color(Color::black);
		}
	}

	log.info("[g={}] found {} blocked clauses, removed {} vars", config.growth,
	         nBCE, nEliminated);
	log.info("added {} resolvents (rejected {} via bin- and {} via long "
	         "subsumption, {} via size). Removed {} lits via otf-ssr.",
	         nResolvents, nBinRejected, nLongRejected, nSizeRejected,
	         nBinShortened);
}

int run_elimination(Cnf &sat, EliminationConfig const &config)
{
	// assert(is_normal_form(sat)); // not strictly necessary

	auto elim = Elimination(sat, config);
	elim.run();

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

int run_blocked_clause_addition(Cnf &sat)
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
