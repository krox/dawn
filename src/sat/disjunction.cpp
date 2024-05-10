#include "sat/disjunction.h"

#include "util/bit_vector.h"
#include "util/hash_map.h"
#include "util/logging.h"
#include <queue>
#include <utility>

namespace dawn {

namespace {

/** does NOT clear 'seen' */
int markImplied(Sat const &sat, util::bit_vector &seen, Lit root)
{
	assert((int)seen.size() == sat.var_count() * 2);
	if (seen[root])
		return 0;

	std::vector<Lit> todo;
	int count = 1;
	seen[root] = true;
	todo.push_back(root);

	while (!todo.empty())
	{
		Lit a = todo.back();
		todo.pop_back();
		for (Lit b : sat.bins[a.neg()])
			if (!seen[b])
			{
				count += 1;
				seen[b] = true;
				todo.push_back(b);
			}
	}
	return count;
}

} // namespace

int makeDisjunctions(Sat &sat)
{
	auto log = util::Logger("BVA");

	int minOccs = 10; // arbitrary cutoff. should be configurable
	int nFound = 0;

	// helper function
	using Pair = std::pair<Lit, Lit>;
	auto sort = [](Pair pair) -> Pair {
		if (pair.first < pair.second)
			return pair;
		else
			return {pair.second, pair.first};
	};

	// occ-lists per pair of literals
	util::hash_map<Pair, std::vector<CRef>> pairOccs;
	for (auto [ci, cl] : sat.clauses.enumerate())
		if (cl.color == Color::blue || cl.size() <= 8)
			for (int i = 0; i < cl.size(); ++i)
				for (int j = i + 1; j < cl.size(); ++j)
					pairOccs[sort({cl[i], cl[j]})].push_back(ci);

	// build priority queue of pairs to replace
	util::hash_map<Pair, int> pairCount;
	std::priority_queue<std::pair<int, Pair>> queue;
	for (auto &[pair, occs] : pairOccs)
	{
		if ((int)occs.size() < minOccs)
			continue;
		pairCount[pair] = (int)occs.size();
		queue.push({(int)occs.size(), pair});
	}

	// greedily replace pairs that occur most often.
	// NOTE: by replacing one pair, other related pairs can decrease in
	//       occurance, but never increase. And new pairs using the new
	//       variable come into being of course.
	// NOTE: we update the 'pairCount' but dont update the 'pairOccs'
	while (!queue.empty())
	{
		auto [count, pair] = queue.top();
		queue.pop();

		// outdated candidate -> skip for now (re-add for later)
		if (int newCount = pairCount[pair]; newCount != count)
		{
			assert(newCount < count); // can only decrease
			if (newCount >= minOccs)
				queue.push({newCount, pair});
			continue;
		}

		nFound += 1;

		// add new variable "a <-> pair.first v pair.second"
		Lit a = Lit(sat.add_var(), false);
		sat.add_binary(a, pair.first.neg());
		sat.add_binary(a, pair.second.neg());
		sat.add_ternary(a.neg(), pair.first, pair.second, Color::blue);

		// replace all the occurances of the pair
		int replaced = 0;
		for (CRef ci : pairOccs[pair])
		{
			// check of occurance is still valid
			auto &cl = sat.clauses[ci];
			if (!cl.remove_litarals(pair.first, pair.second))
				continue;
			replaced += 1;

			// update occurance of other pairs
			for (Lit l : sat.clauses[ci])
			{
				pairCount[sort({l, pair.first})] -= 1;
				pairCount[sort({l, pair.second})] -= 1;

				pairCount[sort({l, a})] += 1;
				pairOccs[sort({l, a})].push_back(ci);
			}

			sat.clauses[ci].add_literal_unchecked(a);

			// TODO: add new pairs to queue
		}
		assert(replaced == pairCount[pair]);
	}

	// cleanup
	for (auto &cl : sat.clauses.all())
	{
		if (cl.size() >= 3)
			continue;
		if (cl.size() == 2)
			sat.add_binary(cl[0], cl[1]);
		else if (cl.size() == 1)
			sat.add_unary(cl[0]);
		else
			assert(false);
		cl.color = Color::black;
	}
	sat.clauses.prune_black();

	log.info("added {} vars", nFound);
	return nFound;
}

void substituteDisjunctions(Sat &sat)
{
	// build occ lists (per lit)
	auto occs = std::vector<std::vector<CRef>>(sat.var_count() * 2);
	for (auto [ci, cl] : sat.clauses.enumerate())
		for (Lit a : cl.lits())
			occs[a].push_back(ci);

	// look for definitions a <=> b1 v b2 v ... v bn
	int count = 0;
	auto seen = util::bit_vector(2 * sat.var_count());
	for (Lit a : sat.all_lits())
	{
		seen.clear();
		markImplied(sat, seen, a.neg());

		for (CRef ci : occs[a.neg()])
		{
			Clause const &cl = sat.clauses[ci];
			// std::cout << cl << std::endl;
			for (Lit b : cl.lits())
				if (!seen[b.neg()])
					goto next_clause;
			fmt::print("found one!!!\n");
			++count;
		next_clause:;
		}
	}

	fmt::print("c found {} disjunctions\n", count);
}

} // namespace dawn
