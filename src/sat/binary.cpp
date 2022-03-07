#include "sat/binary.h"

#include "util/unionfind.h"
#include <algorithm>
#include <vector>

namespace dawn {

namespace {

class Tarjan
{
  public:
	Sat &sat;
	util::bit_vector visited;
	std::vector<int> back;
	std::vector<Lit> stack;
	int cnt = 0;
	std::vector<Lit> comp;
	std::vector<Lit> equ;
	int nComps = 0; // number of SCC's

	Tarjan(Sat &sat)
	    : sat(sat), visited(sat.varCount() * 2), back(sat.varCount() * 2, 0),
	      equ(sat.varCount(), Lit::undef())
	{}

	void dfs(Lit v)
	{
		if (visited[v])
			return;
		visited[v] = true;

		int x = back[v] = cnt++;

		stack.push_back(v);

		for (Lit w : sat.bins[v.neg()])
		{
			dfs(w);
			x = std::min(x, back[w]);
		}

		if (x < back[v])
		{
			back[v] = x;
			return;
		}

		comp.resize(0);

		while (true)
		{
			Lit t = stack.back();
			stack.pop_back();
			back[t] = 999999999;
			comp.push_back(t);
			if (t == v)
				break;
		}

		std::sort(comp.begin(), comp.end());
		if (comp[0].sign() == true)
			return;

		if (comp.size() >= 2 && comp[0] == comp[1].neg())
		{
			sat.addEmpty();
			return;
		}

		for (auto l : comp)
		{
			assert(equ[l.var()] == Lit::undef());
			equ[l.var()] = Lit(nComps, l.sign());
		}

		nComps++;
	}
};

} // namespace

int runSCC(Sat &sat)
{
	if (sat.contradiction)
		return 0;

	auto tarjan = Tarjan(sat);

	// run tarjan
	for (int i = 0; i < sat.varCount() * 2 && !sat.contradiction; ++i)
		tarjan.dfs(Lit(i));

	// contradiction found -> don't bother to renumber (also equ[] is not fully
	// built)
	if (sat.contradiction)
		return 1;

	int nFound = sat.varCount() - tarjan.nComps;

	// no equivalences -> quit
	if (nFound == 0)
		return 0;

	// otherwise renumber
	sat.renumber(tarjan.equ, tarjan.nComps);
	return nFound;
}

void printBinaryStats(Sat const &sat)
{
	int nIsolated = 0; // vertices with no binary clauses
	int nRoots = 0;    // vertices without incoming edges
	int nSinks = 0;    // vertices without outgoing edges
	int nFrom = 0;     // vertices with >=2 outging edges
	int nTo = 0;       // vertices with >= 2 incoming edges

	for (int i = 0; i < 2 * sat.varCount(); ++i)
	{
		Lit a = Lit(i);
		if (sat.bins[a.neg()].empty() && sat.bins[a].empty())
		{
			++nIsolated;
			continue;
		}

		if (sat.bins[a.neg()].empty())
			++nSinks;
		if (sat.bins[a].empty())
			++nRoots;
		if (sat.bins[a.neg()].size() >= 2)
			++nFrom;
		if (sat.bins[a].size() >= 2)
			++nTo;
	}

	// sanity check the symmetry of the graph
	assert(nIsolated % 2 == 0);
	assert(nRoots == nSinks);
	assert(nFrom == nTo);

	int nVertices = sat.varCount() * 2 - nIsolated;
	fmt::print("c vars with binaries: {} ({:.2f} GiB for transitive closure)\n",
	           nVertices / 2,
	           (double)nVertices * nVertices * 8 / 1024 / 1024 / 1024);
	fmt::print("c binary roots: {}\n", nRoots);
	fmt::print(
	    "c non-trivial nodes: 2 x {} ({:.2f} GiB for transitive closure)\n",
	    nFrom, (double)nFrom * nFrom / 8 / 1024 / 1024 / 1024);

	auto uf = util::UnionFind(sat.varCount());
	for (int i = 0; i < 2 * sat.varCount(); ++i)
	{
		Lit a = Lit(i);
		for (auto b : sat.bins[a])
			uf.join(a.var(), b.var());
	}

	auto top = TopOrder(sat);
	fmt::print("c acyclic: {}\n", top.valid());

	// roots have level=0, increasing from there
	// height = 1 + max(level)
	auto level = std::vector<int>(2 * sat.varCount());
	auto height = std::vector<int>(sat.varCount());
	for (Lit a : top.lits())
	{
		for (Lit b : sat.bins[a])
		{
			if (top.valid())
				assert(top.order()[b.neg()] < top.order()[a]);
			level[a] = std::max(level[a], 1 + level[b.neg()]);
		}
		height[uf.root(a.var())] =
		    std::max(height[uf.root(a.var())], 1 + level[a]);
	}
	std::vector<std::pair<int, int>> comps;

	for (int i = 0; i < sat.varCount(); ++i)
		if (uf.root(i) == i)
			if (uf.compSize(i) > 1)
				comps.push_back({uf.compSize(i), height[i]});
	std::sort(comps.begin(), comps.end(), std::greater<>());

	for (int i = 0; i < (int)comps.size() && i < 10; ++i)
		fmt::print("c size = {}, height = {}\n", comps[i].first,
		           comps[i].second);
	if (comps.size() > 10)
		fmt::print("c (skipping {} smaller non-trivial components)\n",
		           comps.size() - 10);
}

void runBinaryReduction(Sat &sat)
{
	util::Stopwatch sw;
	sw.start();

	auto top = TopOrder(sat);
	if (!top.valid()) // require acyclic
		throw std::runtime_error("tried to run TBR without SCC first");

	// sort clauses by topological order
	for (int i = 0; i < sat.varCount() * 2; ++i)
	{
		auto a = Lit(i);
		auto &bins = sat.bins[a.neg()];

		std::sort(bins.begin(), bins.end(), [&top](Lit a, Lit b) -> bool {
			return top.order(a) < top.order(b);
		});

		bins.erase(std::unique(bins.begin(), bins.end()), bins.end());

		for (int j = 0; j < (int)bins.size(); ++j)
		{
			assert(top.order(Lit(i)) < top.order(bins[j]));
			assert(j == 0 || top.order(bins[j - 1]) < top.order(bins[j]));
		}
	}

	// start transitive reduction from pretty much all places
	auto seen = util::bit_vector(2 * sat.varCount());
	auto stack = std::vector<Lit>{};
	int nFound = 0;
	int64_t propCount = 0;
	for (int i = 0; i < sat.varCount() * 2; ++i)
	{
		auto a = Lit(i);
		if (sat.bins[a.neg()].size() < 2)
			continue;

		seen.clear();
		assert(stack.empty());
		erase_if(sat.bins[a.neg()], [&](Lit b) {
			// if b is already seen then (a->b) is redundant
			if (seen[b])
			{
				nFound += 1;
				return true;
			}

			// otherwise mark b and all its implications
			stack.push_back(b);
			seen[b] = true;
			while (!stack.empty())
			{
				Lit c = stack.back();
				stack.pop_back();
				// fmt::print("pop {} ({} remain)\n", c.toDimacs(),
				// stack.size());
				for (Lit d : sat.bins[c.neg()])
					if (!seen[d])
					{
						seen[d] = true;
						stack.push_back(d);

						propCount++;
					}
			}
			return false;
		});
	}
	assert(nFound % 2 == 0);
	fmt::print("c [TBR          {:#6.2f}] removed {} redundant binaries (using "
	           "{:.2f}M props)\n",
	           sw.secs(), nFound / 2, propCount / 1024. / 1024.);
}

} // namespace dawn
