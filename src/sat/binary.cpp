#include "sat/binary.h"

#include "sat/logging.h"
#include "util/unionfind.h"
#include <algorithm>
#include <vector>

namespace dawn {

ImplicationGraph::ImplicationGraph(Cnf const &cnf) : bins(cnf.var_count() * 2)
{
	for (Lit a : cnf.all_lits())
		for (Lit b : cnf.bins[a])
			if (a < b)
			{
				bins[a].push_back(b);
				bins[b].push_back(a);
			}
}

namespace {
void top_order_dfs(Lit a, TopOrder &r, ImplicationGraph const &g)
{
	if (r.order[a] >= 0)
		return;
	if (r.order[a] == -2)
	{
		r.valid = false;
		return;
	}
	assert(r.order[a] == -1);
	r.order[a] = -2;
	for (Lit b : g[a])
		top_order_dfs(b.neg(), r, g);
	r.order[a] = (int)r.lits.size();
	r.lits.push_back(a);
}
} // namespace

TopOrder::TopOrder(ImplicationGraph const &g) : valid(true)
{
	order.resize(2 * g.var_count(), -1);
	lits.reserve(2 * g.var_count());

	for (int i = 0; i < 2 * g.var_count(); ++i)
		top_order_dfs(Lit(i), *this, g);
	assert((int)lits.size() == 2 * g.var_count());
}

namespace {
void stamps_dfs(Lit a, Stamps &r, int &time, ImplicationGraph const &g)
{
	if (r.start[a] != -1)
		return;
	r.start[a] = time++;
	for (Lit b : g[a.neg()])
		stamps_dfs(b, r, time, g);
	r.end[a] = time++;
}
} // namespace

Stamps::Stamps(Cnf const &cnf)
    : start(cnf.var_count() * 2, -1), end(cnf.var_count() * 2, -1)
{
	// Sort binaries by topological order.
	// Not strictly necessary, but should improve effectivity.
	auto g = ImplicationGraph(cnf);
	auto top = TopOrder(g);
	if (!top.valid)
		throw std::runtime_error(
		    "tried to compute stamps with non-acyclic graph");
	auto cmp = [&top](Lit a, Lit b) { return top.order[a] < top.order[b]; };
	for (auto &bs : g.bins)
		std::sort(bs.begin(), bs.end(), cmp);

	int time = 0;
	for (Lit a : top.lits)
		stamps_dfs(a, *this, time, g);
	assert(time == 4 * cnf.var_count());
}

namespace {
class Tarjan
{
  public:
	ImplicationGraph const &g;
	util::bit_vector visited;
	std::vector<int> back;
	std::vector<Lit> stack;
	int cnt = 0;
	std::vector<Lit> comp;
	std::vector<Lit> equ;
	int nComps = 0; // number of SCC's

	Tarjan(ImplicationGraph const &g)
	    : g(g), visited(g.var_count() * 2), back(g.var_count() * 2, 0),
	      equ(g.var_count(), Lit::undef())
	{}

	// return true on contradiction
	bool dfs(Lit v)
	{
		if (visited[v])
			return false;
		visited[v] = true;

		int x = back[v] = cnt++;

		stack.push_back(v);

		for (Lit w : g[v.neg()])
		{
			if (dfs(w))
				return true;
			x = std::min(x, back[w]);
		}

		if (x < back[v])
		{
			back[v] = x;
			return false;
		}

		comp.resize(0);

		while (true)
		{
			Lit t = stack.back();
			stack.pop_back();
			back[t] = INT_MAX;
			comp.push_back(t);
			if (t == v)
				break;
		}

		std::sort(comp.begin(), comp.end());
		if (comp[0].sign() == true)
			return false;

		if (comp.size() >= 2 && comp[0] == comp[1].neg())
			return true;

		for (auto l : comp)
		{
			assert(equ[l.var()] == Lit::undef());
			equ[l.var()] = Lit(nComps, l.sign());
		}

		nComps++;
		return false;
	}
};

} // namespace

int run_scc(Sat &sat)
{
	if (sat.contradiction || sat.bins.empty())
		return 0;

	auto g = ImplicationGraph(sat);
	if (TopOrder(g).valid)
		return 0;

	auto tarjan = Tarjan(g);

	// run tarjan
	for (Lit a : sat.all_lits())
		if (tarjan.dfs(a))
		{
			sat.add_empty();
			return sat.var_count();
		}

	int nFound = sat.var_count() - tarjan.nComps;

	// no equivalences -> quit
	assert(nFound);
	if (nFound == 0)
		return 0;

	// otherwise renumber
	sat.renumber(tarjan.equ, tarjan.nComps);
	return nFound;
}

void print_binary_stats(ImplicationGraph const &g)
{
	int nIsolated = 0; // vertices with no binary clauses
	int nRoots = 0;    // vertices with only outgoing edges
	int nSinks = 0;    // vertices with only incoming edges
	int nFrom = 0;     // vertices with >=2 outging edges
	int nTo = 0;       // vertices with >= 2 incoming edges

	for (int i = 0; i < g.var_count() * 2; ++i)
	{
		auto a = Lit(i);

		if (g[a].empty() && g[a.neg()].empty())
		{
			++nIsolated;
			continue;
		}

		if (g[a.neg()].empty())
			++nSinks;
		if (g[a].empty())
			++nRoots;
		if (g[a.neg()].size() >= 2)
			++nFrom;
		if (g[a].size() >= 2)
			++nTo;
	}

	// sanity check the symmetry of the graph
	assert(nIsolated % 2 == 0);
	assert(nRoots == nSinks);
	assert(nFrom == nTo);

	int nVertices = g.var_count() * 2 - nIsolated;
	fmt::print("c vars with binaries: {} ({:.2f} GiB for transitive closure)\n",
	           nVertices / 2,
	           (double)nVertices * nVertices * 8 / 1024 / 1024 / 1024);
	fmt::print("c binary roots: {}\n", nRoots);
	fmt::print(
	    "c non-trivial nodes: 2 x {} ({:.2f} GiB for transitive closure)\n",
	    nFrom, (double)nFrom * nFrom / 8 / 1024 / 1024 / 1024);

	auto uf = util::UnionFind(g.var_count());
	for (int i = 0; i < g.var_count() * 2; ++i)
		for (auto b : g[Lit(i)])
			uf.join(Lit(i).var(), b.var());

	auto top = TopOrder(g);
	fmt::print("c acyclic: {}\n", top.valid);

	// roots have level=0, increasing from there
	// height = 1 + max(level)
	auto level = std::vector<int>(2 * g.var_count());
	auto height = std::vector<int>(g.var_count());
	for (Lit a : top.lits)
	{
		for (Lit b : g[a])
		{
			if (top.valid)
				assert(top.order[b.neg()] < top.order[a]);
			level[a] = std::max(level[a], 1 + level[b.neg()]);
		}
		height[uf.root(a.var())] =
		    std::max(height[uf.root(a.var())], 1 + level[a]);
	}
	std::vector<std::pair<int, int>> comps;

	for (int i = 0; i < g.var_count(); ++i)
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

void run_binary_reduction(Cnf &cnf)
{
	auto log = Logger("TBR");
	auto g = ImplicationGraph(cnf);

	auto top = TopOrder(g);
	if (!top.valid) // require acyclic
		throw std::runtime_error("tried to run TBR without SCC first");

	// sort clauses by topological order
	for (auto &c : g.bins)
		unique_sort(
		    c, [&top](Lit a, Lit b) { return top.order[a] < top.order[b]; });

	// start transitive reduction from pretty much all places
	auto seen = util::bit_vector(2 * cnf.var_count());
	util::vector<Lit> stack;
	int nFound = 0;
	int64_t propCount = 0;
	for (Lit a : cnf.all_lits())
	{
		if (g[a.neg()].size() < 2)
			continue;

		seen.clear();
		assert(stack.empty());
		erase_if(g[a.neg()], [&](Lit b) {
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
				Lit c = stack.pop_back();
				for (Lit d : g[c.neg()])
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

	if (nFound)
	{
		cnf.bins = std::move(g.bins);
		/*cnf.bins.resize(0);
		for (Lit a : cnf.all_lits())
		    for (Lit b : g[a])
		        if (a < b)
		            cnf.bins.push_back({a, b});*/
	}

	log.info("removed {} redundant binaries (using {:.2f}M props)", nFound / 2,
	         propCount / 1024. / 1024.);
}

} // namespace dawn
