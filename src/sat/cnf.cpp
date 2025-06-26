#include "sat/cnf.h"

#include "fmt/format.h"
#include "sat/probing.h"
#include "sat/propengine.h"
#include "util/logging.h"
#include "util/stats.h"
#include "util/unionfind.h"
#include <algorithm>
#include <cassert>
#include <random>
#include <sstream>

namespace dawn {

Cnf::Cnf(int n, ClauseStorage clauses_)
    : recon_(n), bins(n), clauses(std::move(clauses_))
{
	for (auto &cl : clauses.all())
	{
		cl.normalize();
		if (cl.color() == Color::black || cl.size() >= 3)
			continue;
		if (cl.size() == 0)
			add_empty();
		else if (cl.size() == 1)
			add_unary(cl[0]);
		else if (cl.size() == 2)
			add_binary(cl[0], cl[1]);
		else
			assert(false);
		cl.set_color(Color::black);
	}
	clauses.prune_black();
}

void Cnf::add_clause_safe(std::span<const Lit> lits)
{
	util::small_vector<Lit, 16> buf;
	for (auto a : lits)
	{
		assert(a.proper() || a.fixed());
		buf.push_back(a);
	}
	int s = normalize_clause({buf.begin(), buf.end()});
	if (s != -1)
	{
		buf.resize(s);
		add_clause({buf.begin(), buf.end()}, Color::blue);
	}
}

void Cnf::add_clause_safe(std::string_view cl)
{
	std::vector<Lit> lits;
	std::istringstream iss{std::string{cl}};
	for (auto it = std::istream_iterator<std::string>(iss),
	          end = std::istream_iterator<std::string>();
	     it != end; ++it)
		lits.push_back(Lit::fromDimacs(std::stoi(*it)));
	add_clause_safe(lits);
}

void Cnf::add_and_clause_safe(Lit a, Lit b, Lit c)
{
	add_clause_safe({{a, b.neg(), c.neg()}});
	add_clause_safe({{a.neg(), b}});
	add_clause_safe({{a.neg(), c}});
}

void Cnf::add_or_clause_safe(Lit a, Lit b, Lit c)
{
	add_and_clause_safe(a.neg(), b.neg(), c.neg());
}

void Cnf::add_xor_clause_safe(Lit a, Lit b, Lit c)
{
	add_clause_safe({{a, b, c.neg()}});
	add_clause_safe({{a, b.neg(), c}});
	add_clause_safe({{a.neg(), b, c}});
	add_clause_safe({{a.neg(), b.neg(), c.neg()}});
}

void Cnf::add_xor_clause_safe(Lit a, Lit b, Lit c, Lit d)
{
	add_clause_safe({{a, b, c, d.neg()}});
	add_clause_safe({{a, b, c.neg(), d}});
	add_clause_safe({{a, b.neg(), c, d}});
	add_clause_safe({{a.neg(), b, c, d}});
	add_clause_safe({{a, b.neg(), c.neg(), d.neg()}});
	add_clause_safe({{a.neg(), b, c.neg(), d.neg()}});
	add_clause_safe({{a.neg(), b.neg(), c, d.neg()}});
	add_clause_safe({{a.neg(), b.neg(), c.neg(), d}});
}

void Cnf::add_maj_clause_safe(Lit a, Lit b, Lit c, Lit d)
{
	add_clause_safe({{a.neg(), b, c}});
	add_clause_safe({{a.neg(), b, d}});
	add_clause_safe({{a.neg(), c, d}});
	add_clause_safe({{a, b.neg(), c.neg()}});
	add_clause_safe({{a, b.neg(), d.neg()}});
	add_clause_safe({{a, c.neg(), d.neg()}});
}

void Cnf::add_ite_clause_safe(Lit a, Lit b, Lit c, Lit d)
{
	add_clause_safe({{a, b.neg(), c.neg()}});
	add_clause_safe({{a, b, d.neg()}});
	add_clause_safe({{a.neg(), b.neg(), c}});
	add_clause_safe({{a.neg(), b, d}});

	// redundant clauses
	add_clause_safe({{a, c.neg(), d.neg()}});
	add_clause_safe({{a.neg(), c, d}});
}

size_t Cnf::unary_count() const { return units.size(); }

size_t Cnf::binary_count() const { return bins.clause_count(); }

size_t Cnf::long_count() const { return clauses.count(); }

size_t Cnf::clause_count() const
{
	return unary_count() + binary_count() + long_count() + contradiction;
}

size_t Cnf::long_count_irred() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (cl.color() == Color::blue)
			++r;
	return r;
}

size_t Cnf::long_count_red() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (cl.color() != Color::blue && cl.color() != Color::black)
			++r;
	return r;
}

size_t Cnf::lit_count_irred() const
{
	size_t r = 0;
	for (auto &cl : clauses.all())
		if (cl.color() == Color::blue)
			r += cl.size();
	return r;
}

util::IntHistogram Cnf::clause_histogram() const
{
	util::IntHistogram r;
	r.add(0, contradiction ? 1 : 0);
	r.add(1, unary_count());
	r.add(2, binary_count());
	for (auto &cl : clauses.all())
		r.add(cl.size());
	return r;
}

void Cnf::add_rule(std::span<const Lit> cl) { recon_.add_rule(cl); }
void Cnf::add_rule(std::span<const Lit> cl, Lit pivot)
{
	recon_.add_rule(cl, pivot);
}
Assignment Cnf::reconstruct_solution(Assignment const &a) const
{
	return recon_(a);
}

void Cnf::renumber(std::span<const Lit> trans, int newVarCount)
{
	// check input
	assert(trans.size() == (size_t)var_count());
	for (Lit l : trans)
		assert(l.fixed() || l == Lit::elim() ||
		       (l.proper() && l.var() < newVarCount));

	recon_.renumber(trans, newVarCount);

	// renumber units
	{
		auto units_old = std::move(units);
		units.clear();
		for (Lit a : units_old)
		{
			a = trans[a.var()] ^ a.sign();
			if (a == Lit::one())
				continue;
			else if (a == Lit::zero())
				add_empty();
			else if (a.proper())
				add_unary(a);
			else
				assert(false); // disallows elim
		}
	}

	// renumber binaries
	{
		BinaryGraph binsOld(newVarCount);
		std::swap(bins, binsOld);

		for (int i = 0; i < binsOld.var_count() * 2; ++i)
		{
			const auto a = Lit(i);

			for (Lit b : binsOld[a])
			{
				assert(a.var() != b.var());
				if (a.var() < b.var())
					continue;

				// translate both literals
				Lit c = trans[a.var()] ^ a.sign();
				Lit d = trans[b.var()] ^ b.sign();

				if (c == Lit::elim() || c == Lit::undef() || d == Lit::elim() ||
				    d == Lit::undef())
					throw std::runtime_error(
					    "invalid renumbering: elim/undef in binary clause");

				// (true, x), (x, -x) -> tautology
				if (c == Lit::one() || d == Lit::one() || c == d.neg())
					continue;

				// (false, false) -> ()
				else if (c == Lit::zero() && d == Lit::zero())
					add_empty();

				// (false, x), (x, x) -> (x)
				else if (c == Lit::zero())
					add_unary(d);
				else if (d == Lit::zero())
					add_unary(c);
				else if (c == d)
					add_unary(c);

				// actual binary clause left
				else
					add_binary(c, d);
			}
		}
	}

	// renumber long clauses
	for (auto &cl : clauses.all())
	{
		if (cl.color() == Color::black)
			continue;
		for (Lit &a : cl.lits())
			a = trans[a.var()] ^ a.sign();
		cl.normalize();
		if (cl.color() == Color::black)
			continue;
		if (cl.size() == 0)
			add_empty();
		if (cl.size() == 1)
			add_unary(cl[0]);
		if (cl.size() == 2)
			add_binary(cl[0], cl[1]);
		if (cl.size() <= 2)
			cl.set_color(Color::black);
	}
	clauses.prune_black();

	assert(var_count() == newVarCount);
}

size_t Cnf::memory_usage() const
{
	size_t r = 0;
	r += units.capacity() * sizeof(Lit);
	r += bins.memory_usage();
	r += clauses.memory_usage();
	return r;
}

namespace {
void top_order_dfs(Lit a, TopOrder &r, BinaryGraph const &g)
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

class Tarjan
{
  public:
	BinaryGraph const &g;
	util::bit_vector visited;
	std::vector<int> back;
	std::vector<Lit> stack;
	int cnt = 0;
	std::vector<Lit> comp;
	std::vector<Lit> equ;
	int nComps = 0; // number of SCC's

	Tarjan(BinaryGraph const &g)
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

TopOrder::TopOrder(BinaryGraph const &g) : valid(true)
{
	order.resize(2 * g.var_count(), -1);
	lits.reserve(2 * g.var_count());

	for (int i = 0; i < 2 * g.var_count(); ++i)
		top_order_dfs(Lit(i), *this, g);
	assert((int)lits.size() == 2 * g.var_count());
}

int run_unit_propagation(Cnf &sat)
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
		sat.bins.clear();
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

int run_scc(Cnf &sat)
{
	if (sat.contradiction)
		return 0;

	auto const &g = sat.bins;
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

void run_binary_reduction(Cnf &cnf)
{
	auto &g = cnf.bins;

	auto top = TopOrder(g);
	if (!top.valid) // require acyclic
		throw std::runtime_error("tried to run TBR without SCC first");

	// sort clauses by topological order
	for (auto &c : g.bins_)
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

	// log.info("removed {} redundant binaries (using {:.2f}M props)", nFound /
	// 2, propCount / 1024. / 1024.);
}

void cleanup(Cnf &sat)
{
	auto log = util::Logger("cleanup");

	// NOTE: Theoretically, this loop could become quadratic. But in practice,
	// I never saw more than a few iterations, so we dont bother capping it.
	while (true)
	{
		run_unit_propagation(sat);
		if (run_scc(sat))
			continue;
		if (run_probing(sat))
			continue;
		break;
	}
	run_binary_reduction(sat);
	sat.clauses.prune_black();
	log.debug("now at {} vars, {} bins, {} irred, {} learnt", sat.var_count(),
	          sat.binary_count(), sat.long_count_irred(), sat.long_count_red());
}

bool is_normal_form(Cnf const &cnf)
{
	if (cnf.contradiction && cnf.var_count() != 0)
		return false;
	if (!cnf.units.empty())
		return false;
	if (!TopOrder(cnf.bins).valid)
		return false;
	return true;
}

void shuffle_variables(Cnf &sat, util::xoshiro256 &rng)
{
	auto trans = std::vector<Lit>(sat.var_count());
	for (int i : sat.all_vars())
	{
		trans[i] = Lit(i, std::bernoulli_distribution(0.5)(rng));
		int j = std::uniform_int_distribution<int>(0, i)(rng);
		std::swap(trans[i], trans[j]);
	}
	sat.renumber(trans, sat.var_count());
}

void print_binary_stats(BinaryGraph const &g)
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

void print_stats(Cnf const &cnf)
{
	util::IntHistogram blue, red;
	blue.add(0, cnf.contradiction ? 1 : 0);
	blue.add(1, cnf.unary_count());
	blue.add(2, cnf.binary_count());
	for (auto &cl : cnf.clauses.all())
		if (cl.color() == Color::blue)
			blue.add(cl.size());
		else
			red.add(cl.size());
	auto log = util::Logger("stats");
	log.info("nvars = {}", cnf.var_count());
	for (int k = 0; k <= std::max(blue.max(), red.max()); ++k)
		if (blue.bin(k) || red.bin(k))
			log.info("nclauses[{:3}] = {:5} + {:5}", k, blue.bin(k),
			         red.bin(k));
	log.info("nclauses[all] = {:5} + {:5}", blue.count(), red.count());
}

} // namespace dawn
