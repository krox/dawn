#include "sat/scc.h"

#include <algorithm>
#include <vector>

namespace {

class Tarjan
{
  public:
	Sat &sat;
	std::vector<bool> visited;
	std::vector<int> back;
	std::vector<Lit> stack;
	int cnt = 0;
	std::vector<Lit> comp;
	std::vector<Lit> equ;
	int nComps = 0; // number of SCC's

	Tarjan(Sat &sat)
	    : sat(sat), visited(sat.varCount() * 2, false),
	      back(sat.varCount() * 2, 0), equ(sat.varCount(), Lit::undef())
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
