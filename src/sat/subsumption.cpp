#include "sat/subsumption.h"

#include "fmt/format.h"
#include "util/bitset.h"
#include "util/span.h"

namespace {

bool trySubsume(Clause &a, Clause &b)
{
	if (a.size() > b.size())
		return false;

	Lit x = Lit::undef();
	for (int i = 0; i < a.size(); ++i)
	{
		for (int j = 0; j < b.size(); ++j)
		{
			if (a[i] == b[j])
				goto next;
			if (a[i] == b[j].neg())
			{
				if (x != Lit::undef())
					return false;
				x = b[j];
			}
		}
		return false;
	next:;
	}

	if (x == Lit::undef())
	{
		if (b.irred())
			a.makeIrred();
		b.remove();
	}
	else
		b.removeLiteral(x);
	return true;
}

class Subsumption
{
	std::vector<Lit> stack; // temporary for DFS

  public:
	Sat &sat;
	std::vector<util::small_vector<CRef, 6>> occs;
	util::bitset seen;

	// statistics
	size_t nRemovedClsBin = 0, nRemovedLitsBin = 0;

	Subsumption(Sat &sat)
	    : sat(sat), occs(sat.varCount() * 2), seen(sat.varCount() * 2)
	{
		for (auto [ci, cl] : sat.clauses)
			for (Lit a : cl.lits())
				occs[a].push_back(ci);
	}

	/** mark all literals implied by a */
	void markReachable(Lit a)
	{
		seen.clear();
		assert(stack.empty());
		seen[a] = true;
		stack.push_back(a);
		while (!stack.empty())
		{
			Lit b = stack.back();
			stack.pop_back();
			for (Lit c : sat.bins[b.neg()])
				if (!seen[c])
				{
					seen[c] = true;
					stack.push_back(c);
				}
		}
	}

	/**
	 * perform subsumption and self-subsuming resolution using
	 * implications a -> X (also find failed literals)
	 */
	void subsumeBinary(Lit a)
	{
		// early-out for literals without any implications
		if (sat.bins[a.neg()].empty())
			return;

		// mark all literals reachable from a
		markReachable(a);
		seen[a] = false;

		// if a implies ~a, we have a failed literal (should be rare here)
		if (seen[a.neg()])
		{
			sat.addUnary(a.neg());
			return;
		}

		// remove clauses subsumed by some implication a -> *
		for (CRef k : occs[a.neg()])
			if (!sat.clauses[k].isRemoved()) // might already have bee subsumed
				for (Lit x : sat.clauses[k].lits())
					if (seen[x])
					{
						sat.clauses[k].remove();
						++nRemovedClsBin;
						break;
					}

		// strengthen clauses using implications a -> *
		for (CRef k : occs[a])
		{
			Clause &cl = sat.clauses[k];

			if (!cl.isRemoved())
				for (Lit x : cl.lits())
					if (seen[x])
					{
						if (cl.removeLiteral(a))
						{
							++nRemovedLitsBin;
							if (cl.size() == 2)
							{
								sat.addBinary(cl[0], cl[1]);
								cl.remove();
							}
						}
						break;
					}
		}
	}
};
} // namespace

bool subsumeBinary(Sat &sat)
{
	util::StopwatchGuard swg(sat.stats.swSubsumeBin);

	Subsumption sub(sat);
	for (int i = 0; i < sat.varCount() * 2; ++i)
		sub.subsumeBinary(Lit(i));
	fmt::print("c binary-long subsumption removed {} clauses and {} lits\n",
	           sub.nRemovedClsBin, sub.nRemovedLitsBin);

	return sub.nRemovedClsBin || sub.nRemovedLitsBin;
}

bool subsumeLong(Sat &sat)
{
	util::StopwatchGuard swg(sat.stats.swSubsumeLong);
	Stopwatch sw;
	sw.start();

	// create occurence-lists per variable
	auto occs = std::vector<util::small_vector<CRef, 6>>(sat.varCount());
	for (auto [ci, cl] : sat.clauses)
		for (Lit a : cl.lits())
			occs[a.var()].push_back(ci);

	int64_t nRemovedClsLong = 0;
	int64_t nRemovedLitsLong = 0;

	// subsume clauses using cl
	for (auto [i, cl] : sat.clauses)
	{
		// skip already removed
		if (cl.isRemoved())
			continue;

		// choose variable with shortest occ list
		int pivot = cl[0].var();
		for (Lit lit : cl.lits())
			if (occs[lit.var()].size() < occs[pivot].size())
				pivot = lit.var();

		// use occ-list of pivot variable as candidates for subsumption
		for (CRef j : occs[pivot])
		{
			if (i == j) // dont subsume clauses with itself
				continue;
			if (trySubsume(cl, sat.clauses[j]))
			{
				if (sat.clauses[j].isRemoved())
					nRemovedClsLong += 1;
				else
					nRemovedLitsLong += 1;
			}
		}
	}

	fmt::print(
	    "c long-long subsumption removed {} clauses and {} lits in {:.2}s\n",
	    nRemovedClsLong, nRemovedLitsLong, sw.secs());
	return nRemovedClsLong || nRemovedLitsLong;
}
