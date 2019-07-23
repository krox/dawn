#include "sat/subsumption.h"

#include "fmt/format.h"
#include "util/bitset.h"

namespace {
class Subsumption
{
	std::vector<Lit> stack; // temporary for DFS

  public:
	Sat &sat;
	std::vector<util::small_vector<CRef, 6>> occs;
	util::bitset seen;

	// statistics
	size_t nRemovedClsBin = 0, nRemovedLitsBin = 0;
	size_t nRemovedClsLong = 0, nRemovedLitsLong = 0;

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
			if (!sat.clauses[k].isRemoved())
				for (Lit x : sat.clauses[k].lits())
					if (seen[x])
					{
						if (sat.clauses[k].removeLiteral(a))
							++nRemovedLitsBin;
						break;
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
	// fmt::print("c long-long subsumption removed {} clauses and {} lits\n",
	// sub.nRemovedClsLong, sub.nRemovedLitsLong);
	return true;
}
