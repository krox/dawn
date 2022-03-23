#include "sat/subsumption.h"

#include "fmt/format.h"
#include "util/bit_vector.h"
#include "util/span.h"

namespace dawn {

namespace {

/**
 * Try to subsume b using a. This can either:
 *    - do nothing (return false)
 *    - shorten b (return true, b.isRemoved()=false)
 *    - remove b (return true, b.isRemoved()=true)
 * In the last case, a can become irreducible if b was before.
 * NOTE: this method assumes that the lits in both clauses are sorted. If they
 *       are not, it just produces some false-negatives. This means some
 *       possible subsumptions will stay undetected, but nothing will break.
 */
bool trySubsume(Clause &a, Clause &b)
{
	if (a.size() > b.size())
		return false;

	Lit x = Lit::undef();
	for (int i = 0, j = 0; i < a.size(); ++i, ++j)
	{
		while (j < b.size() && b[j].var() < a[i].var())
			++j;
		if (j == b.size())
			return false;

		if (a[i] == b[j]) // exact match
			continue;
		else if (a[i] == b[j].neg()) // same variable, different sign
		{
			if (x != Lit::undef())
				return false;
			x = b[j];
		}
		else
			return false;
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
	util::bit_vector seen;

	// statistics
	size_t nRemovedClsBin = 0, nRemovedLitsBin = 0;

	Subsumption(Sat &sat)
	    : sat(sat), occs(sat.var_count() * 2), seen(sat.var_count() * 2)
	{
		for (auto [ci, cl] : sat.clauses.enumerate())
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
			sat.add_unary(a.neg());
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
								sat.add_binary(cl[0], cl[1]);
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
	util::Stopwatch sw;
	sw.start();

	Subsumption sub(sat);
	for (Lit a : sat.all_lits())
		sub.subsumeBinary(a);
	if (sub.nRemovedClsBin + sub.nRemovedLitsBin == 0)
		fmt::print("c [subsumption  {:#6.2f}] - (binary)\n", sw.secs());
	else
	{
		int nRemovedVars = cleanup(sat);
		fmt::print("c [subsumption  {:#6.2f}] removed {} clauses and {} lits "
		           "(binary) (removed {} vars)\n",
		           sw.secs(), sub.nRemovedClsBin, sub.nRemovedLitsBin,
		           nRemovedVars);
	}

	return sub.nRemovedClsBin || sub.nRemovedLitsBin;
}

bool subsumeLong(Sat &sat)
{
	util::StopwatchGuard swg(sat.stats.swSubsumeLong);
	util::Stopwatch sw;
	sw.start();

	// NOTE: Clauses can only subsume clauses of the same or larger size and
	//       subsumption between clauses of the same size is symmetric.
	//       Therefore we iterate through the clauses from long to short
	//       and only add a clause to the occ-list after it has been used
	//       for subsumption itself.
	// TODO: same-size subsumption only consists of cases where both clauses
	//       have the same variables (with eihter zero or one sign-difference).
	//       These cases could be handled completely separately and faster.
	//       This would help problems with a lot of clauses of the same size.
	// TODO: We should really introduce some cutoff. Trying to subsume each
	//       and every worthless learnt clause is probably not really useful...

	// sort variables in clauses (to simplify 'trySubsume()')
	// and list clauses by size
	std::array<std::vector<CRef>, 128> clauses;
	auto occs = std::vector<util::small_vector<CRef, 6>>(sat.var_count());
	for (auto [ci, cl] : sat.clauses.enumerate())
	{
		std::sort(cl.lits().begin(), cl.lits().end());
		clauses[cl.size() < 128 ? cl.size() : 127].push_back(ci);
	}

	int64_t nRemovedClsLong = 0;
	int64_t nRemovedLitsLong = 0;

	for (int size = 127; size >= 3; --size)
	{
		for (CRef i : clauses[size])
		{
			Clause &cl = sat.clauses[i];
			if (cl.isRemoved())
				continue; // can this happen at all here?

			// choose variable in cl with shortest occ-list
			int pivot = cl[0].var();
			for (Lit lit : cl.lits())
				if (occs[lit.var()].size() < occs[pivot].size())
					pivot = lit.var();

			// use occ-list of pivot variable as candidates for subsumption
			for (CRef j : occs[pivot])
			{
				if (i == j)   // dont subsume clauses with itself
					continue; // can this happen here at all?
				Clause &cl2 = sat.clauses[j];
				if (cl2.isRemoved())
					continue; // already removed by different subsumption
				if (trySubsume(cl, cl2))
				{
					if (cl2.isRemoved())
						nRemovedClsLong += 1;
					else
					{
						nRemovedLitsLong += 1;
						if (cl2.size() <= 2)
						{
							if (cl2.size() == 0)
								sat.add_empty(); // dont think this can happen
							else if (cl2.size() == 1)
								sat.add_unary(cl2[0]);
							else if (cl2.size() == 2)
								sat.add_binary(cl2[0], cl2[1]);
							cl2.remove();
						}
					}
				}
			}

			// add vlause to occ-lists
			for (Lit a : sat.clauses[i].lits())
				occs[a.var()].push_back(i);
		}
	}
	if (nRemovedClsLong + nRemovedLitsLong == 0)
		fmt::print("c [subsumption  {:#6.2f}] - (long)\n", sw.secs());
	else
	{
		int nRemovedVars = cleanup(sat);
		fmt::print("c [subsumption  {:#6.2f}] removed {} clauses and {} lits "
		           "(long) (removed {} vars)\n",
		           sw.secs(), nRemovedClsLong, nRemovedLitsLong, nRemovedVars);
	}
	return nRemovedClsLong || nRemovedLitsLong;
}

} // namespace dawn
