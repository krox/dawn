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
 * In the last case, a can become irreducible if b was irreducible previously.
 * NOTE: this method assumes that the lits in both clauses are sorted. If they
 *       are not, it just produces some false-negatives. This means some
 *       possible subsumptions will stay undetected, but nothing will break.
 */
bool try_subsume(Clause &a, Clause &b)
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
			a.set_irred();
		b.set_removed();
	}
	else
		b.remove_literal(x); // TODO: slightly subptimal performance...
	return true;
}

class Subsumption
{
	std::vector<Lit> stack; // temporary for DFS

  public:
	Sat &sat;
	std::vector<util::small_vector<CRef, 7>> occs;
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

	// mark all literals implied by a
	void mark_reachable(Lit a)
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

	// perform subsumption and self-subsuming resolution using
	// implications a -> X (also finds some failed literals)
	void subsumeBinary(Lit a)
	{
		// early-out for literals without any implications
		if (sat.bins[a.neg()].empty())
			return;

		// mark all literals reachable from a
		mark_reachable(a);
		seen[a] = false;

		// if a implies ~a, we have a failed literal (should be rare here)
		if (seen[a.neg()])
		{
			sat.add_unary(a.neg());
			return;
		}

		// NOTE: occ lists are not updated, so they can contain removed clauses
		//       and removed literals. Need to check each time.

		// remove clauses subsumed by some implication a -> *
		for (CRef k : occs[a.neg()])
		{
			auto &cl = sat.clauses[k];
			if (cl.removed())
				continue;

			for (Lit x : sat.clauses[k].lits())
				if (seen[x])
				{
					sat.clauses[k].set_removed();
					++nRemovedClsBin;
					break;
				}
		}

		// strengthen clauses using implications a -> *
		for (CRef k : occs[a])
		{
			auto &cl = sat.clauses[k];
			if (cl.removed())
				continue;

			for (Lit x : cl.lits())
				if (seen[x])
				{
					if (cl.remove_literal(a))
					{
						++nRemovedLitsBin;
						if (cl.size() == 2)
						{
							sat.add_binary(cl[0], cl[1]);
							cl.set_removed();
						}
					}
					break;
				}
		}
	}

	void subsumeBinary()
	{
		// TODO: checking them in a clever order could allow to make
		//       'mark_reachable' incremental, thus saving some work
		for (Lit a : sat.all_lits())
			subsumeBinary(a);
	}
};

std::pair<int64_t, int64_t> subsumeLong(Sat &sat)
{
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
	auto occs = std::vector<util::small_vector<CRef, 7>>(sat.var_count());
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
			if (cl.removed())
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
				if (cl2.removed())
					continue; // already removed by different subsumption
				if (try_subsume(cl, cl2))
				{
					if (cl2.removed())
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
							cl2.set_removed();
						}
					}
				}
			}

			// add vlause to occ-lists
			for (Lit a : sat.clauses[i].lits())
				occs[a.var()].push_back(i);
		}
	}

	return {nRemovedClsLong, nRemovedLitsLong};
}

} // namespace

bool run_subsumption(Sat &sat)
{
	util::StopwatchGuard swg(sat.stats.swSubsume);
	auto log = Logger("subsumption");

	Subsumption sub(sat);
	sub.subsumeBinary();

	auto [nRemovedClsLong, nRemovedLitsLong] = subsumeLong(sat);

	int nRemovedVars = cleanup(sat);
	log.info("removed {} + {} clauses and {} + {} lits (removed {} vars)",
	         sub.nRemovedClsBin, nRemovedClsLong, sub.nRemovedLitsBin,
	         nRemovedLitsLong, nRemovedVars);

	return sub.nRemovedClsBin || sub.nRemovedLitsBin || nRemovedClsLong ||
	       nRemovedLitsLong;
}

} // namespace dawn
