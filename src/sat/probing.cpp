#include "sat/probing.h"

#include "sat/binary.h"
#include "sat/propengine.h"

namespace dawn {

int probe(Sat &sat, int maxTries)
{
	util::StopwatchGuard swg(sat.stats.swProbing);
	util::Stopwatch sw;
	sw.start();

	PropEngine p(sat);
	if (p.conflict)
		return 0;

	// list and shuffle candidates
	std::vector<Lit> candidates;
	for (int i = 0; i < 2 * sat.varCount(); ++i)
	{
		auto l = Lit(i);
		if (sat.bins[l.neg()].empty())
			continue;
		if (!sat.bins[l].empty())
			continue;
		candidates.push_back(l);
	}
	std::shuffle(candidates.begin(), candidates.end(), sat.rng);
	if (maxTries && (int)candidates.size() > maxTries)
		candidates.resize(maxTries);

	int nTries = 0, nFails = 0;
	std::vector<Lit> buf;

	for (Lit branch : candidates)
	{
		// skip fixed literals
		if (p.assign[branch] || p.assign[branch.neg()])
			continue;

		// skip non-roots (former roots might have become non-roots)
		if (sat.bins[branch.neg()].empty() || !sat.bins[branch].empty())
			continue;

		nTries += 1;

		p.branch(branch);

		if (p.conflict) // literal failed -> analyze and learn unit
		{
			nFails += 1;
			[[maybe_unused]] int backLevel = p.analyzeConflict(buf);
			assert(backLevel == 0);
			assert(buf.size() == 1);
			p.unroll(0);
			p.addLearntClause(buf, 1);
			p.propagateFull(buf[0], Reason::undef());
			buf.resize(0);

			// UNSAT encountered
			if (p.conflict)
				break;
		}
		else // no fail -> do nothing
		{
			p.unroll(0);
		}
	}

	fmt::print("c [probing      {:#6.2f}] found {} failing literals\n",
	           sw.secs(), nFails);
	return nFails;
}

int probeBinary(Sat &sat)
{
	/*
	Idea: Propagate two literals a and b. If a conflict arises, we can learn
	      the binary clause (-a,-b). Some optimizations arise:
	1) If a conflict arises, dont just learn (-a,-b). Instead do conflict
	   analysis and potentially learn an even stronger clause.
	2) If no conflict arises when propagating b and b implies b', then no
	   conflict can arise when propagating b' instead of b. No need to check.
	3) To maximize the effect of (1) and (2), we probe literals in (approximate)
	   topological order.
	 */
	util::StopwatchGuard swg(sat.stats.swProbing);
	util::Stopwatch sw;
	sw.start();

	PropEngine p(sat);
	if (p.conflict)
		return 0;

	auto top = TopOrder(sat);
	auto seenA = util::bitset(sat.varCount() * 2);
	auto seenB = util::bitset(sat.varCount() * 2);
	std::vector<Lit> buf;
	int nTries = 0;
	int nFails = 0;

	auto backtrack = [&p, &buf, &nFails]() {
		int back = p.analyzeConflict(buf);
		p.unroll(back);
		auto reason = p.addLearntClause(buf, 2); // dont care about glue here
		p.propagateFull(buf[0], reason);
		buf.resize(0);
	};

	for (Lit a : top.lits())
	{
		seenB.clear();

	use_this_a:

		if (p.assign[a] || p.assign[a.neg()] || seenA[a])
			continue;
		seenA[a] = true;
		p.branch(a);
		assert(p.level() == 1);

		// failed literal -> analyze and learn unit
		if (p.conflict)
		{
			// nFailsUnary += 1;
			backtrack();

			if (p.conflict) // still conflict -> UNSAT
				break;
			else // conflict resolved -> next literal
				continue;
		}

		// propagating a worked fine -> probe all possible b
		assert(p.level() == 1);

		for (Lit b : top.lits())
		{
			if (p.assign[b] || p.assign[b.neg()] || seenB[b])
				continue;
			if ((int)b > (int)a)
				continue;
			p.branch(b);
			nTries += 1;

			if (p.conflict)
			{
				nFails += 1;
				while (p.conflict)
					if (p.level() == 0) // level 0 conflict -> UNSAT
						return 1;
					else
						backtrack();

				if (p.level() == 0)
					goto next_a;
				else if (p.level() == 1)
					continue;
				else
					assert(false);
			}
			else
			{
				// no conflict -> mark everything propagated as seen
				assert(p.level() == 2);
				for (Lit c : p.trail(2))
					seenB[c] = true;
				p.unroll(1);
			}
		}
		p.unroll(0);

		if (nFails > 1000)
			break;

		// for this a, all b were probed. Try to get a weaker a next
		// in order to reuse the 'seenB' array
		for (Lit a2 : p.sat.bins[a.neg()])
			if (!(p.assign[a2] || p.assign[a2.neg()] || seenA[a2]))
			{
				a = a2;
				goto use_this_a;
			}

	next_a:;
	}

	fmt::print(
	    "c Binary-Probing found {} failing bins after {} tries in {:.2f}s\n",
	    nFails, nTries, sw.secs());

	return nFails;
}

} // namespace dawn
