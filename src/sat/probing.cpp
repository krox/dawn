#include "sat/probing.h"

#include "sat/propengine.h"

int probe(Sat &sat, int maxTries)
{
	StopwatchGuard swg(sat.stats.swProbing);

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
	std::shuffle(candidates.begin(), candidates.end(), sat.stats.rng);
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
				return 1;
		}
		else // no fail -> do nothing
		{
			p.unroll(0);
		}
	}

	return nFails;
}
