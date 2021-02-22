#include "sat/vivification.h"

#include "sat/propengine.h"

namespace {
/**
 * try vifify a single clause
 *   - returns true if something was found
 *   - changes cl in place
 */
bool vivify_clause(PropEngineLight &p, std::vector<Lit> &cl)
{
	assert(p.level() == 0);
	assert(!p.conflict);

	p.mark();
	for (size_t i = 0; i < cl.size(); ++i)
	{

		p.mark();

		for (size_t j = i + 1; j < cl.size(); ++j)
		{
			p.propagate(cl[j].neg());
			if (p.conflict)
				break;
		}

		if (p.conflict)
		{
			std::swap(cl[i], cl.back());
			cl.pop_back();
			p.unroll();
			p.unroll();
			return true;
		}

		p.unroll();
		if (i + 1 == cl.size())
			break;

		p.propagate(cl[i].neg());
		if (p.conflict)
		{
			cl.resize(i + 1);
			p.unroll();
			return true;
		}
	}
	p.unroll();
	return false;
}
} // namespace

bool run_vivification(Sat &sat)
{
	util::StopwatchGuard swg(sat.stats.swVivification);
	Stopwatch sw;
	sw.start();

	auto p = PropEngineLight(sat);
	if (p.conflict)
		return false;
	std::vector<Lit> buf;
	int nFound = 0;
	ClauseStorage newClauses;
	for (auto [ci, cl] : sat.clauses)
	{
		if (!(cl.irred() || cl.size() < 8))
			continue;
		(void)ci;
		buf.assign(cl.lits().begin(), cl.lits().end());
		if (vivify_clause(p, buf))
		{
			assert(buf.size() < cl.size());
			nFound++;
			newClauses.addClause(buf, cl.irred());
			cl.remove();
		}
	}

	for (auto [ci, cl] : newClauses)
	{
		(void)ci;
		sat.addClause(cl.lits(), cl.irred());
	}

	fmt::print("c vivification shortened {} clauses in {:.2f}s\n", nFound,
	           sw.secs());

	return nFound;
}
