#include "sat/vivification.h"

#include "sat/propengine.h"

namespace dawn {

namespace {

struct Vivification
{
	Sat &sat;
	PropEngineLight p;
	int64_t shortened = 0;    // number of lits removed
	int64_t strengthened = 0; // number of lits replaced by stronger one

	Vivification(Sat &s) : sat(s), p(s) {}

	/**
	 * try vifify a single clause
	 *   - returns true if something was found
	 *   - changes cl in place
	 */
	bool vivifyClause(std::vector<Lit> &cl, bool withBinary)
	{
		assert(p.level() == 0);
		assert(!p.conflict);
		assert(cl.size() >= 3); // not sure about this limitation

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
				shortened += 1;
				std::swap(cl[i], cl.back());
				cl.pop_back();
				p.unroll();
				p.unroll();
				return true;
			}

			// at this point, everything except cl[i] propagated without
			// conflict, so we can now try to replace cl[i] with a stronger
			// literal (using some binary clause)
			if (withBinary)
			{
				for (Lit a : sat.bins[cl[i]]) // a.neg => cl[i]
				{
					for (size_t j = 0; j < cl.size(); ++j)
						if (i != j && cl[j].var() == a.var())
							goto next_try;
					p.mark();
					p.propagate(a);
					if (p.conflict)
					{
						cl[i] = a.neg();
						strengthened += 1;
						p.unroll();
						p.unroll();
						p.unroll();
						return true;
					}
					else
						p.unroll();
				next_try:;
				}
			}

			p.unroll();
			if (i + 1 == cl.size())
				break;

			p.propagate(cl[i].neg());
			if (p.conflict)
			{
				shortened += cl.size() - (i + 1);
				cl.resize(i + 1);
				p.unroll();
				return true;
			}
		}
		p.unroll();
		return false;
	}
};

} // namespace

bool runVivification(Sat &sat, bool withBinary)
{
	util::StopwatchGuard swg(sat.stats.swVivification);
	util::Stopwatch sw;
	sw.start();

	auto viv = Vivification(sat);
	if (viv.p.conflict)
		return false;
	std::vector<Lit> buf;

	ClauseStorage newClauses;
	for (auto [ci, cl] : sat.clauses)
	{
		(void)ci;

		if (!(cl.irred() || cl.size() < 8))
			continue;
		if (interrupt)
			break;

		buf.assign(cl.begin(), cl.end());
		if (viv.vivifyClause(buf, withBinary))
		{
			assert(buf.size() <= cl.size());
			newClauses.addClause(buf, cl.irred());
			cl.remove();
		}
	}

	for (auto [ci, cl] : newClauses)
	{
		(void)ci;
		sat.addClause(cl.lits(), cl.irred());
	}

	if (withBinary)
	{
		int nRemoved = cleanup(sat);
		fmt::print("c [vivification {:#6.2f}] removed {} lits and replaced {} "
		           "lits (removed {} vars)\n",
		           sw.secs(), viv.shortened, viv.strengthened, nRemoved);
	}
	else
	{
		int nRemoved = cleanup(sat);
		fmt::print(
		    "c [vivification {:#6.2f}] removed {} lits (removed {} vars)\n",
		    sw.secs(), viv.shortened, nRemoved);
	}

	return viv.shortened + viv.strengthened;
}

} // namespace dawn
