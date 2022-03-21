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

		bool change = false;

		p.mark();
		for (size_t i = 0; i < cl.size(); ++i)
		{
			p.mark();
			p.propagate_neg(util::span(cl).subspan(i + 1));

			if (p.conflict)
			{
				shortened += 1;
				std::swap(cl[i], cl.back());
				cl.pop_back();
				--i;
				p.unroll();
				shortened += 1;
				change = true;
				continue;
			}

			// at this point, everything except cl[i] propagated without
			// conflict, so we can now try to replace cl[i] with a stronger
			// literal (using some binary clause)
			if (withBinary)
			{
			again:
				for (Lit a : sat.bins[cl[i]]) // a.neg => cl[i]
				{
					// this is some tautology or subsumption case we dont want
					// to handle right here... maybe we should
					for (size_t j = 0; j < cl.size(); ++j)
						if (i != j && cl[j].var() == a.var())
							goto next_try;

					if (p.probe(a) == -1)
					{
						cl[i] = a.neg();
						strengthened += 1;
						change = true;

						goto again;
					}

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
				change = true;
				break;
			}
		}
		p.unroll();
		return change;
	}
};

} // namespace

bool runVivification(Sat &sat, bool withBinary)
{
	if (!is_normal_form(sat))
		return false;

	util::StopwatchGuard swg(sat.stats.swVivification);
	util::Stopwatch sw;
	sw.start();

	auto viv = Vivification(sat);
	std::vector<Lit> buf;

	ClauseStorage newClauses;

	for (int i = 0; i < sat.varCount() * 2; ++i)
	{
		for (Lit b : sat.bins[i])
		{
			if (Lit(i) > b)
				continue;
			buf = {Lit(i), b};
			if (viv.vivifyClause(buf, withBinary))
				newClauses.addClause(buf, true);
		}
	}

	for (auto &cl : sat.clauses.all())
	{
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

	for (auto &cl : newClauses.all())
		sat.addClause(cl.lits(), cl.irred());

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
