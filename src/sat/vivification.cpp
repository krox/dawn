#include "sat/vivification.h"

#include "sat/propengine.h"
#include <unordered_set>

namespace dawn {

namespace {

struct Vivification
{
	Sat &sat;
	PropEngineLight p;
	int64_t shortened = 0;    // number of lits removed
	int64_t strengthened = 0; // number of lits replaced by stronger one

	/*std::unordered_set<std::pair<Lit, Lit>, util::hash<pair<Lit, Lit>>>
	    bins_seen;*/

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
			p.propagate_neg(std::span(cl).subspan(i + 1));

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

bool run_vivification(Sat &sat, VivifyConfig const &config)
{
	if (!is_normal_form(sat))
		return false;

	util::StopwatchGuard swg(sat.stats.swVivification);
	auto log = Logger("vivification");

	auto viv = Vivification(sat);
	std::vector<Lit> buf;

	ClauseStorage newClauses;

	// shortening binaries is essentially probing, which is done elsewhere
	if (config.with_binary)
	{
		for (Lit a : sat.all_lits())
			for (Lit b : sat.bins[a])
			{
				if (a > b)
					continue;
				buf = {a, b};
				if (viv.vivifyClause(buf, config.with_binary))
					newClauses.add_clause(buf, true);
			}
	}

	for (auto &cl : sat.clauses.all())
	{
		if (config.irred_only && !cl.irred())
			continue;
		if (interrupt)
			break;

		buf.assign(cl.begin(), cl.end());
		if (viv.vivifyClause(buf, config.with_binary))
		{
			assert(buf.size() <= cl.size());
			newClauses.add_clause(buf, cl.irred());
			cl.set_removed();
		}
	}

	for (auto &cl : newClauses.all())
		sat.add_clause(cl.lits(), cl.irred());

	if (config.with_binary)
	{
		int nRemoved = cleanup(sat);
		log.info("removed {} lits and replaced {} lits (removed {} vars)",
		         viv.shortened, viv.strengthened, nRemoved);
	}
	else
	{
		int nRemoved = cleanup(sat);
		log.info("removed {} lits (removed {} vars)", viv.shortened, nRemoved);
	}

	return viv.shortened + viv.strengthened;
}

} // namespace dawn
