#include "sat/vivification.h"

#include "sat/propengine.h"
#include <unordered_set>

namespace dawn {

namespace {

struct Vivification
{
	Cnf &cnf_;
	PropEngineLight p;
	int64_t shortened = 0;    // number of lits removed
	int64_t strengthened = 0; // number of lits replaced by stronger one

	/*std::unordered_set<std::pair<Lit, Lit>, util::hash<pair<Lit, Lit>>>
	    bins_seen;*/

	Vivification(Cnf &cnf) : cnf_(cnf), p(cnf) {}

	// try to vifify a single clause
	//   - returns true if something was found
	//   - changes cl in place
	bool vivify_clause(std::vector<Lit> &cl, bool with_binary)
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
			if (with_binary)
			{
			again:
				for (Lit a : cnf_.bins[cl[i]]) // a.neg => cl[i]
				{
					// this is some tautology or subsumption case we dont want
					// to handle right here... maybe we should
					for (size_t j = 0; j < cl.size(); ++j)
						if (cl[j].var() == a.var())
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

bool run_vivification(Cnf &cnf, VivifyConfig const &config)
{
	if (!is_normal_form(cnf))
		return false;

	// util::StopwatchGuard swg(sat.stats.swVivification); TODO
	auto log = Logger("vivification");

	auto viv = Vivification(cnf);

	// NOTE: strengthening inplace is kinda fragile, so we binaries inplace is a
	// bit fragile (e.g. when there are equivalences). So we just add new
	// clauses, and rely on a later TBR run to clean up.
	std::vector<Lit> buf;
	ClauseStorage new_clauses;

	// shortening binaries is essentially probing, which is done elsewhere.
	// but strengthening binaries along other binaries is kinda cool and we do
	// it here
	if (config.with_binary)
	{
		for (Lit a : cnf.all_lits())
			for (Lit b : cnf.bins[a])
			{
				if (a > b)
					continue;
				buf = {a, b};
				if (viv.vivify_clause(buf, true))
					new_clauses.add_clause(buf, Color::blue);
			}
	}

	for (auto &cl : cnf.clauses.all())
	{
		if (cl.color <= Color::red)
			continue;
		if (interrupt)
			break;

		buf.assign(cl.begin(), cl.end());
		if (viv.vivify_clause(buf, config.with_binary))
		{
			assert(buf.size() <= cl.size());
			new_clauses.add_clause(buf, cl.color);
			cl.color = Color::black;
		}
	}

	if (new_clauses.empty())
	{
		log.info("-");
		return false;
	}

	cnf.clauses.prune_black();
	for (auto &cl : new_clauses.all())
		cnf.add_clause(cl.lits(), cl.color);

	if (config.with_binary)
		log.info("removed {} lits and replaced {} lits", viv.shortened,
		         viv.strengthened);
	else
		log.info("removed {} lits", viv.shortened);

	return viv.shortened + viv.strengthened;
}

} // namespace dawn
