#include "sat/vivification.h"

#include "sat/propengine.h"
#include "util/hash_map.h"

// TODO: vivification needs some serious cleaning up.
//    * maybe properly separate basic / binary / ternary
//    * bin-vivify on binaries (and tern-vivivy on ternaries) is a bit subtle to
//      get right (and the latter one is disabled for now)
//    * candidates for more general vivification could be found by near-misses
//      in subsumption
//    * subtle BUG: need to re-color ternaries when tern-vivifying something
//      more blue
//    * subtle not-quite-bug: marking shortened clause black and only re-adding
//      the shorter version much later is actually incorrect, because a black
//      clause will be immediately ignored by the PropEngine.

namespace dawn {

namespace {

std::pair<Lit, Lit> make_pair(Lit a, Lit b)
{
	assert(a.var() != b.var());
	return a < b ? std::pair(a, b) : std::pair(b, a);
}

struct Vivification
{
	Cnf &cnf_;
	PropEngineLight p;
	int64_t shortened = 0;    // number of lits removed
	int64_t strengthened = 0; // number of lits replaced by stronger one

	util::hash_map<std::pair<Lit, Lit>, util::small_vector<Lit, 1>> ternaries;

	explicit Vivification(Cnf &cnf, VivifyConfig const &config)
	    : cnf_(cnf), p(cnf)
	{
		if (config.with_ternary)
			for (Clause const &cl : cnf.clauses.all())
				if (cl.size() == 3 && cl.color() != Color::black)
				{
					ternaries[make_pair(cl[0], cl[1])].push_back(cl[2]);
					ternaries[make_pair(cl[0], cl[2])].push_back(cl[1]);
					ternaries[make_pair(cl[1], cl[2])].push_back(cl[0]);
				}
	}

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

	bool vivify_clause_ternary(std::vector<Lit> &cl)
	{
		assert(p.level() == 0);
		assert(!p.conflict);
		assert(cl.size() >= 4);

		for (size_t i = 0; i < cl.size(); ++i)
			for (size_t j = i + 1; j < cl.size(); ++j)
				if (auto t = ternaries.find(make_pair(cl[i], cl[j]));
				    t != ternaries.end())
				{
					p.mark();

					p.propagate_neg(std::span(cl).subspan(0, i));
					p.propagate_neg(std::span(cl).subspan(i + 1, j - i - 1));
					p.propagate_neg(std::span(cl).subspan(j + 1));

					if (p.conflict)
					{
						// not strictly a problem, but I dont want to deal with
						// it...
						fmt::print(
						    "c WARNING: inconsistent vivification state!\n");
						p.unroll();
						return false;
					}

					for (Lit a : t->second)
					{
						// some subsumption/tautology case we dont want to deal
						// with here
						for (Lit b : cl)
							if (a.var() == b.var())
								goto next;

						if (p.probe(a) == -1)
						{
							p.unroll();
							cl[i] = a.neg();
							cl[j] = cl.back();
							cl.pop_back();
							return true;
						}
					next:;
					}

					p.unroll();
				}
		return false;
	}
};

} // namespace

bool run_vivification(Cnf &cnf, VivifyConfig const &config,
                      std::stop_token stoken)
{
	if (!is_normal_form(cnf))
		return false;

	auto log = util::Logger("vivification");

	auto viv = Vivification(cnf, config);

	// NOTE: strengthening inplace is kinda fragile, so we binaries inplace is a
	// bit fragile (e.g. when there are equivalences). So we just add new
	// clauses, and rely on a later TBR run to clean up.
	std::vector<Lit> buf;
	ClauseStorage new_clauses;
	int nTernStrengthened = 0;

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
		if (cl.color() <= Color::red)
			continue;
		if (stoken.stop_requested())
			break;

		buf.assign(cl.begin(), cl.end());
		if (viv.vivify_clause(buf, config.with_binary))
		{
			assert(buf.size() <= cl.size());
			new_clauses.add_clause(buf, cl.color());
			cl.set_color(Color::black);
		}
		else if (config.with_ternary && buf.size() >= 4 &&
		         viv.vivify_clause_ternary(buf))
		{
			nTernStrengthened += 1;
			new_clauses.add_clause(buf, cl.color());
			cl.set_color(Color::black);
		}
	}

	if (new_clauses.empty())
	{
		log.info("-");
		return false;
	}

	cnf.clauses.prune_black();
	for (auto &cl : new_clauses.all())
		cnf.add_clause(cl.lits(), cl.color());

	log.info("removed {} lits, and bin-replaced {}, tern-replaced {}",
	         viv.shortened, viv.strengthened, nTernStrengthened);

	return viv.shortened + viv.strengthened;
}

} // namespace dawn
