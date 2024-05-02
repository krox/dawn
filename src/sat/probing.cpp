#include "sat/probing.h"

#include "sat/binary.h"
#include "sat/propengine.h"
#include <climits>

namespace dawn {
int probeBinary(Cnf &cnf)
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
	// util::StopwatchGuard swg(sat.stats.swProbing); TODO
	auto log = Logger("bin-probing");

	PropEngine p(cnf);
	if (p.conflict)
		return 0;

	auto top = TopOrder(cnf);
	auto seenA = util::bit_vector(cnf.var_count() * 2);
	auto seenB = util::bit_vector(cnf.var_count() * 2);
	std::vector<Lit> buf;
	int nTries = 0;
	int nFails = 0;

	auto backtrack = [&cnf, &p, &buf, &nFails]() {
		p.analyze_conflict(buf, nullptr);
		p.shorten_learnt(buf, true);
		auto back = p.backtrack_level(buf);
		p.unroll(back);
		auto reason = p.add_clause(buf, Color::green, 2);
		cnf.add_clause(buf, Color::green);
		p.propagateFull(buf[0], reason);
		buf.resize(0);
	};

	for (Lit a : top.lits)
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

		for (Lit b : top.lits)
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
		for (Lit a2 : p.bins[a.neg()])
			if (!(p.assign[a2] || p.assign[a2.neg()] || seenA[a2]))
			{
				a = a2;
				goto use_this_a;
			}

	next_a:;
	}

	if (nFails == 0)
		log.info("-");
	else
	{
		log.info("found {} failing bins using {:.2f}M tries", nFails,
		         nTries / 1e6);
	}

	return nFails;
}

struct IntreeProbing
{
	Cnf &cnf;
	PropEngineLight p;
	util::bit_vector done;

	IntreeProbing(Cnf &s) : cnf(s), p(s), done(s.var_count() * 2) {}

	// probe from a sink(!) a, going up the implication graph. Returns learnt
	// unit or Lit::undef() if nothing was found.
	Lit probe(Lit a)
	{
		assert(a.proper());
		if (done[a])
			return Lit::undef();
		done[a] = true;

		assert(!p.conflict);
		p.mark();
		p.propagate_with_hbr(a);
		if (p.conflict)
		{
			p.unroll();
			return a.neg();
		}

		for (Lit b : cnf.bins[a])
			if (Lit u = probe(b.neg()); u != Lit::undef())
			{
				p.unroll();
				return u;
			}

		p.unroll();
		return Lit::undef();
	}
};

bool intree_probing(Cnf &cnf)
{
	// util::StopwatchGuard swg(sat.stats.swProbing); TODO
	auto log = Logger("probing");
	auto p = IntreeProbing(cnf);

	if (p.p.conflict)
		return false;

	int64_t nUnits = 0;
	for (Lit a : cnf.all_lits())
		if (!cnf.bins[a].empty() && cnf.bins[a.neg()].empty())
			if (Lit u = p.probe(a); u != Lit::undef())
			{
				nUnits += 1;
				cnf.add_unary(u);
				p.p.propagate(u);
				if (p.p.conflict)
					return true;
			}

	if (nUnits || p.p.nHbr)
	{
		log.info("found {} failing lits and {} hyper bins", nUnits, p.p.nHbr);
		return true;
	}
	else
	{
		log.info("-");
		return false;
	}
}

} // namespace dawn
