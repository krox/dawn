#include "sat/probing.h"

#include "sat/propengine.h"
#include <climits>

using namespace dawn;

int dawn::probe_binary(Cnf &cnf)
{
	// basic structure:
	//   for (Lit a)
	//       for (Lit b)
	//           if (probe(a, b) == conflict)
	//               learn (-a,-b)
	// some optimizations:
	//   * If no conflict arises when propagating b and b implies b', then no
	//     conflict can arise when propagating b' instead of b. This is
	//     implemented using the 'seenB' array.
	//   * If a implies a', everything that is not-conflicting with a is also
	//     not-conflicting with a'. This is implemented by opportunistically
	//     re-using the 'seenB' array.
	//   * To maximize the effect of the above, both loops should be in
	//     topological order.
	//   * TODO: Dont 'just' learn (-a,-b) on conflict, but do actual conflict
	//     analysis. Currently, we are paying for the the full capability of
	//     'PropEngine' without using it.
	//   * TODO: be more careful which combinations of 'a' and 'b' need probing,
	//     depending on their position in the binary implication graph:
	//     - both 'a' and 'b' are sinks or isolated points: Can only conflict if
	//       they appear together in a ternary clause. This is handled in
	//       vivification already, so we can skip it here.
	//     - 'a' and 'b' belong to different weakly connected components: Only
	//       probe if both are sources.
	//   * TODO: randomize probing order a bit and implement a cutoff in order
	//     to do a partial run on large CNFs.

	auto log = util::Logger("bin-probing");
	auto p = PropEngine(cnf);
	auto top = TopOrder(cnf.bins);

	// sanity check. Not strictly necessary, but running (expensive) bin-probing
	// without (cheap) normalization first is a waste of time.
	if (!top.valid || p.conflict || !cnf.units.empty())
	{
		log.warning("CNF not normalized, skipping bin-probing.");
		return 0;
	}

	auto seenA = util::bit_vector(cnf.var_count() * 2);
	auto seenB = util::bit_vector(cnf.var_count() * 2);
	int nTries = 0;
	int nUnitFails = 0;
	int nBinFails = 0;

	for (Lit a : top.lits)
	{
		// UNSAT found
		assert(p.level() == 0);
		if (p.conflict) [[unlikely]]
		{
			cnf.add_empty();
			break;
		}

		seenB.clear();
		if (p.assign[a] || p.assign[a.neg()] || seenA[a])
			continue;

	use_this_a:
		seenA[a] = true;
		p.branch(a);
		assert(p.level() == 1);

		for (Lit b : top.lits)
		{
			// failed literal -> learn unit
			if (p.conflict)
			{
				nUnitFails += 1;
				p.unroll();
				cnf.add_unary(a.neg());
				p.propagate(a.neg());
				goto next_a;
			}
			if (p.assign[b] || p.assign[b.neg()] || seenB[b])
				continue;

			// arbitrary symmetry breaking
			if ((int)b > (int)a)
				continue;

			p.branch(b);
			assert(p.level() == 2);
			nTries += 1;

			if (p.conflict)
			{
				nBinFails += 1;
				p.unroll();
				cnf.add_binary(a.neg(), b.neg());
				p.add_clause({a.neg(), b.neg()}, Color::green);
				p.propagate(b.neg());
				continue;
			}

			// no conflict -> mark everything propagated as seen
			assert(p.level() == 2);
			for (Lit c : p.trail(2))
				seenB[c] = true;
			p.unroll();
		}
		assert(p.level() == 1);
		p.unroll();

		// Done with this 'a'. Try to get a weaker 'a' next in order to reuse
		// the 'seenB' array
		for (Lit a2 : p.bins[a.neg()])
			if (!(p.assign[a2] || p.assign[a2.neg()] || seenA[a2]))
			{
				a = a2;
				goto use_this_a;
			}

	next_a:;
	}

	log.info("found {} units and {} bins using {:.2f}M tries", nUnitFails,
	         nBinFails, nTries / 1e6);

	return nUnitFails + nBinFails;
}

// probe from a sink(!) a, going up the implication graph. Returns learnt
// unit or Lit::undef() if nothing was found.
namespace {
Lit probe(Lit a, PropEngineLight &p, util::bit_vector &done)
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

	for (Lit b : p.cnf.bins[a])
		if (Lit u = probe(b.neg(), p, done); u != Lit::undef())
		{
			p.unroll();
			return u;
		}

	p.unroll();
	return Lit::undef();
}
} // namespace

bool dawn::run_probing(Cnf &cnf)
{
	if (cnf.contradiction)
		return false;
	auto p = PropEngineLight(cnf);
	if (p.conflict)
		return true;

	auto done = util::bit_vector(p.cnf.var_count() * 2);

	int64_t nUnits = 0;
	for (Lit a : p.cnf.all_lits())
		if (!cnf.bins[a].empty() && cnf.bins[a.neg()].empty())
			if (Lit u = probe(a, p, done); u != Lit::undef())
			{
				nUnits += 1;
				cnf.add_unary(u);
				p.propagate(u);
				if (p.conflict)
					break;
			}

	assert(p.level() == 0);
	return nUnits || p.nHbr;
}
