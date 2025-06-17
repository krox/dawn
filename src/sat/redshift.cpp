#include "sat/redshift.h"
#include "sat/elimination.h"
#include "sat/propengine.h"

using namespace dawn;

namespace {

class Redshift
{
	// check if cl is blocked on a (classic definition, i.e., only exact
	// tautologies)
	bool is_blocked(Clause const &cl, Lit a) const;

	bool is_blocked_np(Lit a);

  public:
	util::Logger log = util::Logger("redshift");
	Sat &sat;
	PropEngineLight p;
	std::vector<std::vector<CRef>> occs;

	int64_t nBC = 0, nRUP = 0, nRAT = 0;

	Redshift(Sat &sat_) : sat(sat_), p(sat, false), occs(sat.var_count() * 2)
	{
		for (auto [i, cl] : sat.clauses.enumerate())
			if (cl.color() == Color::blue)
			{
				for (Lit a : cl.lits())
					occs[a].push_back(i);
				p.attach_clause(i);
			}
	}

	// pre-condition: cl is not attached to the prop engine
	// * returns true if cl is redundant, false otherwise
	// * if true, the clause is not re-colored, but appropriate rules are
	//   added to the reconstruction
	bool is_redundant(Clause const &cl);
};

bool Redshift::is_blocked(Clause const &cl, Lit a) const
{
	for (CRef i : occs[a.neg()])
		if (sat.clauses[i].color() == Color::blue)
			if (!is_resolvent_tautological_unsorted(cl, sat.clauses[i].lits()))
				return false;
	for (Lit b : sat.bins[a.neg()])
		if (!cl.contains(b.neg()))
			return false;
	return true;
}

bool Redshift::is_blocked_np(Lit a)
{
	for (CRef i : occs[a.neg()])
		if (sat.clauses[i].color() == Color::blue)
			if (p.probe_neg(sat.clauses[i], a.neg()) != -1)
				return false;
	for (Lit b : sat.bins[a.neg()])
		if (p.probe(b.neg()) != -1)
			return false;
	return true;
}

bool Redshift::is_redundant(Clause const &cl)
{
	// NOTE: 'RUP' and 'BC' are not mutually exclusive. Kinda arbitrary which to
	// check first. Though 'RAT' is a superset of both, so it should not be too
	// meaningful in the end.
	assert(cl.color() == Color::blue);
	for (Lit a : cl)
		if (is_blocked(cl, a))
		{
			sat.add_rule(cl, a);
			nBC += 1;
			return true;
		}

	p.mark();

	if (int r = p.propagate_neg(cl); r == -1)
	{
		p.unroll();
		nRUP += 1;
		return true;
	}

	for (Lit a : cl)
		if (is_blocked_np(a))
		{
			sat.add_rule(cl, a);
			nRAT += 1;
			p.unroll();
			return true;
		}

	p.unroll();
	return false;
};
} // namespace

void dawn::run_redshift(Sat &sat, redshift_config const &config)
{
	(void)config;

	// Sanity check: running redshift before basic cleanup would be weird, and
	// units might mess with the clause_attach/detach logic
	if (sat.contradiction)
		return;
	assert(sat.units.empty());

	auto redshift = Redshift(sat);

	for (auto [i, cl] : sat.clauses.enumerate())
		if (cl.color() == Color::blue)
		{
			redshift.p.detach_clause(i);

			if (redshift.is_redundant(cl))
				cl.set_color(Color::green);
			else
				redshift.p.attach_clause(i);
		}

	redshift.log.info("removed {} BC, {} RUP, {} RAT", redshift.nBC,
	                  redshift.nRUP, redshift.nRAT);
}