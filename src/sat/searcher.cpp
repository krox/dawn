#include "sat/searcher.h"

namespace dawn {

namespace {

// https://oeis.org/A182105
int luby(int i)
{
	assert(i > 0);
	if (__builtin_popcount(i + 1) == 1)
		return (i + 1) / 2;
	else
		return luby(i - (1 << (31 - __builtin_clz(i))) + 1);
}

int restartSize(int iter, Searcher::Config const &config)
{
	assert(iter >= 1);
	switch (config.restart_type)
	{
	case RestartType::constant:
		return config.restart_base;
	case RestartType::linear:
		return iter * config.restart_base;
	case RestartType::geometric:
		return std::pow(config.restart_mult, iter - 1) * config.restart_base;
	case RestartType::luby:
		return luby(iter) * config.restart_base;
	default:
		assert(false);
	}
}

} // namespace

Lit Searcher::choose_branch()
{
	// choose a branching variable
	// int branch = p.unassignedVariable();
	int branchVar = -1;

	while (!act_.empty())
	{
		int v = act_.pop();
		if (p_.assign[Lit(v, false)] || p_.assign[Lit(v, true)])
			continue;

		// check the heap(very expensive, debug only)
		// for (int i = 0; i < sat.varCount(); ++i)
		//	assert(assign[Lit(i, false)] || assign[Lit(i, true)] ||
		//	       sat.activity[i] <= sat.activity[v]);

		branchVar = v;
		break;
	}

	// no unassigned left -> solution is found
	if (branchVar == -1)
		return Lit::undef();

	Lit branchLit = Lit(branchVar, polarity_[branchVar]);

	if (config_.branch_dom >= 1)
	{
		// NOTE: the counter avoids infinite loop due to equivalent vars
		// TODO: think again about the order of binary clauses. That has an
		//       influence here
		int counter = 0;
	again:
		for (Lit l : p_.bins[branchLit]) // l.neg implies branchLit
			if (!p_.assign[l])
				if (config_.branch_dom >= 2 ||
				    polarity_[l.var()] == l.neg().sign())
				{
					branchLit = l.neg();
					if (++counter < 5)
						goto again;
					else
						break;
				}
	}

	return branchLit;
}

Color Searcher::on_learnt(std::span<const Lit> lits)
{
	if ((int)lits.size() <= config_.green_cutoff)
	{
		ngreen += 1;
		learnts_.add_clause(lits, Color::green);
		return Color::green;
	}
	else
	{
		nred += 1;
		return Color::red;
	}
}

void Searcher::run_restart(std::stop_token stoken)
{
	// util::StopwatchGuard _(p_.sat.stats.swSearch); TODO
	int max_confls = restartSize(++iter_, config_);
	int64_t nConfl = 0;
	assert(p_.level() == 0);

	while (true)
	{
		// handle conflicts
		while (p_.conflict)
		{
			nConfl += 1;

			// level 0 conflict -> UNSAT
			if (p_.level() == 0)
			{
				on_learnt({});
				return;
			}
			assert(p_.conflict && p_.level() > 0);

			// analyze conflict
			p_.analyze_conflict(buf_, &act_, config_.otf);
			assert(buf_.size() > 0);

			auto color = on_learnt(buf_);
			int backLevel = p_.backtrack_level(buf_);

			// unroll to apropriate level and propagate new learnt clause
			p_.unroll(backLevel, act_);

			Reason r = Reason::undef();
			if (buf_.size() > 1)
				r = p_.add_clause(buf_, color);
			for (Lit x : p_.propagate(buf_[0], r))
				polarity_[x.var()] = x.sign();
		}

		// maxConfl reached -> unroll and exit
		// NOTE: by convention we handle all conflicts before returning, thus
		//       max_confls can be (slightly) exceeded in case one conflict
		//       leads to another immediately.
		if (nConfl >= max_confls ||
		    (nConfl % 16 == 0 && stoken.stop_requested()))
		{
			if (p_.level() > 0)
				p_.unroll(0, act_);
			return;
		}

		// choose and propagate next branch
		Lit branchLit = choose_branch();
		if (branchLit == Lit::undef())
		{
			solution_ = p_.assign;
			return;
		}
		// TODO: question: should we set polarity in case of conflict?
		//       (same applies when handling conflicts by adding new learnt)
		for (Lit x : p_.branch(branchLit))
			polarity_[x.var()] = x.sign();
	}
}

void Searcher::run_epoch(int64_t max_confls, std::stop_token stoken)
{
	auto log = util::Logger("searcher");

	p_.stats.clear();

	while (p_.stats.nConfls() < max_confls && !stoken.stop_requested())
	{
		run_restart(stoken);
		if (solution_)
		{
			log.info("found solution");
			return;
		}
		else if (p_.conflict)
		{
			log.info("found contradiction");
			learnts_.add_clause({}, Color::green);
			return;
		}
	}

	util::Stopwatch sw;
	sw.start();
	for (Clause &cl : p_.clauses.all())
		if (cl.color == Color::red)
			cl.color = Color::black;
	sw.stop();

	log.info(
	    "learnt {} green clauses out of {} conflicts ({:.2f} kconfls/s, {:.2f} "
	    "kprops/s, {:.2f}s of cleaning)",
	    ngreen, ngreen + nred, p_.stats.nConfls() / log.secs() / 1000,
	    p_.stats.nProps() / log.secs() / 1000, sw.secs());
}

} // namespace dawn