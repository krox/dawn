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

void Searcher::handle_conflict(
    util::function_view<Color(std::span<const Lit>)> on_learnt)
{
	assert(p_.conflict && p_.level() > 0);

	// analyze conflict
	uint8_t glue;
	buf_.resize(0);
	p_.analyze_conflict(buf_, &act_);
	assert(buf_.size() > 0);
	if (config.otf >= 1)
		p_.shorten_learnt(buf_, config.otf >= 2);
	auto color = on_learnt(buf_);
	int backLevel = p_.backtrack_level(buf_);
	if (config.full_resolution)
	{
		glue = buf_.size() > 255 ? 255 : (uint8_t)buf_.size();
		assert(glue == p_.calcGlue(buf_));
	}
	else
		glue = p_.calcGlue(buf_);

	act_.decay_variable_activity();
	p_.stats.nLitsLearnt += buf_.size();

	// unroll to apropriate level and propagate new learnt clause
	p_.unroll(backLevel, act_);

	if (buf_.size() == 1)
	{
		assert(backLevel == 0);
		p_.propagateFull(buf_[0], Reason::undef());
	}
	else
	{
		Reason r = p_.add_clause(buf_, color, glue);
		p_.propagateFull(buf_[0], r);
	}

	for (Lit x : p_.trail(p_.level()))
		polarity_[x.var()] = x.sign();
}

std::optional<Assignment> Searcher::run_restart(
    util::function_view<Color(std::span<const Lit>)> on_learnt,
    std::stop_token stoken)
{
	// util::StopwatchGuard _(p_.sat.stats.swSearch); TODO
	int max_confls = restartSize(++iter_, config);
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
				return {};
			}
			handle_conflict(on_learnt);
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
			return {};
		}

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
			return p_.assign;

		Lit branchLit = Lit(branchVar, polarity_[branchVar]);

		if (config.branch_dom >= 1)
		{
			// NOTE: the counter avoids infinite loop due to equivalent vars
			// TODO: think again about the order of binary clauses. That has an
			//       influence here
			int counter = 0;
		again:
			for (Lit l : p_.bins[branchLit]) // l.neg implies branchLit
				if (!p_.assign[l])
					if (config.branch_dom >= 2 ||
					    polarity_[l.var()] == l.neg().sign())
					{
						branchLit = l.neg();
						if (++counter < 5)
							goto again;
						else
							break;
					}
		}

		// propagate branch
		p_.branch(branchLit);
		for (Lit x : p_.trail(p_.level()))
			polarity_[x.var()] = x.sign();
	}
}

std::variant<ClauseStorage, Assignment>
Searcher::run_epoch(int64_t max_confls, std::stop_token stoken)
{
	auto log = util::Logger("searcher");
	ClauseStorage learnts;
	int64_t ngreen = 0, nred = 0;
	auto on_learnt = [&](std::span<const Lit> cl) -> Color {
		if ((int)cl.size() <= config.green_cutoff)
		{
			ngreen += 1;
			learnts.add_clause(cl, Color::green);
			return Color::green;
		}
		else
		{
			nred += 1;
			return Color::red;
		}
	};

	p_.stats.clear();

	while (p_.stats.nConfls() < max_confls && !stoken.stop_requested())
	{
		if (auto assign = run_restart(on_learnt, stoken))
		{
			log.info("found solution");
			return *std::move(assign);
		}
		else if (p_.conflict)
		{
			log.info("found contradiction");
			return ClauseStorage();
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
	return learnts;
}

} // namespace dawn