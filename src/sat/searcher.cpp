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

Searcher::Searcher(Cnf const &cnf, Config const &config)
    : p_(cnf), act_(cnf.var_count()), polarity_(cnf.var_count()),
      config_(config)
{
	auto rng = std::default_random_engine(config.seed);
	std::uniform_int_distribution<int> dist(0, 1);
	if (config_.starting_polarity == Polarity::random)
	{
		for (int i = 0; i < cnf.var_count(); ++i)
			polarity_[i] = dist(rng);
	}
	else if (config_.starting_polarity == Polarity::negative)
	{
		for (int i = 0; i < cnf.var_count(); ++i)
			polarity_[i] = false;
	}
	else
	{
		assert(config_.starting_polarity == Polarity::positive);
		for (int i = 0; i < cnf.var_count(); ++i)
			polarity_[i] = true;
	}
}

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

void Searcher::run_restart(Result &result, std::stop_token stoken)
{
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
				result.learnts.add_clause({}, Color::green);
				return;
			}
			assert(p_.conflict && p_.level() > 0);

			// analyze conflict
			p_.analyze_conflict(buf_, &act_, config_.otf);
			assert(buf_.size() > 0);

			auto color = (int)buf_.size() <= config_.green_cutoff ? Color::green
			                                                      : Color::red;
			if (color == Color::green)
				result.learnts.add_clause(buf_, color);
			int backLevel = p_.backtrack_level(buf_);

			// unroll to apropriate level and propagate new learnt clause
			p_.unroll(backLevel, act_);

			Reason r = Reason::undef();
			if (buf_.size() > 1)
				r = p_.add_clause(buf_, color);

			// policy: do not save polarity in case of conflict
			if (p_.propagate(buf_[0], r) != -1)
				for (Lit x : p_.trail(p_.level()))
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
			result.solution = p_.assign;
			return;
		}
		// TODO: question: should we set polarity in case of conflict?
		//       (same applies when handling conflicts by adding new learnt)
		if (p_.branch(branchLit) != -1)
			for (Lit x : p_.trail(p_.level()))
				polarity_[x.var()] = x.sign();
	}
}

Searcher::Result Searcher::run_epoch(int64_t max_confls, std::stop_token stoken)
{
	Result result;

	p_.stats.clear();

	while (p_.stats.nConfls() < max_confls && !stoken.stop_requested() &&
	       !p_.conflict && !result.solution)
		run_restart(result, stoken);

	result.stats = p_.stats;
	p_.stats.clear();

	// crude cleaning: remove everything not green
	// TODO: while setting color=black does make PropEngine ignore the clauses,
	// they are never actually removed?
	for (Clause &cl : p_.clauses.all())
		if (cl.color() == Color::red)
			cl.set_color(Color::black);

	return result;
}

} // namespace dawn