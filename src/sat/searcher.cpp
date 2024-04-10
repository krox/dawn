#include "sat/searcher.h"

namespace dawn {
std::optional<Assignment>
Searcher::run(int maxConfl,
              util::function_view<void(std::span<const Lit>)> on_learnt)
{
	// util::StopwatchGuard _(p_.sat.stats.swSearch); TODO

	int64_t nConfl = 0;

	std::vector<Lit> buf;

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

			// analyze conflict
			int backLevel;
			uint8_t glue;
			p_.analyze_conflict(buf, &act_);
			if (config.otf >= 1)
				p_.shorten_learnt(buf, config.otf >= 2);
			on_learnt(buf);

			backLevel = p_.backtrack_level(buf);
			if (config.full_resolution)
			{
				glue = buf.size() > 255 ? 255 : (uint8_t)buf.size();
				assert(glue == p_.calcGlue(buf));
			}
			else
				glue = p_.calcGlue(buf);

			act_.decay_variable_activity();
			p_.stats.nLitsLearnt += buf.size();

			// unroll to apropriate level and propagate new learnt clause
			p_.unroll(backLevel, act_);

			if (buf.size() == 1)
			{
				assert(backLevel == 0);
				p_.propagateFull(buf[0], Reason::undef());
			}
			else
			{
				Reason r = p_.add_learnt_clause(buf, glue);
				p_.propagateFull(buf[0], r);
			}

			for (Lit x : p_.trail(p_.level()))
				polarity_[x.var()] = x.sign();

			buf.resize(0);
		}

		/** maxConfl reached -> unroll and exit */
		if (nConfl > maxConfl || interrupt)
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
} // namespace dawn