#include "sat/solver.h"

#include "fmt/format.h"
#include "sat/binary.h"
#include "sat/disjunction.h"
#include "sat/elimination.h"
#include "sat/probing.h"
#include "sat/propengine.h"
#include "sat/searcher.h"
#include "sat/subsumption.h"
#include "sat/vivification.h"
#include <optional>

namespace dawn {

static void printHeader()
{
	fmt::print(
	    "c     vars    units     bins    longs  size   learnt  size  glue\n");
}

static void printLine(Sat &sat)
{
	// number of unary/binary clauses
	size_t unaryCount = sat.units.size();
	size_t binaryCount = 0;
	for (auto &b : sat.bins)
		binaryCount += b.size();
	binaryCount /= 2;

	// number/size/glue of irred/learnt long clauses
	size_t longCount = 0;
	size_t learntCount = 0;
	size_t longLits = 0;
	size_t learntLits = 0;
	size_t learntGlue = 0;

	for (auto &cl : sat.clauses.all())
		if (cl.irred())
		{
			longCount += 1;
			longLits += cl.size();
		}
		else
		{
			learntCount += 1;
			learntLits += cl.size();
			learntGlue += cl.glue;
		}

	fmt::print(
	    "c {:#8} {:#8} {:#8} {:#8} {:5.2f} {:#8} {:5.2f} {:5.2f} {:8.2f} MiB\n",
	    sat.var_count(), unaryCount, binaryCount, longCount,
	    (double)longLits / longCount, learntCount,
	    (double)learntLits / learntCount, (double)learntGlue / learntCount,
	    sat.memory_usage() / 1024. / 1024.);
}

int luby(int i)
{
	assert(i > 0);
	if (__builtin_popcount(i + 1) == 1)
		return (i + 1) / 2;
	else
		return luby(i - (1 << (31 - __builtin_clz(i))) + 1);
}

int restartSize(int iter, SolverConfig const &config)
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

void cleanClausesSize(ClauseStorage &clauses, size_t nKeep)
{
	std::vector<std::vector<CRef>> list(200);
	for (auto [ci, cl] : clauses.enumerate())
	{
		if (cl.irred())
			continue;
		if (cl.size() >= list.size())
		{
			cl.set_removed();
			continue;
		}
		list[cl.size()].push_back(ci);
	}

	size_t count = 0;
	size_t len = 0;
	for (; len < list.size() && count < nKeep; len++)
		count += list[len].size();
	for (; len < list.size(); len++)
		for (CRef ci : list[len])
			clauses[ci].set_removed();
}

void cleanClausesGlue(ClauseStorage &clauses, size_t nKeep)
{
	std::vector<std::vector<CRef>> list(200);
	for (auto [ci, cl] : clauses.enumerate())
	{
		if (cl.irred())
			continue;
		if (cl.glue >= list.size())
		{
			cl.set_removed();
			continue;
		}
		list[cl.glue].push_back(ci);
	}

	size_t count = 0;
	size_t len = 0;
	for (; len < list.size() && count < nKeep; len++)
		count += list[len].size();
	for (; len < list.size(); len++)
		for (CRef ci : list[len])
			clauses[ci].set_removed();
}

void maybe_clause_clean(Sat &sat, SolverConfig const &config, size_t nConfls)
{
	for (auto &cl : sat.clauses.all())
	{
		if (cl.irred())
			continue;
		if (cl.size() > config.max_learnt_size ||
		    cl.glue > config.max_learnt_glue)
			cl.set_removed();
	}
	if ((int64_t)sat.long_count_red() > config.max_learnt)
	{
		if (config.use_glue)
			cleanClausesGlue(sat.clauses, config.max_learnt);
		else
			cleanClausesSize(sat.clauses, config.max_learnt);
	}
	if (sat.long_count_red() > nConfls)
	{
		if (config.use_glue)
			cleanClausesGlue(sat.clauses, nConfls / 8);
		else
			cleanClausesSize(sat.clauses, nConfls / 8);
	}
}

/** run the full inprocessing */
void inprocess(Sat &sat, SolverConfig const &config)
{

	// printBinaryStats(sat);
	cleanup(sat);

	for (int iter = 0;
	     config.inprocessIters == 0 || iter < config.inprocessIters; ++iter)
	{
		bool change = false;
		// failed literal probing settings:
		// 0 = none
		// 1 = only run while very successful
		// 2 = run until everything is found
		// 3 = also run binary probing
		// if (config.probing > 0)
		//	change |= probe(sat, true, config.probing >= 2 ? 0 : 10000);
		if (config.probing)
			change |= intree_probing(sat);

		if (config.subsume >= 1)
			change |= run_subsumption(sat);

		if (config.probing >= 3)
			change |= probeBinary(sat);

		VivifyConfig vivConfig;
		vivConfig.with_binary = config.vivify >= 2;
		vivConfig.irred_only = config.vivify <= 2;
		if (config.vivify >= 1)
		{
			if (vivConfig.with_binary)
				run_binary_reduction(sat);
			change |= run_vivification(sat, vivConfig);
		}

		if (config.bva >= 1)
		{
			change |= makeDisjunctions(sat);
			if (config.vivify >= 1)
				change |= run_vivification(sat, vivConfig);
		}

		// cleanup
		// (do this last, because it cant lead to anything new for the other
		// passes)
		if (config.tbr > 0)
			run_binary_reduction(sat);

		if (!change)
			break;
	}

	// Very rarely, normal form is destroyed without the passes itself noticing.
	// Not sure why, guessing lhbr in probing/vivification?
	cleanup(sat);
}

void preprocess(Sat &sat)
{
	// cheap search/strengthening
	intree_probing(sat, 10000);
	// probe(sat, true, 10000);
	run_subsumption(sat);

	// clause elimination (no resolution)
	// (pure/unused)
	run_binary_reduction(sat);
	EliminationConfig elimConfig = {};
	elimConfig.level = 1;
	run_elimination(sat, elimConfig);

	// elimination and subsumption influence each other quite a bit. SatELite
	// alternatates them until fixed point. Cryptominisat seems to do multiple
	// passes with increasing max-growth. For now, we just copy that strategy...
	for (int growth : {0, 8, 16})
	{
		run_blocked_clause_elimination(sat);
		elimConfig.level = 5;
		elimConfig.growth = growth;
		run_elimination(sat, elimConfig);

		// little bit of searching
		intree_probing(sat);
		// probe(sat, true, 10000);
		run_subsumption(sat);
		run_binary_reduction(sat);
	}
}

int solve(Sat &sat, Assignment &sol, SolverConfig const &config)
{
	// NOTE: dont do too much preprocessing before the first round a searching.
	//       CDCL tends to be quite efficient compared to exhaustive probing.

	util::StopwatchGuard _(sat.stats.swTotal);
	auto log = Logger("solver");

	cleanup(sat);
	log.info("starting with {} vars and {} clauses", sat.var_count(),
	         sat.clause_count());
	preprocess(sat);

	log.info("after preprocessing {} vars and {} clauses", sat.var_count(),
	         sat.clause_count());

	printHeader();

	PropStats propStats;
	int64_t lastInprocess = 0;
	int64_t lastPrint = 0;

	// we use "total length of irreducible long clauses" as metric for progress,
	// as it always decreases with serching/subsumption/... . After some
	// progress is made, we run elimination again.
	int64_t lastElimination = sat.lit_count_irred();

	// it is kinda expensive to reconstruct the PropEngine at every restart,
	// so we keep it and only reconstruct after inprocessing or cleaning has run
	std::unique_ptr<Searcher> searcher = nullptr;

	auto on_learnt = [&](std::span<const Lit> lits) {
		sat.add_clause(lits, false);
	};

	// main solver loop
	for (int iter = 1;; ++iter)
	{
		auto nConfls = propStats.nConfls();
		if (searcher)
			nConfls += searcher->p_.stats.nConfls();
		// check limit
		if (nConfls >= config.max_confls)
		{
			log.info("conflict limit reached. abort solver.");
			return 30;
		}

		if (searcher == nullptr)
		{
			searcher = std::make_unique<Searcher>(sat);
			searcher->config.otf = config.otf;
			searcher->config.branch_dom = config.branch_dom;
			searcher->config.full_resolution = config.full_resolution;
		}

		// search for a number of conflicts
		if (auto tmp = searcher->run(restartSize(iter, config), on_learnt); tmp)
		{
			assert(!sat.contradiction);
			sol = sat.to_outer(*tmp);
			sol.fix_unassigned();
			sat.extender.extend(sol);
			return 10;
		}

		if (sat.contradiction)
			return 20;

		if (interrupt)
		{
			log.info("interrupted. abort solver.");
			return 30;
		}
		bool needInprocess = nConfls > lastInprocess + 20000;

		if (needInprocess || nConfls > lastPrint + 1000)
		{
			printLine(sat);
			lastPrint = nConfls;
		}

		// inprocessing
		if (needInprocess)
		{
			if (searcher)
			{
				propStats += searcher->p_.stats;
				searcher.reset();
			}
			lastInprocess = nConfls;
			inprocess(sat, config);

			if (sat.lit_count_irred() <= 0.95 * lastElimination)
			{
				log.info("removing all learnt and restart everything\n");
				for (auto &cl : sat.clauses.all())
					if (!cl.irred())
						cl.set_removed();
				cleanup(sat);
				preprocess(sat);
				log.info("after preprocessing {} vars and {} clauses\n",
				         sat.var_count(), sat.clause_count());
				lastElimination = sat.lit_count_irred();
			}
			else
				maybe_clause_clean(sat, config, nConfls);

			sat.clauses.compactify();

			printHeader();
			printLine(sat);
		}
	}
}

} // namespace dawn
