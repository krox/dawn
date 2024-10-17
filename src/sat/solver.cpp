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

/*
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
*/

/*
void clause_clean(Sat &sat, SolverConfig const &config, size_t nKeep)
{
    util::IntHistogram hist_glue, hist_size;
    for (auto &cl : sat.clauses.all())
    {
        if (cl.color == Color::blue)
            continue;
        hist_glue.add(cl.glue);
        hist_size.add(cl.size());
    }

    int cutoff_size, cutoff_glue;
    if (config.use_glue)
    {
        cutoff_size = config.max_learnt_size;
        cutoff_glue =
            std::min(hist_glue.find_nth(nKeep), config.max_learnt_glue);
    }
    else
    {
        cutoff_size =
            std::min(hist_size.find_nth(nKeep), config.max_learnt_size);
        cutoff_glue = config.max_learnt_glue;
    }

    auto pred = [&](Clause const &cl) {
        if (cl.color == Color::blue)
            return false;
        return cl.size() > cutoff_size || cl.glue > cutoff_glue;
    };
    sat.clauses.prune(pred);
}*/

/** run the full inprocessing */
void inprocess(Sat &sat, SolverConfig const &config, std::stop_token stoken)
{

	// printBinaryStats(sat);
	cleanup(sat);

	for (int iter = 0;
	     config.inprocessIters == 0 || iter < config.inprocessIters; ++iter)
	{
		bool change = false;

		if (config.subsume >= 1)
		{
			change |= run_subsumption(sat);
			cleanup(sat);
		}

		if (config.bin_probing)
		{
			change |= probeBinary(sat);
			cleanup(sat);
		}

		VivifyConfig vivConfig;
		if (config.vivify < 2)
			vivConfig.with_binary = false;

		if (config.vivify >= 1)
		{

			change |= run_vivification(sat, vivConfig, stoken);
			cleanup(sat); // bin-vivify really likes SCC and TBR before
		}

		if (config.bva >= 1)
		{
			change |= makeDisjunctions(sat);
			if (config.vivify >= 1)
				change |= run_vivification(sat, vivConfig, stoken);
			cleanup(sat);
		}

		if (!change)
			break;
	}
}

void preprocess(Sat &sat)
{
	// cheap search/strengthening
	cleanup(sat);
	run_subsumption(sat);
	cleanup(sat);

	// clause elimination (no resolution)
	// (pure/unused)
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
		cleanup(sat);
		run_subsumption(sat);
		cleanup(sat);
	}
}

int solve(Sat &sat, Assignment &sol, SolverConfig const &config,
          std::stop_token stoken)
{
	auto log = util::Logger("solver");

	cleanup(sat);
	log.info("starting solver with {} vars and {} clauses", sat.var_count(),
	         sat.clause_count());
	preprocess(sat);

	log.info("after preprocessing, got {} vars and {} clauses", sat.var_count(),
	         sat.clause_count());

	PropStats propStats;

	// it is kinda expensive to reconstruct the PropEngine at every restart,
	// so we keep it and only reconstruct after inprocessing or cleaning has run
	std::unique_ptr<Searcher> searcher = nullptr;

	// main solver loop
	for (int epoch = 0;; ++epoch)
	{
		auto nConfls = propStats.nConfls();
		if (searcher)
			nConfls += searcher->stats().nConfls();
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
			searcher->config.restart_type = config.restart_type;
			searcher->config.restart_base = config.restart_base;
			searcher->config.restart_mult = config.restart_mult;
		}

		// search for a number of conflicts
		auto result = searcher->run_epoch(2'000, stoken);
		if (auto assign = std::get_if<Assignment>(&result))
		{
			assert(!sat.contradiction);
			sol = sat.to_outer(*assign);
			sol.fix_unassigned();
			sat.extender.extend(sol);
			return 10;
		}
		else if (auto learnts = std::get_if<ClauseStorage>(&result))
		{
			for (auto &cl : learnts->all())
				sat.add_clause(cl, cl.color);
		}
		else
			assert(false);

		if (sat.contradiction)
			return 20;

		if (stoken.stop_requested())
		{
			log.info("interrupted. abort solver.");
			return 30;
		}
		bool needInprocess = (epoch + 1) % 5 == 0;

		// inprocessing
		if (needInprocess)
		{
			if (searcher)
			{
				propStats += searcher->stats();
				searcher.reset();
			}
			inprocess(sat, config, stoken);
		}
	}
}

} // namespace dawn
