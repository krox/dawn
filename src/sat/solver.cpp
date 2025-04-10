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
#include "util/gnuplot.h"
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
	std::optional<util::Gnuplot> plt;
	if (config.plot)
		plt.emplace();

	cleanup(sat);
	log.info("starting solver with {} vars and {} clauses", sat.var_count(),
	         sat.clause_count());
	preprocess(sat);

	log.info("after preprocessing, got {} vars and {} clauses", sat.var_count(),
	         sat.clause_count());

	PropStats propStats = {};

	// main solver loop
	for (int epoch = 0;; ++epoch)
	{
		// check limit
		if (propStats.nConfls() >= config.max_confls)
		{
			log.info("conflict limit reached. abort solver.");
			return 30;
		}

		Searcher::Config sconfig;
		sconfig.otf = config.otf;
		sconfig.branch_dom = config.branch_dom;
		sconfig.restart_type = config.restart_type;
		sconfig.restart_base = config.restart_base;
		sconfig.restart_mult = config.restart_mult;
		auto result = Searcher(sat, sconfig).run_epoch(10'000, stoken);

		log.info("learnt {} green clauses out of {} conflicts ({:.2f} "
		         "kconfls/s, {:.2f} "
		         "kprops/s)",
		         result.learnts.count(), result.stats.nConfls(),
		         result.stats.nConfls() / log.secs() / 1000,
		         result.stats.nProps() / log.secs() / 1000);

		propStats += result.stats;
		for (auto const &cl : result.learnts.all())
			sat.add_clause(cl, cl.color());

		if (result.solution)
		{
			assert(!sat.contradiction);
			sol = sat.to_outer(*result.solution);
			sol.fix_unassigned();
			sat.extender.extend(sol);
			return 10;
		}

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
			if (plt)
			{
				if (propStats.learn_events.size() >= 100)
				{
					plt->clear();
					plt->plot_range_data(
					    propStats.learn_events |
					        std::views::transform(&LearnEvent::size),
					    "learnt size");
					plt->plot_range_data(
					    propStats.learn_events |
					        std::views::transform(&LearnEvent::depth),
					    "depth");
				}
			}

			inprocess(sat, config, stoken);
		}
	}
}

} // namespace dawn
