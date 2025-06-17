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

// run the full inprocessing
void inprocess(Sat &sat, SolverConfig const &config, std::stop_token stoken)
{
	// printBinaryStats(sat);
	cleanup(sat);

	if (config.subsume >= 1)
	{
		run_subsumption(sat);
		cleanup(sat);
	}

	if (config.bin_probing)
	{
		probeBinary(sat);
		cleanup(sat);
	}

	VivifyConfig vivConfig;
	if (config.vivify < 2)
		vivConfig.with_binary = false;

	if (config.vivify >= 1)
	{
		run_vivification(sat, vivConfig, stoken);
		cleanup(sat); // bin-vivify really likes SCC and TBR before
	}

	if (config.bva >= 1)
	{
		makeDisjunctions(sat);
		if (config.vivify >= 1)
			run_vivification(sat, vivConfig, stoken);
		cleanup(sat);
	}
}

void preprocess(Sat &sat)
{
	// elimination and subsumption influence each other quite a bit. SatELite
	// alternatates them until fixed point. Cryptominisat seems to do multiple
	// passes with increasing max-growth. For now, we just copy that strategy...

	cleanup(sat);
	run_subsumption(sat);
	cleanup(sat);
	print_stats(sat);

	run_elimination(sat, {.growth = 0, .max_resolvents = 10'000});
	cleanup(sat);
	run_subsumption(sat);
	cleanup(sat);
	print_stats(sat);

	run_elimination(sat, {.growth = 8, .max_resolvents = 10'000});
	cleanup(sat);
	run_subsumption(sat);
	cleanup(sat);
	print_stats(sat);

	run_elimination(sat, {.growth = 16, .max_resolvents = 10'000});
	cleanup(sat);
	run_subsumption(sat);
	cleanup(sat);
	print_stats(sat);
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
		util::Stopwatch sw;
		sw.start();
		auto result = Searcher(sat, sconfig).run_epoch(10'000, stoken);
		sw.stop();

		log.info("learnt {} green clauses out of {} conflicts ({:.2f} "
		         "kconfls/s, {:.2f} kprops/s)",
		         result.learnts.count(), result.stats.nConfls(),
		         result.stats.nConfls() / sw.secs() / 1000,
		         result.stats.nProps() / sw.secs() / 1000);

		propStats += result.stats;
		for (auto const &cl : result.learnts.all())
			sat.add_clause(cl, cl.color());

		if (result.solution)
		{
			assert(!sat.contradiction);
			sol = sat.reconstruct_solution(*result.solution);
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
			print_stats(sat);
		}
	}
}

} // namespace dawn
