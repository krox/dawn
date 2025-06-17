#include "CLI/CLI.hpp"
#include "sat/assignment.h"
#include "sat/cnf.h"
#include <string>

using namespace dawn;

namespace {

struct Options
{
	// NOTE: 4.26 is roughly the hardest clause/variable ratio for random
	//       3-sat instances, and also the phase transition between mostly
	//       satisfiable and mostly unsatisfiable instances. This program only
	//       generates satisfiable instances, so this fact might not be exactly
	//       applicable, but it is a reasonable default value nontheless.

	int nvars = 100;
	int nclauses = 0;
	float ratio = 4.26;
	std::string seed;
};

void run_gen_command(Options opt)
{
	if (opt.seed.empty())
		opt.seed = fmt::format("{}", std::random_device()());
	if (opt.nclauses == 0)
		opt.nclauses = int(opt.ratio * opt.nvars);

	util::xoshiro256 rng(opt.seed);
	std::uniform_int_distribution<uint32_t> litDist(0, 2 * opt.nvars - 1);
	std::bernoulli_distribution coinDist(0.5);

	// random solution
	Assignment sol(opt.nvars);
	for (int i = 0; i < opt.nvars; ++i)
		sol.set(Lit(i, coinDist(rng)));

	// generate clauses that are satisfied by the solution
	Cnf sat(opt.nvars);
	std::vector<Lit> cl;
	for (int ci = 0; ci < opt.nclauses;)
	{
		while (cl.size() < 3)
		{
			Lit a = Lit(litDist(rng));
			for (Lit b : cl)
				if (a.var() == b.var())
					goto next_lit;
			cl.push_back(a);
		next_lit:;
		}

		if (sol.satisfied(cl))
		{
			++ci;
			sat.add_clause(cl, Color::blue);
		}

		cl.resize(0);
	}

	fmt::print("{}", sat);
}
} // namespace

void setup_gen_command(CLI::App &app)
{
	auto opt = std::make_shared<Options>();

	app.add_option("nvars", opt->nvars, "number of variables");
	app.add_option("nclauses", opt->nclauses, "number of clauses");
	app.add_option("--ratio", opt->ratio,
	               "ratio of clauses to variables (default = 4.26)");

	app.add_option("--seed", opt->seed, "seed for random number generator");

	app.callback([opt]() { run_gen_command(*opt); });
}
