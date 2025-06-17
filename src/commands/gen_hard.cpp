#include "CLI/CLI.hpp"
#include "sat/assignment.h"
#include "sat/cnf.h"
#include <string>

using namespace dawn;

namespace {

struct Options
{
	int nvars = 100;
	int group_size = 5;
	int partitions = 3;
	std::string seed;
};

void add_max_one_clause(Cnf &cnf, Lit a, std::span<const Lit> tail)
{
	for (Lit b : tail)
		cnf.add_binary(a.neg(), b.neg());
	for (int i = 0; i < (int)tail.size(); ++i)
		for (int j = i + 1; j < (int)tail.size(); ++j)
			cnf.add_binary(tail[i].neg(), tail[j].neg());
}

void add_min_one_clause(Cnf &cnf, Lit a, std::span<const Lit> tail)
{
	static std::vector<Lit> cl;
	cl.assign(tail.begin(), tail.end());
	cl.push_back(a);
	cnf.add_clause(cl, Color::blue);
}

void run_command(Options opt)
{
	if (opt.seed.empty())
		opt.seed = fmt::format("{}", std::random_device()());

	util::xoshiro256 rng(opt.seed);
	std::uniform_int_distribution<uint32_t> litDist(0, 2 * opt.nvars - 1);
	std::bernoulli_distribution coinDist(0.5);

	// round up to the next multiple of group_size
	int nGroups = (opt.nvars + opt.group_size - 1) / opt.group_size;
	opt.nvars = nGroups * opt.group_size;

	// in the solution, the first nGroups Lits are true, the rest are false
	std::vector<Lit> pos;
	std::vector<Lit> neg;
	for (int i = 0; i < opt.nvars;)
	{
		pos.push_back(Lit(i++, false));
		for (int j = 1; j < opt.group_size; ++j)
			neg.push_back(Lit(i++, false));
	}
	assert((int)pos.size() == nGroups);
	assert((int)(pos.size() + neg.size()) == opt.nvars);

	auto cnf = Cnf(opt.nvars);

	// first partition: Permit at most one true variable in each group
	for (int g = 0; g < nGroups; ++g)
		add_max_one_clause(cnf, pos[g],
		                   {neg.begin() + g * (opt.group_size - 1),
		                    neg.begin() + (g + 1) * (opt.group_size - 1)});

	// further partitions: Require at least one true variable in each group
	for (int iter = 1; iter < opt.partitions; ++iter)
	{
		std::shuffle(pos.begin(), pos.end(), rng);
		std::shuffle(neg.begin(), neg.end(), rng);
		for (int g = 0; g < nGroups; ++g)
			add_min_one_clause(cnf, pos[g],
			                   {neg.begin() + g * (opt.group_size - 1),
			                    neg.begin() + (g + 1) * (opt.group_size - 1)});
	}

	fmt::print("{}", cnf);
}
} // namespace

void setup_gen_hard_command(CLI::App &app)
{
	auto opt = std::make_shared<Options>();

	app.add_option("nvars", opt->nvars, "number of variables");
	app.add_option("-g", opt->group_size, "group size (>= 2)");
	app.add_option("-p", opt->partitions, "number of partitions (>= 2)");
	app.add_option("--seed", opt->seed, "seed for random number generator");

	app.callback([opt]() { run_command(*opt); });
}
