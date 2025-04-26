#include "CLI/CLI.hpp"
#include "sat/assignment.h"
#include "sat/sat.h"
#include <string>

using namespace dawn;

namespace {

struct Options
{
	int width = 50;
	int height = 50;
	float xor_ratio = 0.5;
	std::string seed;
};

void run_command(Options opt)
{
	// NOTE: this simply builds 'height' layers of 'width' variables each. Each
	// variable is defined by random AND gate depending on the layer before.
	// Final output is fixed, so the SAT instance consists of inverting the
	// computation all the way to the first layer.
	// TODO: somehow this seems to result in quite easy instances, even with
	// houndreds of layers. Am I missing something? I thought inverting random
	// functions should be hard.
	if (opt.seed.empty())
		opt.seed = fmt::format("{}", std::random_device()());

	util::xoshiro256 rng(opt.seed);
	std::uniform_int_distribution<uint32_t> litDist(0, opt.width - 1);
	std::bernoulli_distribution coin(0.5);

	int nvars = opt.width * opt.height;
	util::bit_vector solution(nvars);
	auto cnf = Cnf(nvars);
	for (int i = 0; i < opt.width; ++i)
		solution[i] = coin(rng);

	for (int k = 1; k < opt.height; ++k)
		for (int i = 0; i < opt.width; ++i)
		{
			int index = k * opt.width + i;
			Lit a = Lit(litDist(rng) + (k - 1) * opt.width, coin(rng));
			Lit b = Lit(litDist(rng) + (k - 1) * opt.width, coin(rng));
			Lit c = Lit(index, coin(rng));

			if (rng.uniform() <= opt.xor_ratio)
			{
				cnf.add_xor_clause_safe(c, a, b);
				solution[index] = (solution[a.var()] ^ a.sign()) ^
				                  (solution[b.var()] ^ b.sign()) ^ c.sign();
			}
			else
			{
				cnf.add_and_clause_safe(c, a, b);
				solution[index] = ((solution[a.var()] ^ a.sign()) &&
				                   (solution[b.var()] ^ b.sign())) ^
				                  c.sign();
			}
		}

	for (int i = 0; i < opt.width; ++i)
	{
		int index = (opt.height - 1) * opt.width + i;
		cnf.add_unary(Lit(index, true) ^ solution[index]);
	}

	fmt::print("{}", cnf);
}
} // namespace

void setup_gen_circuit_command(CLI::App &app)
{
	auto opt = std::make_shared<Options>();

	app.add_option("width", opt->width, "number of variables");
	app.add_option("height", opt->height, "group size (>= 2)");
	app.add_option("--xor-ratio", opt->xor_ratio,
	               "ratio of XOR gates ([0,1], default = 0.5)");
	app.add_option("--seed", opt->seed, "seed for random number generator");

	app.callback([opt]() { run_command(*opt); });
}
