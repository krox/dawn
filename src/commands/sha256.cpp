#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/dimacs.h"
#include "sat/register.h"
#include "sat/sat.h"
#include "sat/solver.h"
using namespace dawn;

namespace {
Register<32> ep0(Register<32> x)
{
	return make_xor(rotr(x, 2), rotr(x, 13), rotr(x, 22));
}
Register<32> ep1(Register<32> x)
{
	return make_xor(rotr(x, 6), rotr(x, 11), rotr(x, 25));
}
Register<32> sig0(Register<32> x)
{
	return make_xor(rotr(x, 7), rotr(x, 18), (x >> 3));
}
Register<32> sig1(Register<32> x)
{
	return make_xor(rotr(x, 17), rotr(x, 19), (x >> 10));
}

uint32_t byteswap(uint32_t x)
{
	return (x >> 24) | ((x >> 8) & 0xff00) | ((x << 8) & 0xff0000) | (x << 24);
}
Register<32> byteswap(Register<32> x)
{
	for (int i = 0; i < 8; ++i)
	{
		std::swap(x.lits_[i], x.lits_[i + 24]);
		std::swap(x.lits_[i + 8], x.lits_[i + 16]);
	}
	return x;
}

uint32_t sha256_k[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};

void sha256_transform(std::span<Register<32>> state,
                      std::span<Register<32>> data, int rounds)
{
	assert(state.size() == 8);
	assert(data.size() == 16);
	std::vector<Register<32>> m;
	m.reserve(64);

	for (size_t i = 0; i < 16; ++i)
		m.push_back(byteswap(data[i]));
	for (size_t i = 16; i < 64; ++i)
		m.push_back(sig1(m[i - 2]) + m[i - 7] + sig0(m[i - 15]) + m[i - 16]);

	Register<32> a = state[0];
	Register<32> b = state[1];
	Register<32> c = state[2];
	Register<32> d = state[3];
	Register<32> e = state[4];
	Register<32> f = state[5];
	Register<32> g = state[6];
	Register<32> h = state[7];

	assert(rounds <= 64);
	for (size_t i = 0; i < (size_t)rounds; ++i)
	{
		Register<32> t1 = h + ep1(e) + choose(e, f, g) + sha256_k[i] + m[i];
		Register<32> t2 = ep0(a) + maj(a, b, c);
		h = g;
		g = f;
		f = e;
		e = d + t1;
		d = c;
		c = b;
		b = a;
		a = t1 + t2;
	}

	state[0] += a;
	state[1] += b;
	state[2] += c;
	state[3] += d;
	state[4] += e;
	state[5] += f;
	state[6] += g;
	state[7] += h;
}

[[maybe_unused]] std::vector<Register<32>> sha256(std::span<Register<32>> data,
                                                  int rounds) noexcept
{
	auto &sat = data[0].sat_;
	std::vector<Register<32>> state;
	state.reserve(8);
	state.push_back(Register<32>(sat, 0x6a09e667));
	state.push_back(Register<32>(sat, 0xbb67ae85));
	state.push_back(Register<32>(sat, 0x3c6ef372));
	state.push_back(Register<32>(sat, 0xa54ff53a));
	state.push_back(Register<32>(sat, 0x510e527f));
	state.push_back(Register<32>(sat, 0x9b05688c));
	state.push_back(Register<32>(sat, 0x1f83d9ab));
	state.push_back(Register<32>(sat, 0x5be0cd19));

	auto buf = data.data();

	size_t blocks = data.size() / (16);
	size_t tail = data.size() % (16);

	// process whole blocks
	for (size_t i = 0; i < blocks; ++i)
	{
		sha256_transform(state, *(std::array<Register<32>, 16> *)buf, rounds);
		buf += 16;
	}

	auto tmp = std::vector<Register<32>>(16, Register<32>(sat, 0));
	for (size_t i = 0; i < tail; ++i)
		tmp[i] = buf[i];

	// NOTE: the trailing 0x80 always fits in the last (incomplete) block,
	//       but the trailing size might not
	tmp[tail] = Register<32>(sat, 0x80); // this always fits in last block

	if (tail >= 14)
	{
		sha256_transform(state, tmp, rounds);
		for (int i = 0; i < 16; ++i)
			tmp[i] = Register<32>(sat, 0);
	}

	// append size (in bits!)
	size_t bitlen = 32 * data.size();
	tmp[15] = Register<32>(sat, byteswap(uint32_t(bitlen)));
	tmp[14] = Register<32>(sat, byteswap(uint32_t(bitlen >> 32)));
	sha256_transform(state, tmp, rounds);

	for (size_t i = 0; i < 8; ++i)
		state[i] = byteswap(state[i]);

	return state;
}

struct Options
{
	std::string cnf_filename;
	int input_zero_bits = 0;
	int input_bits = 256;
	int rounds = 64;
	int zero_bits = 256;
	bool solve = false;
};

[[maybe_unused]] uint32_t choose(uint32_t a, uint32_t b, uint32_t c)
{
	return (a & b) ^ ((~a) & c);
}

[[maybe_unused]] uint32_t maj(uint32_t a, uint32_t b, uint32_t c)
{
	return (a & b) ^ (a & c) ^ (b & c);
}

void run_sha256_command(const Options &opt)
{
	Sat sat;

	assert(opt.input_bits % 32 == 0);
	std::vector<Register<32>> data;
	data.reserve(opt.input_bits / 32);
	for (int i = 0; i < opt.input_bits / 32; ++i)
		data.push_back(Register<32>::unknown(sat));
	auto hash = sha256(data, opt.rounds);
	auto zero = Register<32>(sat, 0);
	assert(opt.zero_bits % 32 == 0);
	for (int i = 0; i < opt.zero_bits / 32; ++i)
		equal(hash[i], zero);
	assert(opt.input_zero_bits % 32 == 0);
	for (int i = 0; i < opt.input_zero_bits / 32; ++i)
		equal(data[i], zero);

	if (opt.solve)
	{
		fmt::print("{}\n", sat.var_count());
		Assignment sol;
		int r = solve(sat, sol, {});
		assert(r == 10);
		uint32_t v = 0;
		for (int i = 0; i < 32; ++i)
			if (sol.satisfied(hash[0].lits_[i]))
				v |= 1 << i;
		v = byteswap(v);
		fmt::print("hash = {:08x}\n", v);
	}
	else
	{
		fmt::print("{}", sat);
	}
}

} // namespace

void setup_sha256_command(CLI::App &app)
{
	auto opt = std::make_shared<Options>();

	// input/output
	app.add_option("output", opt->cnf_filename, "output CNF in dimacs format")
	    ->type_name("<filename>");
	app.add_option("--input-bits", opt->input_bits,
	               "number of input bits (default: 256)");
	app.add_option("--zero-bits", opt->zero_bits,
	               "number of zero bits (default: 256)");
	app.add_option(
	    "--input-zero-bits", opt->input_zero_bits,
	    "number of zero bits at the beginning of the input (default: 0)");
	app.add_option("--rounds", opt->rounds, "number of rounds (default: 64)");
	app.add_flag("--solve", opt->solve,
	             "solve the generated CNF (for testing trivial cases)");
	app.callback([opt]() { run_sha256_command(*opt); });
}
