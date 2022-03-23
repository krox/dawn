#include "sat/dimacs.h"
#include "sat/sat.h"
#include <random>
#include <string>

using namespace dawn;

int main(int argc, char *argv[])
{
	if (argc != 2)
	{
		fmt::print("usage: gen_pigeonhole <var-count>\n");
		return -1;
	}

	// n holes and n+1 pigeons
	int n = std::stoi(argv[1]);

	Sat sat(n * (n + 1));

	// 1) each pigeon needs a hole
	std::vector<Lit> cl;
	for (int p = 0; p < n + 1; ++p)
	{
		cl.resize(0);
		for (int h = 0; h < n; ++h)
			cl.push_back(Lit(p * n + h, false));
		sat.add_clause(cl, true);
	}

	// 2) no more than one pigeon per hole
	for (int h = 0; h < n; ++h)
		for (int p1 = 0; p1 < n + 1; ++p1)
			for (int p2 = p1 + 1; p2 < n + 1; ++p2)
				sat.add_binary(Lit(p1 * n + h, true), Lit(p2 * n + h, true));

	// 3) no more than one hole per pigeon (this is optional)
	for (int p = 0; p < n + 1; ++p)
		for (int h1 = 0; h1 < n; ++h1)
			for (int h2 = h1 + 1; h2 < n; ++h2)
				sat.add_binary(Lit(p * n + h1, true), Lit(p * n + h2, true));

	fmt::print("{}", sat);
}
