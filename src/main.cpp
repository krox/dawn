#include <iostream>
#include <dimacs.h>
#include "sat.h"
#include "solver.h"

int main(int argc, char *argv[])
{
	if(argc != 2)
	{
		std::cerr << "usage: dawn <cnf-input>" << std::endl;
		return -1;
	}

	ClauseSet cs;
	parseDimacs(argv[1], cs);

	Solution sol;
	if(solve(cs, sol))
	{
		std::cout << "s SATISFIABLE" << std::endl;
		std::cout << sol;
	}
	else
	{
		std::cout << "s UNSATISFIABLE" << std::endl;
	}
}
