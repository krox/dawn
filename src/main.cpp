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

	auto sol = solve(cs);
	if(sol.empty())
	{
		std::cout << "s UNSATISFIABLE" << std::endl;
	}
	else
	{
		std::cout << "s SATISFIABLE" << std::endl;
		std::cout << "v ";
		for(int i = 0; i < (int)cs.varCount(); ++i)
		{
			if(sol[Lit(i,false)])
				std::cout << Lit(i,false).toDimacs() << " ";
			if(sol[Lit(i,true)])
				std::cout << Lit(i,true).toDimacs() << " ";
		}
		std::cout << "0" << std::endl;
	}
}
