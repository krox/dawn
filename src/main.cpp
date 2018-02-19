#include <iostream>
#include <dimacs.h>
#include "sat.h"
#include "solver.h"

struct Config
{
	std::string cnfFile;
	bool doProbing = false;

	Config(int argc, char *argv[])
	{
		std::vector<std::string> args;

		for(int i = 1; i < argc; ++i)
		{
			auto arg = std::string(argv[i]);
			if(arg == "--probing")
				doProbing = true;
			else args.push_back(arg);
		}

		if(args.size() != 1)
		{
			std::cerr << "usage: dawn [options] <cnf-input>" << std::endl;
			exit(-1);
		}

		cnfFile = args[0];
	}
};

int main(int argc, char *argv[])
{

	Config conf(argc, argv);

	ClauseSet cs;
	parseCnf(conf.cnfFile, cs);

	Solution sol;
	if(solveSimple(cs, sol, conf.doProbing))
	{
		std::cout << "s SATISFIABLE" << std::endl;
		std::cout << sol;
	}
	else
	{
		std::cout << "s UNSATISFIABLE" << std::endl;
	}
}
