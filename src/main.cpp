#include <iostream>
#include <dimacs.h>
#include "sat.h"

int main(int argc, char *argv[])
{
	if(argc != 2)
	{
		std::cerr << "usage: dawn <cnf-input>" << std::endl;
		return -1;
	}

	ClauseSet cs;
	parseDimacs(argv[1], cs);
	std::cout << cs;
}
