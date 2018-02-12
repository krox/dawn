#include <iostream>
#include <dimacs.h>
#include "clause.h"

int main(int argc, char *argv[])
{
	if(argc != 2)
	{
		std::cerr << "usage: dawn <cnf-input>" << std::endl;
		return -1;
	}

	ClauseStorage store;
	parseDimacs(argv[1], store);
	std::cout << store;
}
