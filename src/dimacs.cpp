#include "dimacs.h"
#include <fstream>
#include <string>
#include <cstdio>
#include <memory>
#include <cstdio>
#include <cstring>
#include <cctype>
#include <climits>
#include <vector>
#include <iostream>

/**
 * Custom file buffer + parsing utilities.
 */
class Parser
{
	static constexpr size_t CHUNK = 256*1024;
	FILE* file;
	size_t pos = 0; // current position in buf
	std::unique_ptr<char[]> buf;

public:

	/** returns 0 at end of file */
	inline char operator*()
	{
		return buf[pos];
	}

	/** advances by one character */
	inline void operator++()
	{
		++pos;

		// chunk exhausted -> read new chunk
		if(pos >= CHUNK)
		{
			auto size = fread(buf.get(), 1, CHUNK, file);
			memset(buf.get()+size, 0, CHUNK-size);
			pos = 0;
		}
	}

	inline int parseInt()
	{
		int r = 0;
		int s = 1;
		if(**this == '-')
		{
			s = -1;
			++*this;
		}

		if(!isdigit(**this))
		{
			std::cerr << "PARSE ERROR: unexpected character" << std::endl;
			exit(-1);
		}

		while(isdigit(**this))
		{
			int d = **this - '0';
			++*this;
			if(r > (INT_MAX-d)/10)
			{
				std::cerr << "PARSE ERROR: integer overflow" << std::endl;
				exit(-1);
			}
			r = 10*r + d;
		}
		return r*s;
	}

	/** skip whitespace (including newlines) */
	inline void skipWhite()
	{
		while(isspace(**this))
			++*this;
	}

	/** advances the stream to the next line */
	inline void skipLine()
	{
		while(**this != 0 && **this != '\n')
			++*this;
		if(**this == '\n')
			++*this;
	}

	Parser(std::string filename)
	{
		file = fopen(filename.c_str(), "rb");
		if(file == nullptr)
		{
			std::cerr << "PARSE ERROR: unable to open file" << std::endl;
			exit(-1);
		}
		buf = std::make_unique<char[]>(CHUNK);
		pos = CHUNK;
		++*this;
	}

	~Parser()
	{
		if(file != NULL)
			fclose(file);
	}
};

void parseDimacs(std::string filename, ClauseStorage& clauses)
{
	auto parser = Parser(filename);

	std::vector<Lit> clause;
	while(true)
	{
		parser.skipWhite();

		// end of file
		if(*parser == 0)
			break;

		// comment lines
		else if(*parser == 'c')
		{
			parser.skipLine();
			continue;
		}

		// ignore the line 'p cnf <varCount> <clauseCount>'
		else if(*parser == 'p')
		{
			parser.skipLine();
			continue;
		}

		// integer
		else if(isdigit(*parser) || *parser == '-')
		{
			auto x = parser.parseInt();
			if(x == 0)
			{
				clauses.addClause(clause);
				clause.resize(0);
			}
			else
				clause.push_back(Lit::fromDimacs(x));
			continue;
		}

		else
		{
			std::cerr << "PARSE ERROR: unexpected character: '" << (int)*parser << "'" << std::endl;
			exit(-1);
		}
	}

	if(!clause.empty())
	{
		std::cerr << "PARSE ERROR: incomplete clause at end of file" << std::endl;
		exit(-1);
	}
}
