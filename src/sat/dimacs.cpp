#include "sat/dimacs.h"

#include "util/stopwatch.h"
#include <cctype>
#include <climits>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

static void panic(std::string msg)
{
	std::cout << "PARSE ERROR: " << msg << std::endl;
	exit(-1);
}

#define enforce(x, msg)                                                        \
	if (!(x))                                                                  \
		panic(msg);

/**
 * Custom file buffer + parsing utilities.
 */
class Parser
{
	static constexpr size_t CHUNK = 256 * 1024;
	FILE *file;
	bool needClose;
	size_t pos = 0; // current position in buf
	std::unique_ptr<char[]> buf;

  public:
	Parser(const Parser &) = delete;
	Parser &operator=(const Parser &) = delete;

	/** returns 0 at end of file */
	inline char operator*() { return buf[pos]; }

	/** advances by one character */
	inline void operator++()
	{
		++pos;

		// chunk exhausted -> read new chunk
		if (pos >= CHUNK)
		{
			auto size = fread(buf.get(), 1, CHUNK, file);
			memset(buf.get() + size, 0, CHUNK - size);
			pos = 0;
		}
	}

	inline int parseInt()
	{
		int r = 0;
		int s = 1;
		if (**this == '-')
		{
			s = -1;
			++*this;
		}

		enforce(isdigit(**this), "unexpected character");

		while (isdigit(**this))
		{
			int d = **this - '0';
			++*this;
			enforce(r <= (INT_MAX - d) / 10, "integer overflow");
			r = 10 * r + d;
		}
		return r * s;
	}

	std::string parseString()
	{
		std::string r;
		enforce(isalpha(**this), "unexpected character");
		while (isalpha(**this))
		{
			r += **this;
			++*this;
		}
		return r;
	}

	/** skip whitespace (including newlines) */
	inline void skipWhite()
	{
		while (isspace(**this))
			++*this;
	}

	/** advances the stream to the next line */
	inline void skipLine()
	{
		while (**this != 0 && **this != '\n')
			++*this;
		if (**this == '\n')
			++*this;
	}

	Parser(std::string filename)
	{
		if (filename.empty())
		{
			file = stdin;
			needClose = false;
		}
		else
		{
			file = fopen(filename.c_str(), "rb");
			enforce(file != nullptr, "unable to open file");
			needClose = true;
		}
		buf = std::make_unique<char[]>(CHUNK);
		pos = CHUNK;
		++*this;
	}

	~Parser()
	{
		if (needClose && file != NULL)
			fclose(file);
	}
};

void parseCnf(std::string filename, Sat &sat)
{
	StopwatchGuard(sat.stats.swParsing);
	Stopwatch sw;
	sw.start();

	if (filename != "")
		std::cout << "c reading " << filename << std::endl;
	else
		std::cout << "c reading from stdin" << std::endl;
	auto parser = Parser(filename);

	int varCount = -1;
	int64_t clauseCount = -1;
	int64_t clauseCounter = 0;
	std::vector<Lit> clause;
	while (true)
	{
		parser.skipWhite();

		// end of file
		if (*parser == 0)
			break;

		// comment lines
		else if (*parser == 'c')
		{
			parser.skipLine();
			continue;
		}

		// header in format 'p cnf <varCount> <clauseCount>'
		else if (*parser == 'p')
		{
			++parser;
			parser.skipWhite();
			enforce(parser.parseString() == "cnf", "invalid 'p' line");
			enforce(varCount == -1 && clauseCount == -1, "duplicate 'p' line");
			parser.skipWhite();
			varCount = parser.parseInt();
			parser.skipWhite();
			clauseCount = parser.parseInt();
			while (sat.varCount() < varCount)
				sat.addVarOuter();
			continue;
		}

		// integer
		else if (isdigit(*parser) || *parser == '-')
		{
			auto x = parser.parseInt();
			if (x == 0)
			{
				clauseCounter++;
				sat.addClauseOuter(clause);
				clause.resize(0);
			}
			else
			{
				auto lit = Lit::fromDimacs(x);
				while (sat.varCount() <= lit.var())
					sat.addVarOuter();
				clause.push_back(lit);
			}
			continue;
		}

		else
			panic(std::string("unexpected character '") + *parser + "'");
	}

	enforce(clause.empty(), "incomplete clause at end of file");
	enforce(varCount == -1 || varCount == sat.varCount(),
	        fmt::format(
	            "wrong number of variables: header said {}, actually got {}",
	            varCount, sat.varCount()));
	enforce(
	    clauseCount == -1 || clauseCount == clauseCounter,
	    fmt::format("wrong number of clauses: header said {}, actually got {}",
	                clauseCount, clauseCounter));

	fmt::print("c [parser       {:#6.2f}] read {} vars and {} clauses\n",
	           sw.secs(), sat.varCount(), sat.clauseCount());
}
void parseSolution(std::string filename, Solution &sol)
{
	auto parser = Parser(filename);

	while (true)
	{
		parser.skipWhite();

		// end of file
		if (*parser == 0)
			break;

		// comment lines
		else if (*parser == 'c')
		{
			parser.skipLine();
			continue;
		}

		// ignore the line 's SATISFIABLE'
		else if (*parser == 's')
		{
			parser.skipLine();
			continue;
		}

		// 'v' line
		else if (*parser == 'v')
		{
			++parser;
			while (true)
			{
				parser.skipWhite();
				int x = parser.parseInt();
				if (x == 0)
					break;
				auto lit = Lit::fromDimacs(x);
				enforce(lit.var() < sol.varCount(),
				        "invalid literal in solution");
				sol.set(lit);
			}
		}

		else
			panic(std::string("unexpected character: '") + *parser + "'");
	}

	enforce(sol.valid(), "invalid/incomplete solution");
}
