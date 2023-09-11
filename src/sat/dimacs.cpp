#include "sat/dimacs.h"

#include "sat/logging.h"
#include <cctype>
#include <climits>
#include <cstdio>
#include <cstring>
#include <memory>
#include <string>
#include <vector>

namespace dawn {

static void panic(std::string msg)
{
	fmt::print("PARSE ERROR: {}\n", msg);
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

std::pair<ClauseStorage, int> parseCnf(std::string filename)
{
	auto log = Logger("parser");
	if (filename != "")
		log.info("reading {}", filename);
	else
		log.info("reading from stdin");
	auto parser = Parser(filename);
	ClauseStorage clauses;

	int headerVarCount = -1;
	int headerClauseCount = -1;
	int varCount = 0;
	int clauseCount = 0;
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
			enforce(headerVarCount == -1 && headerClauseCount == -1,
			        "duplicate 'p' line");
			parser.skipWhite();
			headerVarCount = parser.parseInt();
			parser.skipWhite();
			headerClauseCount = parser.parseInt();
			continue;
		}

		// integer
		else if (isdigit(*parser) || *parser == '-')
		{
			auto x = parser.parseInt();
			if (x == 0)
			{
				clauseCount++;
				clauses.add_clause(clause, true);
				clause.resize(0);
			}
			else
			{
				auto lit = Lit::fromDimacs(x);
				varCount = std::max(varCount, lit.var() + 1);
				clause.push_back(lit);
			}
			continue;
		}

		else
			panic(std::string("unexpected character '") + *parser + "'");
	}

	enforce(clause.empty(), "incomplete clause at end of file");

	// there might be unused variables. In that case, respect the header
	if (headerVarCount > varCount)
		varCount = headerVarCount;

	enforce(headerVarCount == -1 || headerVarCount == varCount,
	        fmt::format(
	            "wrong number of variables: header said {}, actually got {}",
	            headerVarCount, varCount));
	enforce(
	    headerClauseCount == -1 || headerClauseCount == clauseCount,
	    fmt::format("wrong number of clauses: header said {}, actually got {}",
	                headerClauseCount, clauseCount));

	log.info("read {} vars and {} clauses", varCount, clauseCount);

	return {std::move(clauses), varCount};
}
void parseAssignment(std::string filename, Assignment &sol)
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
				enforce(lit.var() < sol.var_count(),
				        "invalid literal in solution");
				sol.set(lit);
			}
		}

		else
			panic(std::string("unexpected character: '") + *parser + "'");
	}

	enforce(sol.complete(), "incomplete solution");
}

} // namespace dawn
