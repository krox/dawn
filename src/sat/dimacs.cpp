#include "sat/dimacs.h"

#include "util/io.h"
#include "util/logging.h"
#include <cctype>
#include <climits>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

namespace dawn {

// Custom text parser
class Parser
{
	std::string content;
	size_t pos = 0;

  public:
	Parser(const Parser &) = delete;
	Parser &operator=(const Parser &) = delete;

	inline char operator*() { return pos < content.size() ? content[pos] : 0; }

	inline void operator++() { ++pos; }

	inline int parseInt()
	{
		int r = 0;
		int s = 1;
		if (**this == '-')
		{
			s = -1;
			++*this;
		}

		if (!isdigit(**this))
			throw std::runtime_error("unexpected character (not a digit)");

		while (isdigit(**this))
		{
			int d = **this - '0';
			++*this;
			if (r > (INT_MAX - d) / 10)
				throw std::runtime_error("integer overflow while parsing CNF");
			r = 10 * r + d;
		}
		return r * s;
	}

	std::string parseString()
	{
		std::string r;
		if (!isalpha(**this))
			throw std::runtime_error("unexpected character (not an alphabet)");
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
		auto log = util::Logger("reader");
		if (!filename.empty())
		{
			// TODO: this is weirdly slow. investigate.
			// 		cat foo.cnf | ./dawn stats
			// is faster than
			// 	   ./dawn stats foo.cnf
			// even stranger, not the reading itself is slower, but the parsing
			// afterwards. Must be a difference in cache state? weird...
			content = util::read_file(filename);
			log.info("read {:.2f} MiB from '{}'", content.size() / 1024. / 1024,
			         filename);
		}
		else
		{
			std::istreambuf_iterator<char> begin(std::cin), end;
			content = std::string(begin, end);
			log.info("read {:.2f} MiB from stdin",
			         content.size() / 1024. / 1024);
		}
	}
};
std::pair<ClauseStorage, int> parseCnf(std::string filename)
{
	auto parser = Parser(filename);
	auto log = util::Logger("parser");
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
			if (parser.parseString() != "cnf")
				throw std::runtime_error("invalid 'p' line");
			if (headerVarCount != -1 || headerClauseCount != -1)
				throw std::runtime_error("duplicate 'p' line");
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
				clauses.add_clause(clause, Color::blue);
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
			throw std::runtime_error(std::string("unexpected character: '") +
			                         *parser + "'");
	}

	if (!clause.empty())
		throw std::runtime_error("incomplete clause at end of file");

	// there might be unused variables. In that case, respect the header
	if (headerVarCount > varCount)
		varCount = headerVarCount;

	if (headerVarCount != -1 && headerVarCount != varCount)
		throw std::runtime_error(
		    fmt::format("wrong number of variables: header said {}, "
		                "actually got {}",
		                headerVarCount, varCount));
	if (headerClauseCount != -1 && headerClauseCount != clauseCount)
		throw std::runtime_error(
		    fmt::format("wrong number of clauses: header said {}, "
		                "actually got {}",
		                headerClauseCount, clauseCount));

	log.info("parsed {} vars and {} clauses", varCount, clauseCount);

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
				if (lit.var() >= sol.var_count())
					throw std::runtime_error("invalid literal in solution");
				sol.set(lit);
			}
		}

		else
			throw std::runtime_error(std::string("unexpected character: '") +
			                         *parser + "'");
	}

	if (!sol.complete())
		throw std::runtime_error("incomplete solution");
}

} // namespace dawn
