#include "CLI/CLI.hpp"

#include "sat/cnf.h"

#include "catch2/catch_session.hpp"

void setup_test_command(CLI::App &app)
{
	app.allow_extras();
	app.callback([&]() {
		std::vector<std::string> remaining = app.remaining();
		std::vector<char const *> args;
		args.push_back("dawn");
		for (std::string const &s : remaining)
			args.push_back(s.c_str());
		return Catch::Session().run(args.size(), args.data());
	});
}
