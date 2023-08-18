#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/dimacs.h"
#include "sat/logging.h"
#include "sat/sat.h"
#include "sat/solver.h"
#include <csignal>
#include <cstdio>
#include <random>
#include <unistd.h>

using namespace dawn;

extern "C" void interruptHandler(int)
{
	interrupt.store(true);
	signal(SIGINT, SIG_DFL); // remove the handler so that a second SIGINT will
	                         // abort the program
}

void setup_solve_command(CLI::App &app);
void setup_check_command(CLI::App &app);
void setup_gen_command(CLI::App &app);
void setup_stats_command(CLI::App &app);
void setup_ui_command(CLI::App &app);

int main(int argc, char *argv[])
{
	CLI::App app{"sat solver"};
	app.require_subcommand(1);

	auto cmd = app.add_subcommand("solve", "solve a CNF formula");
	setup_solve_command(*cmd);
	cmd = app.add_subcommand("check", "check a solution to a CNF formula");
	setup_check_command(*cmd);
	cmd = app.add_subcommand("gen", "generate a random CNF");
	setup_gen_command(*cmd);
	cmd = app.add_subcommand("stats", "print statistics about a CNF formula");
	setup_stats_command(*cmd);
	cmd = app.add_subcommand("ui", "start the UI for interactive solving");
	setup_ui_command(*cmd);

	try
	{
		app.parse(argc, argv);
	}
	catch (const CLI::ParseError &e)
	{
		return app.exit(e);
	}
	catch (const std::exception &e)
	{
		std::cerr << "Error: " << e.what() << std::endl;
		return -1;
	}
	catch (...)
	{
		fmt::print("Unknown error\n");
		return -1;
	}

	// NOTE: some commands (namely 'solve') might use std::exit() to return a
	// meaningful non-zero exit code
	return 0;
}
