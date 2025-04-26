#include "CLI/CLI.hpp"
#include "fmt/format.h"
#include "sat/dimacs.h"
#include "sat/sat.h"
#include "sat/solver.h"
#include "util/gnuplot.h"
#include "util/logging.h"
#include <csignal>
#include <cstdio>
#include <random>
#include <ranges>
#include <unistd.h>
#include <vector>

using namespace dawn;

void setup_solve_command(CLI::App &app);
void setup_check_command(CLI::App &app);
void setup_gen_command(CLI::App &app);
void setup_gen_hard_command(CLI::App &app);
void setup_gen_circuit_command(CLI::App &app);
void setup_sha256_command(CLI::App &app);
void setup_stats_command(CLI::App &app);
void setup_ui_command(CLI::App &app);
void setup_test_command(CLI::App &app);

int main(int argc, char *argv[])
{
	CLI::App app{"sat solver"};
	app.require_subcommand(1);

	auto cmd = app.add_subcommand("solve", "solve a CNF formula");
	setup_solve_command(*cmd);
	cmd = app.add_subcommand("check", "check a solution to a CNF formula");
	setup_check_command(*cmd);
	cmd = app.add_subcommand("gen", "generate a CNF instance");
	cmd->require_subcommand(1);
	auto cmd_gen = cmd->add_subcommand(
	    "3sat", "generate a random, satisfiable 3-SAT instance");
	setup_gen_command(*cmd_gen);
	auto cmd_sha256 = cmd->add_subcommand(
	    "sha256", "generate instance of pre-image attack on SHA-256 hash");
	setup_sha256_command(*cmd_sha256);
	auto cmd_hard = cmd->add_subcommand(
	    "hard", "generate small but hard, satisfiable SAT instance, inspired "
	            "by (but less sophisticated than) the 'sgen' generator(s) by "
	            "Ivor Spence");
	setup_gen_hard_command(*cmd_hard);
	auto cmd_circuit =
	    cmd->add_subcommand("circuit", "generate a CNF instance from a random, "
	                                   "layered circuit with fixed output");
	setup_gen_circuit_command(*cmd_circuit);
	cmd = app.add_subcommand("stats", "print statistics about a CNF formula");
	setup_stats_command(*cmd);
	cmd = app.add_subcommand("ui", "start the UI for interactive solving");
	setup_ui_command(*cmd);
	cmd = app.add_subcommand("test", "run tests");
	setup_test_command(*cmd);

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
