cmake_minimum_required(VERSION 3.16.0)
project(dawn LANGUAGES CXX C)

include(cmake/CPM.cmake)

CPMAddPackage(
	NAME util
	GITHUB_REPOSITORY krox/util
	GIT_TAG 5476e838d5e88fd813bd68c33f87d7868cd91bde
)

CPMAddPackage(
	NAME cli11
	GITHUB_REPOSITORY CLIUtils/CLI11
	GIT_TAG f4d0731cebb123ff0ace712c099dffbcd2c58e5a # v2.4.1
)

CPMAddPackage(
	NAME ftxui
	GITHUB_REPOSITORY ArthurSonzogni/ftxui
	GIT_TAG cdf28903a7781f97ba94d30b79c3a4b0c97ccce7 # v5.0.0
)

CPMAddPackage(
	NAME Catch2
	GITHUB_REPOSITORY catchorg/Catch2
	GIT_TAG 2ab20a0e008845e02bd06248e61ca6e5ad1aba33 # v3.3.1
)

set(files_cpp
	src/commands/check.cpp
	src/commands/gen.cpp
	src/commands/sha256.cpp
	src/commands/solve.cpp
	src/commands/stats.cpp
	src/commands/test.cpp
	src/commands/ui.cpp
	tests/tests.cpp
	src/sat/assignment.cpp
	src/sat/binary.cpp
	src/sat/clause.cpp
	src/sat/cnf.cpp
	src/sat/dimacs.cpp
	src/sat/disjunction.cpp
	src/sat/elimination.cpp
	src/sat/probing.cpp
	src/sat/propengine.cpp
	src/sat/sat.cpp
	src/sat/searcher.cpp
	src/sat/solver.cpp
	src/sat/stats.cpp
	src/sat/subsumption.cpp
	src/sat/vivification.cpp
	src/main.cpp
)

add_executable(dawn ${files_cpp})
target_include_directories(dawn PUBLIC src)
target_compile_features(dawn PUBLIC cxx_std_20)
target_link_libraries(dawn PUBLIC util CLI11::CLI11 ftxui::screen ftxui::dom ftxui::component Catch2::Catch2)
target_compile_options(dawn PUBLIC -O3 -Wall -Wextra -Werror -march=native)
