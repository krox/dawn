cmake_minimum_required(VERSION 3.16.0)
project(dawn LANGUAGES CXX)

include(cmake/CPM.cmake)

CPMAddPackage(
	NAME util
	GITHUB_REPOSITORY krox/util
	GIT_TAG dbc2b40084b8940dfeaa780375de818de5a8fbc0
)

CPMAddPackage(
	NAME cli11
	GITHUB_REPOSITORY CLIUtils/CLI11
	GIT_TAG 291c58789c031208f08f4f261a858b5b7083e8e2 # v2.3.2
)

CPMAddPackage(
	NAME ftxui
	GITHUB_REPOSITORY ArthurSonzogni/ftxui
	GIT_TAG 513ec6c5e1e71c8a1366e0db5a61400466697f73 # v4.1.1
)

CPMAddPackage(
	NAME Catch2
	GITHUB_REPOSITORY catchorg/Catch2
	GIT_TAG 2ab20a0e008845e02bd06248e61ca6e5ad1aba33 # v3.3.1
)

file(GLOB files_cpp "src/sat/*.cpp")
add_library(sat STATIC ${files_cpp})

target_compile_features(sat PUBLIC cxx_std_17)
target_include_directories(sat PUBLIC src)
target_link_libraries(sat PUBLIC util)
target_compile_options(sat PRIVATE -O2 -Wall -Wextra -Werror -march=native)

add_executable(dawn src/main.cpp src/commands/check.cpp src/commands/gen.cpp src/commands/solve.cpp src/commands/stats.cpp src/commands/ui.cpp)
target_link_libraries(dawn PRIVATE sat CLI11::CLI11 ftxui::screen ftxui::dom ftxui::component)
target_compile_options(dawn PRIVATE -O2 -Wall -Wextra -Werror -march=native)

# fuzz testing
add_custom_target(fuzz
	COMMAND ./fuzz.py
	WORKING_DIRECTORY ..
	DEPENDS fuzz.py dawn
)

# unittests
if(CMAKE_PROJECT_NAME STREQUAL PROJECT_NAME)
	CPMAddPackage(
		NAME Catch2
		GITHUB_REPOSITORY catchorg/Catch2
		GIT_TAG 2ab20a0e008845e02bd06248e61ca6e5ad1aba33 # v3.3.1
	)

	add_executable(tests tests/tests.cpp)
	target_compile_features(tests PRIVATE cxx_std_17)
	target_link_libraries(tests PRIVATE Catch2::Catch2WithMain sat)
	target_compile_options(tests PRIVATE -Wall -Wextra -Werror -g -march=native)
endif()
