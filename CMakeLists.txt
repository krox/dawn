cmake_minimum_required(VERSION 3.16.0)
project(dawn LANGUAGES CXX)

include(cmake/CPM.cmake)

CPMAddPackage(
	NAME util
	GITHUB_REPOSITORY krox/util
	GIT_TAG 34bb74615ca7e77d8f32c66e17a4eb74fa4c0154
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

file(GLOB files_cpp "src/sat/*.cpp")
add_library(sat STATIC ${files_cpp})

target_compile_features(sat PUBLIC cxx_std_17)
target_include_directories(sat PUBLIC src)
target_link_libraries(sat PUBLIC util)
target_compile_options(sat PRIVATE -O2 -Wall -Wextra -Werror -march=native)

add_executable(dawn src/main.cpp src/commands/check.cpp src/commands/gen.cpp src/commands/solve.cpp src/commands/sha256.cpp src/commands/stats.cpp src/commands/ui.cpp)
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
