cmake_minimum_required(VERSION 3.16.0)
project(dawn LANGUAGES CXX)

include(cmake/CPM.cmake)

CPMAddPackage(
	NAME util
	GITHUB_REPOSITORY krox/util
	GIT_TAG 56bb6d87b7f67f7e47a859f1141d986065d4f39c
)

CPMAddPackage(
	NAME cli11
	GITHUB_REPOSITORY CLIUtils/CLI11
	GIT_TAG 291c58789c031208f08f4f261a858b5b7083e8e2 # v2.3.2
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

foreach(bin "dawn" "simplify" "gen" "gen_pigeonhole")
	add_executable(${bin} src/${bin}.cpp)
	target_link_libraries(${bin} PRIVATE sat CLI11::CLI11)
	target_compile_options(${bin} PRIVATE -O2 -Wall -Wextra -Werror -march=native)
endforeach(bin)

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
