cmake_minimum_required (VERSION 3.16.0)
project (dawn LANGUAGES CXX)

add_subdirectory(util EXCLUDE_FROM_ALL)

include(FetchContent)
FetchContent_Declare(
  cli11
  GIT_REPOSITORY https://github.com/CLIUtils/CLI11
  GIT_TAG        b9be5b9444772324459989177108a6a65b8b2769 # v2.2.0
)
FetchContent_Declare(
  Catch2
  GIT_REPOSITORY https://github.com/catchorg/Catch2.git
  GIT_TAG        v3.0.0-preview4
)
FetchContent_MakeAvailable(cli11)

file(GLOB files_cpp "src/sat/*.cpp")
add_library(sat STATIC ${files_cpp})

target_compile_features(sat PUBLIC cxx_std_17)
target_include_directories(sat PUBLIC src)
target_link_libraries(sat PUBLIC util)
target_compile_options(sat PRIVATE -O2 -Wall -Wextra -Werror)

foreach(bin "dawn" "simplify" "gen" "gen_pigeonhole")
	add_executable(${bin} src/${bin}.cpp)
	target_link_libraries(${bin} PRIVATE sat CLI11::CLI11)
	target_compile_options(${bin} PRIVATE -O2 -Wall -Wextra -Werror)
endforeach(bin)

# fuzz testing
add_custom_target(fuzz
	COMMAND ./fuzz.py
	WORKING_DIRECTORY ..
	DEPENDS fuzz.py dawn
)

# unittests
if(CMAKE_PROJECT_NAME STREQUAL PROJECT_NAME)
	FetchContent_MakeAvailable(Catch2)

	add_executable(tests tests/tests.cpp)
	target_compile_features(tests PRIVATE cxx_std_17)
	target_link_libraries(tests PRIVATE Catch2::Catch2WithMain sat)
	target_compile_options(tests PRIVATE -Wall -Wextra -Werror -g)
endif()
