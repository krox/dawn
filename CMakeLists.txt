cmake_minimum_required (VERSION 3.16.0)
project (dawn LANGUAGES CXX)

add_subdirectory(util EXCLUDE_FROM_ALL)
add_subdirectory(CLI11 EXCLUDE_FROM_ALL)

file(GLOB files_cpp "src/sat/*.cpp")
add_library(sat STATIC ${files_cpp})

target_compile_features(sat PUBLIC cxx_std_17)
target_include_directories(sat PUBLIC src)
target_link_libraries(sat PUBLIC util)
target_compile_options(sat PRIVATE -O2 -Wall -Wextra -Werror -pedantic -Wnoexcept)

foreach(bin "dawn" "dawn_lookahead" "check" "simplify" "gen" "gen_pigeonhole")
	add_executable(${bin} src/${bin}.cpp)
	target_link_libraries(${bin} sat CLI11::CLI11)
	target_compile_options(${bin} PRIVATE -O2 -Wall -Wextra -Werror -pedantic -Wnoexcept)
endforeach(bin)
