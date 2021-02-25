cmake_minimum_required (VERSION 2.8.9)
project (dawn)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2 -Wall -Wextra -Werror -pedantic -g")

add_subdirectory(util)
add_subdirectory(fmt)
add_subdirectory(CLI11)

include_directories(src)
include_directories(util/src)
include_directories(fmt/include)
include_directories(CLI11/include)

file(GLOB files_cpp "src/sat/*.cpp")
add_library(sat STATIC ${files_cpp})
target_link_libraries(sat util fmt)

foreach(bin "dawn" "dawn_lookahead" "check" "simplify" "gen" "gen_pigeonhole")
	add_executable(${bin} src/${bin}.cpp)
	target_link_libraries(${bin} sat util fmt)
endforeach(bin)
