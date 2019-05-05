cmake_minimum_required (VERSION 2.8.9)
project (dawn)
include_directories(src)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2 -Wall -Wextra -Werror -pedantic")

file(GLOB files_cpp "src/sat/*.cpp")

add_executable(dawn src/dawn.cpp ${files_cpp})
add_executable(check src/check.cpp ${files_cpp})
add_executable(gen src/gen.cpp ${files_cpp})
