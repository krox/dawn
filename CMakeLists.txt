cmake_minimum_required (VERSION 2.8.9)
project (dawn)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2 -Wall -Wextra -Werror -pedantic")

add_subdirectory(util)
add_subdirectory(fmt)
add_subdirectory(CLI11)

include_directories(src)
include_directories(util/src)
include_directories(fmt/include)
include_directories(CLI11/include)

file(GLOB files_cpp "src/sat/*.cpp")

add_executable(dawn src/dawn.cpp ${files_cpp})
add_executable(check src/check.cpp ${files_cpp})
add_executable(gen src/gen.cpp ${files_cpp})
add_executable(gen_pigeonhole src/gen_pigeonhole.cpp ${files_cpp})
target_link_libraries(dawn util fmt)
target_link_libraries(check util fmt)
target_link_libraries(gen util fmt)
target_link_libraries(gen_pigeonhole util fmt)
