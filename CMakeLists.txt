cmake_minimum_required (VERSION 2.8.9)
project (dawn)
include_directories(src)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2 -Wall -Wextra -Wno-unused-variable -Wno-unused-but-set-variable -Werror")

file(GLOB sources "src/*.cpp")
list(REMOVE_ITEM sources "${CMAKE_SOURCE_DIR}/src/main.cpp" "${CMAKE_SOURCE_DIR}/src/check.cpp" "${CMAKE_SOURCE_DIR}/src/gen.cpp")

add_executable(dawn src/main.cpp ${sources})
add_executable(check src/check.cpp ${sources})
add_executable(gen src/gen.cpp ${sources})
