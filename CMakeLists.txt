cmake_minimum_required (VERSION 2.8.9)
project (dawn)
include_directories(src)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wno-unused-variable -Werror")

file(GLOB sources "src/*.cpp")
list(REMOVE_ITEM sources "${CMAKE_SOURCE_DIR}/src/main.cpp" "${CMAKE_SOURCE_DIR}/src/check.cpp")

add_executable(dawn src/main.cpp ${sources})
add_executable(check src/check.cpp ${sources})
