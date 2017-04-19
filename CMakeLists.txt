cmake_minimum_required(VERSION 3.6)
project(SAT_solver)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -Wall -O3")

set(SOURCE_FILES SAT-alumnes.cpp)

set(CMAKE_VERBOSE_MAKEFILE ON)

add_executable(SAT_solver ${SOURCE_FILES})
