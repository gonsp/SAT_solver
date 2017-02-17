cmake_minimum_required(VERSION 3.6)
project(SAT_solver)

set(CMAKE_CXX_STANDARD 11)

set(SOURCE_FILES
        SAT-alumnes.cpp)

add_executable(SAT_solver ${SOURCE_FILES})