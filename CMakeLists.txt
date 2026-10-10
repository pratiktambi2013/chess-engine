cmake_minimum_required(VERSION 3.16)
project(mitra_chess_engine VERSION 0.1.0 LANGUAGES CXX)

find_package(Threads REQUIRED)
include(CTest)

add_executable(mitra src/engine.cpp)
target_compile_features(mitra PRIVATE cxx_std_17)
target_link_libraries(mitra PRIVATE Threads::Threads)
if(MSVC)
    target_compile_options(mitra PRIVATE /W4)
else()
    target_compile_options(mitra PRIVATE -Wall -Wextra -Wpedantic)
endif()

if(BUILD_TESTING)
    add_test(NAME mitra-selftest COMMAND mitra --selftest)
endif()
