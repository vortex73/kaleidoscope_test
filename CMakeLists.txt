cmake_minimum_required(VERSION 3.7)

project(Kaleidoscope VERSION 1.0 LANGUAGES C CXX)

execute_process(COMMAND llvm-config --cxxflags
                OUTPUT_VARIABLE LLVM_CXX_FLAGS
                OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND llvm-config --ldflags --system-libs --libs core orcjit native x86
                OUTPUT_VARIABLE LLVM_LD_FLAGS
                OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND llvm-config --libdir
                OUTPUT_VARIABLE LLVM_LIB_DIR
                OUTPUT_STRIP_TRAILING_WHITESPACE)
separate_arguments(LLVM_LD_FLAGS_LIST UNIX_COMMAND "${LLVM_LD_FLAGS}")
separate_arguments(LLVM_LIBS_LIST UNIX_COMMAND "${LLVM_LIBS}")

message(STATUS "LINKS : ${LLVM_LD_FLAGS_LIST}")
add_executable(toy frontend.cpp)
link_directories(${LLVM_LIB_DIR})
target_link_libraries(toy ${LLVM_LD_FLAGS_LIST})
target_link_libraries(toy ${LLVM_LIBS_LIST})
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3")

