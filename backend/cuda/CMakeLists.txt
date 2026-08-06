cmake_minimum_required(VERSION 3.18)
project(ZornModularEngine LANGUAGES CXX CUDA)

# Require modern C++ and CUDA
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CUDA_STANDARD 17)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Optimizations for Tensor Cores (Ampere sm_80, Hopper sm_90)
set(CMAKE_CUDA_ARCHITECTURES 80 90)
set(CMAKE_CUDA_FLAGS "${CMAKE_CUDA_FLAGS} -O3 -use_fast_math")

# Find Lean 4 headers
find_path(LEAN_INCLUDE_DIR lean/lean.h PATHS /usr/local/include/lean $ENV{HOME}/.elan/toolchains/leanprover--lean4---v4.0.0/include $ENV{HOME}/.elan/toolchains/leanprover--lean4---v4.2.0/include $ENV{HOME}/.elan/toolchains/leanprover--lean4---v4.11.0/include)
include_directories(${LEAN_INCLUDE_DIR})

# Compile shared library for Lean FFI
add_library(zorn_cuda SHARED 
    src/ModularFlow.cu
)

target_link_libraries(zorn_cuda PRIVATE cudart)

# CPU Standalone Executable (Gibbs-Fermi CMOS Pipeline Prototype)
find_package(Eigen3 REQUIRED NO_MODULE)
add_executable(twistor_isp twistor_isp_main.cpp)
target_include_directories(twistor_isp PRIVATE ${EIGEN3_INCLUDE_DIR})
target_compile_options(twistor_isp PRIVATE -fopenmp)
target_link_options(twistor_isp PRIVATE -fopenmp)
