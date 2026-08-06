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
find_path(LEAN_INCLUDE_DIR lean/lean.h PATHS /usr/local/include/lean $ENV{HOME}/.elan/toolchains/leanprover--lean4---v4.0.0/include $ENV{HOME}/.elan/toolchains/leanprover--lean4---v4.28.1/include $ENV{HOME}/.elan/toolchains/leanprover--lean4---v4.11.0/include)
include_directories(${LEAN_INCLUDE_DIR})

# CUTLASS Headers
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/cutlass/include)
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/cutlass/tools/util/include)

# Fetch and configure PyBind11
include(FetchContent)
FetchContent_Declare(
  pybind11
  GIT_REPOSITORY https://github.com/pybind/pybind11.git
  GIT_TAG        v2.11.1
)
FetchContent_MakeAvailable(pybind11)

# Compile shared library for Lean FFI
add_library(zorn_cuda SHARED 
    GibbsFermiSensor.cu
    tensor_core_isp.cu
)
target_link_libraries(zorn_cuda PRIVATE cudart cublas)

# PyBind11 Extension Module
pybind11_add_module(zorn_cuda_py zorn_pybind.cpp)
target_link_libraries(zorn_cuda_py PRIVATE zorn_cuda)
set_target_properties(zorn_cuda_py PROPERTIES CUDA_ARCHITECTURES "80;90" OUTPUT_NAME "zorn_cuda")
