cmake_minimum_required(VERSION 3.18)
project(ZornModularEngine LANGUAGES CXX CUDA)

# Require modern C++ and CUDA
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CUDA_STANDARD 17)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Optimizations for Tensor Cores (Ampere sm_80, Hopper sm_90)
set(CMAKE_CUDA_ARCHITECTURES 80 90)
set(CMAKE_CUDA_FLAGS "${CMAKE_CUDA_FLAGS} -O3 -use_fast_math")

# Lean FFI is currently disabled for PyBind11 standalone module

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

# PyBind11 Extension Module
pybind11_add_module(zorn_cuda zorn_pybind.cpp GibbsFermiSensor.cu)
target_link_libraries(zorn_cuda PRIVATE cudart)
set_target_properties(zorn_cuda PROPERTIES CUDA_ARCHITECTURES "80;90")
