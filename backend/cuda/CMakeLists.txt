cmake_minimum_required(VERSION 3.18)
project(ZornModularEngine LANGUAGES CXX CUDA)

# Изискваме модерен C++ и CUDA
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CUDA_STANDARD 17)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Оптимизации за Tensor Cores (Ampere sm_80, Hopper sm_90)
set(CMAKE_CUDA_ARCHITECTURES 80 90)
set(CMAKE_CUDA_FLAGS "${CMAKE_CUDA_FLAGS} -O3 -use_fast_math --ptxas-options=-v")

# Трябва да посочим пътя до Lean 4 хедърите (lean.h)
find_path(LEAN_INCLUDE_DIR lean/lean.h PATHS /usr/local/include/lean $ENV{HOME}/.elan/toolchains/leanprover--lean4---v4.28.1/include)
include_directories(${LEAN_INCLUDE_DIR})

# Компилираме споделената библиотека за Lean FFI
add_library(zorn_cuda SHARED 
    ModularFlow.cu
)

target_link_libraries(zorn_cuda PRIVATE cudart)
