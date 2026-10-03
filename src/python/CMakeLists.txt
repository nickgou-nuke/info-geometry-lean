cmake_minimum_required(VERSION 3.18)
project(cl55_cuda LANGUAGES CXX CUDA)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CUDA_STANDARD 14)

find_package(Python COMPONENTS Interpreter Development REQUIRED)
# We assume pybind11 is installed and available
find_package(pybind11 CONFIG REQUIRED)

pybind11_add_module(cl55_cuda cl55_cuda_binding.cpp ../cpp/Cl55TensorCore.cu)

target_compile_options(cl55_cuda PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:-arch=sm_80>)
