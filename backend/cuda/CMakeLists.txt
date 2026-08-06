cmake_minimum_required(VERSION 3.18)
project(TwistorModularFlowCUDA LANGUAGES CXX CUDA)

# C++ Standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_POSITION_INDEPENDENT_CODE ON) # Required for shared library (.so)

# Create a Shared Library (.so) for Lean 4 FFI linking
add_library(twistor_engine SHARED twistor_modular_flow.cu)

# Target properties (CUDA architecture for Tensor Cores)
# Architectures: 75 (Turing), 80 (Ampere A100), 86 (Ampere RTX), 89 (Ada), 90 (Hopper)
set_target_properties(twistor_engine PROPERTIES CUDA_ARCHITECTURES "80;86;90")

# If you install CUTLASS later, add it to the include directories
# target_include_directories(twistor_engine PRIVATE ${CUTLASS_DIR}/include)
