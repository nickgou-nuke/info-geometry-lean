cmake_minimum_required(VERSION 3.18)
project(TwistorModularFlow LANGUAGES CXX CUDA)

# C++ Standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find Eigen3
# Depending on your system, you might need to specify Eigen3_DIR
find_package(Eigen3 REQUIRED NO_MODULE)

# Executable
add_executable(twistor_engine twistor_modular_flow.cu)

# Target properties (CUDA architecture)
set_target_properties(twistor_engine PROPERTIES CUDA_ARCHITECTURES "75;80;86")

# Include directories
target_include_directories(twistor_engine PRIVATE ${EIGEN3_INCLUDE_DIR})

# Link libraries (cuBLAS, thrust, etc. are usually linked automatically by nvcc, but let's be explicit if needed)
# target_link_libraries(twistor_engine PRIVATE ...)
