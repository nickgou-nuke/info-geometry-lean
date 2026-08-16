from setuptools import setup, Extension
from setuptools.command.build_ext import build_ext
import os

try:
    import pybind11
    HAS_PYBIND11 = True
except ImportError:
    HAS_PYBIND11 = False
    pybind11 = None

class CMakeBuild(build_ext):
    def run(self):
        # We can implement a custom build step here to call nvcc,
        # but for simplicity we will just compile the C++ file and link to the 
        # CUDA object file assuming it was precompiled.
        pass

ext_modules = []
if HAS_PYBIND11 and os.environ.get("BUILD_CL55_CUDA"):
    ext_modules = [
        Extension(
            'cl55_cuda',
            ['src/cpp/cl55_python_bridge.cpp'],
            include_dirs=[
                pybind11.get_include(),
                '/usr/local/cuda/include'
            ],
            extra_compile_args=['-std=c++14', '-O3'],
            extra_objects=['src/cpp/Cl55TensorCore.o'],  # Precompiled by nvcc
            extra_link_args=['-lcudart', '-L/usr/local/cuda/lib64']
        ),
    ]

setup(
    name='infogeometry',
    version='0.1.0',
    description='Python Package for InfoGeometry Framework',
    ext_modules=ext_modules if ext_modules else None,
    zip_safe=False,
)
