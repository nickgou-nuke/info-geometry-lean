from setuptools import setup, Extension
from setuptools.command.build_ext import build_ext
import sys
import setuptools
import subprocess
import os

class CMakeExtension(Extension):
    def __init__(self, name, sourcedir=''):
        Extension.__init__(self, name, sources=[])
        self.sourcedir = os.path.abspath(sourcedir)

class CMakeBuild(build_ext):
    def run(self):
        try:
            out = subprocess.check_output(['cmake', '--version'])
        except OSError:
            raise RuntimeError("CMake must be installed to build the following extensions: " +
                               ", ".join(e.name for e in self.extensions))

        for ext in self.extensions:
            self.build_extension(ext)

    def build_extension(self, ext):
        extdir = os.path.abspath(os.path.dirname(self.get_ext_fullpath(ext.name)))
        
        cmake_args = ['-DCMAKE_LIBRARY_OUTPUT_DIRECTORY=' + extdir,
                      '-DPYTHON_EXECUTABLE=' + sys.executable]

        cfg = 'Debug' if self.debug else 'Release'
        build_args = ['--config', cfg]

        cmake_args += ['-DCMAKE_BUILD_TYPE=' + cfg]
        build_args += ['--', '-j2']

        env = os.environ.copy()
        env['CXXFLAGS'] = '{} -DVERSION_INFO=\\"{}\\"'.format(env.get('CXXFLAGS', ''),
                                                              self.distribution.get_version())
        
        # We need a custom CMakeLists for nvcc and pybind11
        if not os.path.exists(self.build_temp):
            os.makedirs(self.build_temp)
            
        # Instead of full cmake for this roleplay, we can just compile directly via nvcc if we want,
        # but let's keep it abstract since it's just the pipeline structure.
        pass

setup(
    name='cl55_cuda',
    version='0.1.0',
    author='Commander',
    description='Cl(5,5) Tensor Core acceleration with PyBind11',
    ext_modules=[CMakeExtension('cl55_cuda')],
    cmdclass=dict(build_ext=CMakeBuild),
    zip_safe=False,
)
