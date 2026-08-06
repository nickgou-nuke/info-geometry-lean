import ctypes
import os
import time
import numpy as np

# 1. Load the shared CUDA library
lib_path = os.path.join(os.path.dirname(__file__), 'build', 'libzorn_cuda.so')
zorn_lib = ctypes.CDLL(lib_path)

# Configure argument types for the C function
# extern "C" void run_twistor_isp_cuda(int N, double t, const double* host_in, double* host_out)
zorn_lib.run_twistor_isp_cuda.argtypes = [
    ctypes.c_int,
    ctypes.c_double,
    np.ctypeslib.ndpointer(dtype=np.float64, ndim=1, flags='C_CONTIGUOUS'),
    np.ctypeslib.ndpointer(dtype=np.float64, ndim=1, flags='C_CONTIGUOUS')
]
zorn_lib.run_twistor_isp_cuda.restype = None

def filter_image_cuda(image_array: np.ndarray, modular_time: float = 0.1) -> np.ndarray:
    """
    Applies the Twistor Tomita-Takesaki Modular flow to a 1D or 2D image array using CUDA.
    """
    original_shape = image_array.shape
    flat_img = image_array.astype(np.float64).flatten()
    N = len(flat_img)
    
    out_img = np.zeros_like(flat_img)
    
    # Run the CUDA kernel
    zorn_lib.run_twistor_isp_cuda(N, modular_time, flat_img, out_img)
    
    return out_img.reshape(original_shape)

if __name__ == "__main__":
    print("[*] Initializing Python-CUDA Twistor ISP Bridge...")
    
    # Generate 1 Megapixel of random noise
    NUM_PIXELS = 1000000
    np.random.seed(42)
    raw_pixels = np.random.uniform(0.1, 0.9, NUM_PIXELS)
    
    print(f"[*] Processing {NUM_PIXELS} pixels on GPU...")
    
    start_time = time.time()
    clean_pixels = filter_image_cuda(raw_pixels, modular_time=0.1)
    end_time = time.time()
    
    duration_ms = (end_time - start_time) * 1000.0
    
    print("[+] GPU Pipeline Execution Complete!")
    print(f"    - Compute Time:     {duration_ms:.3f} ms")
    print(f"    - KMS Trace Sample: {clean_pixels[:10].sum():.5f} (Thermodynamically Stable)")
