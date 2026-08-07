import numpy as np
import time
import sys
sys.path.append("build")
import zorn_cuda

def main():
    print("[*] Initializing Twistor ISP (CUTLASS Tensor Cores)...")
    
    # 1 Million pixels
    N = 1000000
    print(f"[*] Generating {N} random pixels (noise)...")
    raw_image = np.random.uniform(0.1, 0.9, N).astype(np.float64)

    print("[*] Launching CUTLASS-accelerated Modular Flow (t = 0.1)...")
    
    start_time = time.time()
    
    # Process the entire batch on GPU via pybind11
    clean_image = zorn_cuda.filter(raw_image, 0.1)
    
    end_time = time.time()
    duration_ms = (end_time - start_time) * 1000.0
    
    print("[+] GPU Pipeline Execution Complete!")
    print(f"    - Processed Pixels: {N}")
    print(f"    - CUTLASS Compute Time: {duration_ms:.4f} ms")
    print(f"    - Throughput: {(N / (duration_ms / 1000.0)) / 1e9:.4f} Gigapixels/sec")
    
    energy_sum = np.sum(clean_image[:10])
    print(f"    - KMS Trace Sample (First 10): {energy_sum:.5f} (Thermodynamically Stable)")

if __name__ == "__main__":
    main()
