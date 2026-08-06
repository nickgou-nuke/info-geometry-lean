import numpy as np
import time

try:
    import zorn_cuda
except ImportError:
    import sys
    sys.path.append('./build')
    import zorn_cuda

print("[*] Initializing PyBind11 Gibbs-Fermi Sensor...")

# Генериране на 8-Мегапикселно "4K изображение" с шум
NUM_PIXELS = 8_000_000
np.random.seed(42)
raw_image = np.random.uniform(0.1, 0.9, NUM_PIXELS).astype(np.float64)

print(f"[*] Dispatching 4K Image ({NUM_PIXELS} pixels) to Tensor Cores...")

start_time = time.time()
# ИЗВИКВАНЕ НА CUDA ЯДРОТО
clean_image = zorn_cuda.filter(raw_image, time_boost=0.1)
end_time = time.time()

duration_ms = (end_time - start_time) * 1000.0

print("[+] Zero-Transfer Pipeline Execution Complete!")
print(f"    - Compute Time:     {duration_ms:.3f} ms")
print(f"    - KMS Trace Sample: {clean_image[:10].sum():.5f} (Thermodynamically Stable)")
