import numpy as np
from PIL import Image
import time
import os

try:
    import ctypes
    ctypes.CDLL("/home/goutev/.elan/toolchains/leanprover--lean4---v4.28.1/lib/lean/libleanshared.so", mode=ctypes.RTLD_GLOBAL)
    import zorn_cuda
except ImportError:
    import sys
    sys.path.append('./build')
    import ctypes
    ctypes.CDLL("/home/goutev/.elan/toolchains/leanprover--lean4---v4.28.1/lib/lean/libleanshared.so", mode=ctypes.RTLD_GLOBAL)
    import zorn_cuda

print("========================================")
print("   ZORN TWISTOR ISP: FIRST LIGHT 🌌   ")
print("========================================")

IMAGE_PATH = "/home/goutev/.gemini/antigravity-cli/brain/aa42b119-17fb-4ee5-934e-43c8fadac04f/galaxy_1786042692449.jpg"
ARTIFACT_DIR = "/home/goutev/.gemini/antigravity-cli/brain/aa42b119-17fb-4ee5-934e-43c8fadac04f"

print("[1] Opening Eye (Loading Image)...")
try:
    img = Image.open(IMAGE_PATH).convert('L') # Convert to grayscale for thermodynamic analysis
except Exception as e:
    print(f"Error loading image: {e}")
    sys.exit(1)

# Преобразуваме в нормализиран numpy масив (0.0 до 1.0)
clean_pixels = np.array(img, dtype=np.float64) / 255.0

print("[2] Injecting Quantum Noise (Simulating Sensor)...")
# Инжектираме Поасонов / Гаусов шум, за да симулираме слаба осветеност
np.random.seed(42)
noise = np.random.normal(0, 0.3, clean_pixels.shape)
noisy_pixels = clean_pixels + noise
noisy_pixels = np.clip(noisy_pixels, 0.001, 0.999) # Защитаваме логаритмичния домейн

print(f"[*] Dispatching Image {noisy_pixels.shape} to Tensor Cores...")

# Измерваме времето за целия CUDA Pipeline
start_time = time.time()
filtered_pixels = zorn_cuda.filter(noisy_pixels, time_boost=0.1)
end_time = time.time()

duration_ms = (end_time - start_time) * 1000.0
print(f"[+] Zero-Transfer Pipeline Execution Complete in {duration_ms:.3f} ms!")

# Запазваме резултатите, за да ги видим!
print("[3] Projecting filtered twistors back to classical reality...")

noisy_img_out = Image.fromarray((noisy_pixels * 255).astype(np.uint8))
filtered_img_out = Image.fromarray((filtered_pixels * 255).astype(np.uint8))

noisy_img_out.save(os.path.join(ARTIFACT_DIR, "noisy_galaxy.jpg"))
filtered_img_out.save(os.path.join(ARTIFACT_DIR, "filtered_galaxy.jpg"))

print("[+] All done! First Light achieved.")
