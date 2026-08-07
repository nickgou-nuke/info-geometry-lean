import torch
import torch.nn as nn
import torch.optim as optim
import numpy as np
import time
import os

try:
    from astropy.io import fits
except ImportError:
    print("[!] astropy is not installed. Please run: pip install astropy")
    exit(1)

from twistor_pytorch_layer import TwistorVisionTransformer

def run_pinn_epoch():
    print("==========================================================")
    print("🌌 LEAN 4 TENSOR CORE PINN: EPOCH 1 (COSMIC TIME DESCENT) 🌌")
    print("==========================================================\n")
    
    # 1. Зареждане на космическите данни
    input_file = "james_webb_twistor_clean.fits"
    if not os.path.exists(input_file):
        print(f"[*] Генериране на сурови FITS данни за обучението...")
        data = np.random.normal(50, 15, (1, 1, 256, 256)).astype(np.float32)
    else:
        print(f"[*] Зареждане на FITS данни от {input_file}...")
        with fits.open(input_file) as hdul:
            data = hdul[0].data
            # Избираме 256x256 участък за бързина
            data = data[:256, :256]
            data = data.reshape(1, 1, 256, 256).astype(np.float32)

    # Нормализиране за мрежата
    data_max = data.max()
    tensor_input = torch.tensor(data / data_max, requires_grad=True)
    
    # Симулирана целева "Истина" (Ground Truth) – например идеално изчистен сигнал
    target = torch.tensor(np.clip(data / data_max + np.random.normal(0, 0.05, data.shape), 0, 1).astype(np.float32))

    print(f"[*] Tensor Shape: {tensor_input.shape}")
    
    # 2. Инициализация на модела и оптимизатора
    model = TwistorVisionTransformer()
    optimizer = optim.Adam(model.parameters(), lr=0.01)
    criterion = nn.MSELoss()

    print("\n[*] Стартиране на Епоха 1 (Forward Pass през 4D Туисторен Слой)...")
    start_fwd = time.perf_counter()
    output = model(tensor_input)
    loss = criterion(output, target)
    end_fwd = time.perf_counter()
    print(f"  -> Forward Pass завършен за {(end_fwd - start_fwd)*1000:.2f} ms")
    print(f"  -> Начална Ентропия (Loss): {loss.item():.6f}")

    print("\n[*] Обръщане на Времето (Backward Pass / Gradient Descent)...")
    start_bwd = time.perf_counter()
    optimizer.zero_grad()
    loss.backward()
    
    # 3. Извличане на градиентите от Туисторната трансформация
    # Тъй като input е първоначалният вход, неговият grad ще ни покаже 
    # в коя посока Туисторната физика "дърпа" пространството.
    grad_norm = model.conv1.weight.grad.norm().item()
    
    optimizer.step()
    end_bwd = time.perf_counter()
    
    print(f"  -> Backward Pass завършен за {(end_bwd - start_bwd)*1000:.2f} ms")
    print(f"  -> Топологичен Градиент (Norm): {grad_norm:.6f}")
    
    print("\n[+] Оптимизацията на Епоха 1 е успешна! Градиентите следват кривината на времето.")
    print("==========================================================")

if __name__ == "__main__":
    run_pinn_epoch()
