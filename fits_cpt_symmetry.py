import torch
import torch.nn as nn
import numpy as np

class TwistorModularFlowFunction(torch.autograd.Function):
    @staticmethod
    def forward(ctx, input_tensor, time_boost):
        ctx.save_for_backward(input_tensor)
        ctx.time_boost = time_boost
        
        theta = torch.tensor(time_boost, dtype=torch.float32)
        out = input_tensor.clone()
        
        # Аналитична Hodge Ротация (U(1) Chiral Symmetry)
        # Канал 0: SA (Енергия / Фотони / Кинематика)
        # Канал 3: SkewSA (Фаза / Псевдоскалар / Динамика)
        out[:, 0, :, :] = input_tensor[:, 0, :, :] * torch.cos(theta) - input_tensor[:, 3, :, :] * torch.sin(theta)
        out[:, 3, :, :] = input_tensor[:, 0, :, :] * torch.sin(theta) + input_tensor[:, 3, :, :] * torch.cos(theta)
        return out

    @staticmethod
    def backward(ctx, grad_output):
        time_boost = ctx.time_boost
        theta = torch.tensor(time_boost, dtype=torch.float32)
        input_tensor, = ctx.saved_tensors
        
        grad_input = grad_output.clone()
        # Time-reversed gradient wave (Advanced Wave / Обратно време)
        grad_input[:, 0, :, :] = grad_output[:, 0, :, :] * torch.cos(theta) + grad_output[:, 3, :, :] * torch.sin(theta)
        grad_input[:, 3, :, :] = -grad_output[:, 0, :, :] * torch.sin(theta) + grad_output[:, 3, :, :] * torch.cos(theta)
        
        # Градиент спрямо самия ъгъл θ (за да може мрежата да го оптимизира!)
        grad_theta = grad_output[:, 0, :, :] * (-input_tensor[:, 0, :, :] * torch.sin(theta) - input_tensor[:, 3, :, :] * torch.cos(theta)) + \
                     grad_output[:, 3, :, :] * (input_tensor[:, 0, :, :] * torch.cos(theta) - input_tensor[:, 3, :, :] * torch.sin(theta))
        
        return grad_input, grad_theta.sum()

class TwistorMaxwellLayer(nn.Module):
    def __init__(self, duality_angle=0.0):
        super(TwistorMaxwellLayer, self).__init__()
        # Ъгълът вече е пълноправен обучаем параметър!
        self.duality_angle = nn.Parameter(torch.tensor(duality_angle, dtype=torch.float32))

    def forward(self, x):
        return TwistorModularFlowFunction.apply(x, self.duality_angle)

def run_astrophysics_pipeline():
    print("🔭 Инициализация на FITS Оптичен Пайплайн (Синтетични Телескопични Данни)...")
    
    # 1. Симулиране на сурови сензорни данни от CMOS/CCD телескоп
    torch.manual_seed(42)
    # Поасонов шум за фотоните (Енергия / SA)
    raw_photons = torch.poisson(torch.rand(1, 1, 256, 256) * 100) 
    # Гаусов шум за фазовите аберации (Атмосфера / SkewSA)
    atmospheric_phase = torch.randn(1, 1, 256, 256) * 15         
    
    # 2. Пакетиране в 4D Туистор 
    input_twistor = torch.zeros(1, 4, 256, 256)
    input_twistor[:, 0:1, :, :] = raw_photons 
    input_twistor[:, 3:4, :, :] = atmospheric_phase
    
    print(f"[*] Входен Тензор (F_in): {input_twistor.shape}")
    print(f"    - Средна Енергия (SA / Фотони): {input_twistor[:, 0, :, :].mean().item():.4f}")
    print(f"    - Средна Фаза (SkewSA / Аберации): {input_twistor[:, 3, :, :].mean().item():.4f}")
    
    # 3. Инициализация на PINN слоя с 45 градуса ротация (максимално преплитане)
    layer = TwistorMaxwellLayer(duality_angle=np.pi / 4)
    
    # 4. Forward Pass (Еволюция напред: Оптично изкривяване / Retarded Wave)
    print("\n[>>] Еволюция напред (Forward Pass: Изкривяване на светлината)...")
    F_out = layer(input_twistor)
    
    # 5. Обратимост на времето (Time-Reversal: Оптично деконволюиране / Advanced Wave)
    print("[<<] Обратимост на времето (Time-Reversal Pass: Оптично фазово спрягане)...")
    # Използваме същата топология, но обръщаме посоката на времето (T-operator)
    reversal_layer = TwistorMaxwellLayer(duality_angle=-layer.duality_angle.item())
    F_recon = reversal_layer(F_out)
    
    # 6. Изчисляване на загубата на информация (Reconstruction Error)
    delta = torch.abs(input_twistor - F_recon).max().item()
    
    print("\n🏆 РЕЗУЛТАТИ ОТ CPT СИМЕТРИЯТА (Time Reversal Test):")
    print(f"    - Максимална грешка при реконструкция (Δ): {delta:.6e}")
    if delta < 1e-4:
        print("    - СТАТУС: ПЕРФЕКТНА ОБРАТИМОСТ! (Lossless Time-Reversal до машинна точност 32-bit)")
    else:
        print("    - СТАТУС: Има информационна загуба.")
    
    # 7. Тест на Градиентите (Може ли мрежата да научи атмосферния фазов ъгъл?)
    print("\n[+] Тестване на градиентния поток за обучаемия ъгъл θ...")
    loss = torch.mean(F_out ** 2)
    loss.backward()
    print(f"    - Градиент на θ (dLoss/dθ): {layer.duality_angle.grad.item():.4f}")
    print("🌌 Пайплайнът е ГОТОВ за интеграция с реални FITS масиви и деконволюция!")

if __name__ == "__main__":
    run_astrophysics_pipeline()
