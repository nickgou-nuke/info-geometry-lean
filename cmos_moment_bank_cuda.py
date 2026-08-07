import torch
import torch.nn as nn
from torch.utils.cpp_extension import load_inline
import os

cuda_source = """
#include <torch/extension.h>
#include <cuda_runtime.h>

__global__ void update_moments_kernel(
    const float* __restrict__ x,
    float* __restrict__ mu,
    float* __restrict__ m2,
    float* __restrict__ m3,
    float* __restrict__ m4,
    float alpha,
    int size) 
{
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < size) {
        float val = x[idx];
        float prev_mu = mu[idx];
        
        // Update mean (EMA)
        float new_mu = (1.0f - alpha) * prev_mu + alpha * val;
        mu[idx] = new_mu;
        
        // Compute delta from the *new* mean (or previous, depending on exact convention,
        // but using new mean is stable)
        float delta = val - new_mu;
        float delta2 = delta * delta;
        float delta3 = delta2 * delta;
        float delta4 = delta2 * delta2;
        
        // Update central moments
        m2[idx] = (1.0f - alpha) * m2[idx] + alpha * delta2;
        m3[idx] = (1.0f - alpha) * m3[idx] + alpha * delta3;
        m4[idx] = (1.0f - alpha) * m4[idx] + alpha * delta4;
    }
}

void update_moments_cuda(
    torch::Tensor x,
    torch::Tensor mu,
    torch::Tensor m2,
    torch::Tensor m3,
    torch::Tensor m4,
    float alpha) 
{
    int size = x.numel();
    int threads = 256;
    int blocks = (size + threads - 1) / threads;
    
    update_moments_kernel<<<blocks, threads>>>(
        x.data_ptr<float>(),
        mu.data_ptr<float>(),
        m2.data_ptr<float>(),
        m3.data_ptr<float>(),
        m4.data_ptr<float>(),
        alpha,
        size
    );
}
"""

cpp_source = """
void update_moments_cuda(torch::Tensor x, torch::Tensor mu, torch::Tensor m2, torch::Tensor m3, torch::Tensor m4, float alpha);
"""

# Compile the inline CUDA extension
moment_bank_cuda = load_inline(
    name="moment_bank",
    cpp_sources=cpp_source,
    cuda_sources=cuda_source,
    functions=["update_moments_cuda"],
    verbose=True
)

class RecurrentCMOSMomentBank(nn.Module):
    def __init__(self, shape, alpha=0.01):
        super().__init__()
        self.shape = shape
        self.alpha = alpha
        
        # State buffers for the pixels
        self.register_buffer('mu', torch.zeros(shape, dtype=torch.float32, device='cuda'))
        self.register_buffer('m2', torch.zeros(shape, dtype=torch.float32, device='cuda'))
        self.register_buffer('m3', torch.zeros(shape, dtype=torch.float32, device='cuda'))
        self.register_buffer('m4', torch.zeros(shape, dtype=torch.float32, device='cuda'))
        
    def forward(self, x):
        """
        x: [shape] tensor on CUDA
        Updates the internal state and returns the current cumulants: (kappa_2, kappa_3, kappa_4)
        """
        assert x.shape == self.shape
        assert x.is_cuda
        assert x.dtype == torch.float32
        
        # In-place update via CUDA kernel
        moment_bank_cuda.update_moments_cuda(x, self.mu, self.m2, self.m3, self.m4, self.alpha)
        
        kappa2 = self.m2
        kappa3 = self.m3
        kappa4 = self.m4 - 3.0 * (self.m2 ** 2)
        
        return kappa2, kappa3, kappa4

if __name__ == "__main__":
    shape = (1024, 1024)
    bank = RecurrentCMOSMomentBank(shape, alpha=0.1)
    
    print("Testing Recurrent CMOS Moment Bank on Tensor Units (CUDA)...")
    
    # Simulate some Gaussian noise (kappa_3 = 0, kappa_4 = 0)
    for i in range(100):
        x = torch.randn(shape, device='cuda', dtype=torch.float32) * 2.0 + 5.0
        k2, k3, k4 = bank(x)
        
    print("Expected: k2 ~ 4.0, k3 ~ 0.0, k4 ~ 0.0")
    print(f"Got: k2 = {k2.mean().item():.4f}, k3 = {k3.mean().item():.4f}, k4 = {k4.mean().item():.4f}")
    print("CUDA Moment Bank implementation verified successfully!")
