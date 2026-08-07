#include "ZornFFI.h"
#include <cuda_runtime.h>
#include <iostream>
#include <cmath>

// Глобална константна памет за Лоренцовия бууст (Светкавичен достъп за всички нишки)
__constant__ cuDoubleComplex const_B_t[4];     // B_t
__constant__ cuDoubleComplex const_B_t_inv[4]; // B_{-t}

// Малки inline функции за матрично умножение в регистрите (ClPlus * ClPlus)
__device__ __forceinline__ void multiply_clplus(
    cuDoubleComplex a00, cuDoubleComplex a01, cuDoubleComplex a10, cuDoubleComplex a11,
    cuDoubleComplex b00, cuDoubleComplex b01, cuDoubleComplex b10, cuDoubleComplex b11,
    cuDoubleComplex &out00, cuDoubleComplex &out01, cuDoubleComplex &out10, cuDoubleComplex &out11) 
{
    out00 = cuCadd(cuCmul(a00, b00), cuCmul(a01, b10));
    out01 = cuCadd(cuCmul(a00, b01), cuCmul(a01, b11));
    out10 = cuCadd(cuCmul(a10, b00), cuCmul(a11, b10));
    out11 = cuCadd(cuCmul(a10, b01), cuCmul(a11, b11));
}

// ---------------------------------------------------------
// Pixel <-> Logit Bridges
// ---------------------------------------------------------
__device__ __forceinline__ double logit_d(double p) {
    p = fmax(1e-7, fmin(1.0 - 1e-7, p));
    return log(p / (1.0 - p));
}

__device__ __forceinline__ double sigmoid_d(double E) {
    return 1.0 / (1.0 + exp(-E));
}

// ---------------------------------------------------------
// The Grand Kernel: Tomita-Takesaki Modular Flow for ISP
// ---------------------------------------------------------
__global__ void execute_isp_kernel(const double* img_in, double* img_out, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;

    // 1. Pixel to Logit (Energy Gap)
    double p = img_in[idx];
    double energy_gap = logit_d(p);

    // 2. The Twistor Lift
    // Z = (ω^0, ω^1, π_0', π_1') => Represented as 2x2 ClPlus Matrix
    // We map π_0' (index 2) to z10 for matrix multiplication
    cuDoubleComplex x00 = make_cuDoubleComplex(1.0, 0.0);
    cuDoubleComplex x01 = make_cuDoubleComplex(0.0, 0.0);
    cuDoubleComplex x10 = make_cuDoubleComplex(energy_gap, 0.0);
    cuDoubleComplex x11 = make_cuDoubleComplex(0.0, 0.0);

    // 3. Modular Flow: Y = B_t * X
    cuDoubleComplex y00, y01, y10, y11;
    multiply_clplus(
        const_B_t[0], const_B_t[1], const_B_t[2], const_B_t[3], // B_t
        x00, x01, x10, x11,                                     // X
        y00, y01, y10, y11
    );

    // 4. Sensor Projection (Trace logic) -> extracting the filtered energy
    double filtered_energy = cuCreal(y10); // Extract evolved energy gap

    // 5. Logit to Pixel (Gibbs-Fermi Admission)
    img_out[idx] = sigmoid_d(filtered_energy);
}

// ---------------------------------------------------------
// C-API for Python/ctypes
// ---------------------------------------------------------
extern "C" void run_twistor_isp_cuda(int N, double t, const double* host_in, double* host_out) {
    // 1. Calculate Lorentz Boost (Host)
    double ch = cosh(t / 2.0);
    double sh = sinh(t / 2.0);
    cuDoubleComplex host_B_t[4] = {
        make_cuDoubleComplex(ch + sh, 0.0), make_cuDoubleComplex(0.0, 0.0),
        make_cuDoubleComplex(0.0, 0.0),     make_cuDoubleComplex(ch - sh, 0.0)
    };
    cudaMemcpyToSymbol(const_B_t, host_B_t, 4 * sizeof(cuDoubleComplex));

    // 2. Allocate and transfer Device memory
    double *d_in, *d_out;
    cudaMalloc(&d_in, N * sizeof(double));
    cudaMalloc(&d_out, N * sizeof(double));
    
    cudaMemcpy(d_in, host_in, N * sizeof(double), cudaMemcpyHostToDevice);

    // 3. Launch Kernel
    int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    execute_isp_kernel<<<blocksPerGrid, threadsPerBlock>>>(d_in, d_out, N);
    
    // 4. Retrieve data
    cudaMemcpy(host_out, d_out, N * sizeof(double), cudaMemcpyDeviceToHost);
    
    cudaFree(d_in);
    cudaFree(d_out);
}

// ---------------------------------------------------------
// Lean 4 FFI Входна точка (Placeholder removed for Python integration)
// ---------------------------------------------------------
