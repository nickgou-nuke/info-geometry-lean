#include "ModularMath.cuh"
#include <cuda_runtime.h>
#include <iostream>
#include <cmath>

// Константна памет за Лоренцовия ротор (B_t) - достъп за 1 цикъл за всички нишки
__constant__ ClPlus const_B_t;

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
// The Grand Kernel: Tomita-Takesaki Gibbs-Fermi Sensor
// ---------------------------------------------------------
__global__ void gibbs_fermi_kernel(const double* raw_in, double* clean_out, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;

    // 1. Извличане на пиксела и превръщането му в енергиен разрив (Logit)
    double p = raw_in[idx];
    double energy_gap = logit_d(p);

    // 2. The Twistor Lift (Вдигаме в ZornMatrix / ClPlus)
    ClPlus X;
    X.z00 = make_cuDoubleComplex(1.0, 0.0);
    X.z01 = make_cuDoubleComplex(0.0, 0.0);
    X.z10 = make_cuDoubleComplex(energy_gap, 0.0);
    X.z11 = make_cuDoubleComplex(0.0, 0.0);

    // 3. Модулярен поток: X_evolved = B_t * X * B_{-t}
    ClPlus X_evolved = ModularFlow(const_B_t, X);

    // 4. Trace Projection (Извличаме филтрираната енергия)
    double filtered_energy = cuCreal(X_evolved.z10);

    // 5. Gibbs-Fermi Admission (Връщаме класическа вероятност)
    clean_out[idx] = sigmoid_d(filtered_energy);
}

// ---------------------------------------------------------
// C-API за Python / PyBind11
// ---------------------------------------------------------
void launch_gibbs_fermi_sensor(const double* h_raw, double* h_clean, int N, double t) {
    // 1. Инициализация на Лоренцов бууст
    double ch = cosh(t / 2.0);
    double sh = sinh(t / 2.0);
    
    ClPlus host_B_t;
    host_B_t.z00 = make_cuDoubleComplex(ch + sh, 0.0);
    host_B_t.z01 = make_cuDoubleComplex(0.0, 0.0);
    host_B_t.z10 = make_cuDoubleComplex(0.0, 0.0);
    host_B_t.z11 = make_cuDoubleComplex(ch - sh, 0.0);

    // Копиране в константната памет
    cudaMemcpyToSymbol(const_B_t, &host_B_t, sizeof(ClPlus));

    // 2. Алокиране на памет на GPU
    double *d_raw, *d_clean;
    cudaMalloc((void**)&d_raw, N * sizeof(double));
    cudaMalloc((void**)&d_clean, N * sizeof(double));

    // 3. Прехвърляне (Host -> Device)
    cudaMemcpy(d_raw, h_raw, N * sizeof(double), cudaMemcpyHostToDevice);

    // 4. Изпълнение на Ядрото (256 нишки на блок)
    int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    gibbs_fermi_kernel<<<blocksPerGrid, threadsPerBlock>>>(d_raw, d_clean, N);

    // Синхронизация за точно измерване
    cudaDeviceSynchronize();

    // 5. Връщане на резултата (Device -> Host)
    cudaMemcpy(h_clean, d_clean, N * sizeof(double), cudaMemcpyDeviceToHost);

    // Освобождаване на паметта
    cudaFree(d_raw);
    cudaFree(d_clean);
}
