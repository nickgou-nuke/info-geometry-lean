#include <lean/lean.h>
#include <cuda_runtime.h>
#include <cublas_v2.h>
#include <cmath>
#include <iostream>

#define CUDA_CHECK(err) \
    if (err != cudaSuccess) { \
        std::cerr << "CUDA Error: " << cudaGetErrorString(err) << std::endl; \
        exit(-1); \
    }

__device__ __forceinline__ double logit_d(double p) {
    p = fmax(1e-7, fmin(1.0 - 1e-7, p));
    return log(p / (1.0 - p));
}

__device__ __forceinline__ double sigmoid_d(double E) {
    return 1.0 / (1.0 + exp(-E));
}

// Кернел за повдигане на пиксели в Туистори (Column-Major 4xN матрица)
__global__ void twistor_lift_kernel(const double* raw_in, cuDoubleComplex* Z_matrix, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;
    
    double p = raw_in[idx];
    double energy_gap = logit_d(p);
    
    // В cuBLAS Column-Major, колона `idx` започва от `idx * 4`
    int col_offset = idx * 4;
    Z_matrix[col_offset + 0] = make_cuDoubleComplex(1.0, 0.0);
    Z_matrix[col_offset + 1] = make_cuDoubleComplex(0.0, 0.0);
    Z_matrix[col_offset + 2] = make_cuDoubleComplex(energy_gap, 0.0);
    Z_matrix[col_offset + 3] = make_cuDoubleComplex(0.0, 0.0);
}

// Кернел за проекция на филтрираните Туистори обратно в пиксели
__global__ void twistor_project_kernel(const cuDoubleComplex* Z_out, double* clean_out, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;
    
    int col_offset = idx * 4;
    double filtered_energy = cuCreal(Z_out[col_offset + 2]);
    clean_out[idx] = sigmoid_d(filtered_energy);
}

extern "C" {

lean_obj_res cuda_tensorcore_modular_flow(uint32_t N, double t, lean_obj_arg raw_pixels_obj) {
    // 1. Извличане на данните от Lean 4 без копиране (Zero-Copy on Host)
    double* h_raw_pixels = lean_float_array_cptr(raw_pixels_obj);

    // 2. Алокиране на VRAM
    double* d_raw_pixels;
    double* d_clean_pixels;
    cuDoubleComplex* d_Z_matrix;
    cuDoubleComplex* d_B_t;
    cuDoubleComplex* d_Z_out;
    
    CUDA_CHECK(cudaMalloc((void**)&d_raw_pixels, N * sizeof(double)));
    CUDA_CHECK(cudaMalloc((void**)&d_clean_pixels, N * sizeof(double)));
    CUDA_CHECK(cudaMalloc((void**)&d_Z_matrix, 4 * N * sizeof(cuDoubleComplex)));
    CUDA_CHECK(cudaMalloc((void**)&d_B_t, 4 * 4 * sizeof(cuDoubleComplex)));
    CUDA_CHECK(cudaMalloc((void**)&d_Z_out, 4 * N * sizeof(cuDoubleComplex)));

    // Копиране на суровите пиксели към GPU
    CUDA_CHECK(cudaMemcpy(d_raw_pixels, h_raw_pixels, N * sizeof(double), cudaMemcpyHostToDevice));

    // 3. Подготовка на Лоренцовия Бууст B_t (4x4) на Хоста
    double ch = cosh(t / 2.0);
    double sh = sinh(t / 2.0);
    cuDoubleComplex h_B_t[16] = {make_cuDoubleComplex(0,0)};
    // Запълване на диагонала (Column-major формат за cuBLAS)
    h_B_t[0]  = make_cuDoubleComplex(ch + sh, 0); // (0,0)
    h_B_t[5]  = make_cuDoubleComplex(ch - sh, 0); // (1,1)
    h_B_t[10] = make_cuDoubleComplex(ch - sh, 0); // (2,2)
    h_B_t[15] = make_cuDoubleComplex(ch + sh, 0); // (3,3)
    CUDA_CHECK(cudaMemcpy(d_B_t, h_B_t, 16 * sizeof(cuDoubleComplex), cudaMemcpyHostToDevice));

    // 4. Custom Kernel: Превръщане на Lean FloatArray в Туистор матрица на GPU
    int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    twistor_lift_kernel<<<blocksPerGrid, threadsPerBlock>>>(d_raw_pixels, d_Z_matrix, N);

    // 5. Инициализация на cuBLAS и ТЕНЗОРНИТЕ ЯДРА (The Magic!)
    cublasHandle_t handle;
    cublasCreate(&handle);
    // НАРЕЖДАМЕ ИЗПОЛЗВАНЕТО НА NVIDIA TENSOR CORES
    cublasSetMathMode(handle, CUBLAS_TENSOR_OP_MATH);

    cuDoubleComplex alpha = make_cuDoubleComplex(1.0, 0.0);
    cuDoubleComplex beta  = make_cuDoubleComplex(0.0, 0.0);

    // 6. Хардуерното Умножение: Z_out = B_t * Z_matrix
    cublasZgemm(handle, CUBLAS_OP_N, CUBLAS_OP_N,
                4, N, 4,
                &alpha,
                d_B_t, 4,
                d_Z_matrix, 4,
                &beta,
                d_Z_out, 4);

    // 7. Изтегляне на резултата и прилагане на Gibbs-Fermi (sigmoid)
    twistor_project_kernel<<<blocksPerGrid, threadsPerBlock>>>(d_Z_out, d_clean_pixels, N);
    
    // Създаваме нов Lean FloatArray за резултата
    lean_object* clean_pixels_obj = lean_alloc_sarray(sizeof(double), N, N);
    double* h_clean_pixels = lean_float_array_cptr(clean_pixels_obj);
    
    CUDA_CHECK(cudaMemcpy(h_clean_pixels, d_clean_pixels, N * sizeof(double), cudaMemcpyDeviceToHost));
    
    // Почистване
    cublasDestroy(handle);
    cudaFree(d_raw_pixels); cudaFree(d_clean_pixels);
    cudaFree(d_Z_matrix); cudaFree(d_B_t); cudaFree(d_Z_out);
    
    // Намаляваме брояча на референциите на входния обект
    lean_dec(raw_pixels_obj);

    return clean_pixels_obj;
}

} // extern "C"
