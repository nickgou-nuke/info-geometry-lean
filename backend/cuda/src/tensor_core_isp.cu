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

__global__ void twistor_lift_kernel(const double* raw_in, cuDoubleComplex* z_matrix, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;
    
    double p = raw_in[idx];
    p = fmax(1e-7, fmin(1.0 - 1e-7, p));
    double energy_gap = log(p / (1.0 - p));
    
    z_matrix[0 * N + idx] = make_cuDoubleComplex(1.0, 0.0);
    z_matrix[1 * N + idx] = make_cuDoubleComplex(0.0, 0.0);
    z_matrix[2 * N + idx] = make_cuDoubleComplex(energy_gap, 0.0);
    z_matrix[3 * N + idx] = make_cuDoubleComplex(0.0, 0.0);
}

__global__ void trace_projection_kernel(const cuDoubleComplex* z_out, double* clean_out, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;
    
    double filtered_energy = cuCreal(z_out[2 * N + idx]);
    clean_out[idx] = 1.0 / (1.0 + exp(-filtered_energy));
}

// Persistent GPU Context
struct TwistorEngine {
    uint32_t N;
    cudaStream_t stream;
    cublasHandle_t cublas;
    
    cuDoubleComplex* d_Z_matrix;
    cuDoubleComplex* d_B_t;
    cuDoubleComplex* d_Z_out;
    double* d_raw_in;
    double* d_clean_out;
    
    // Pinned Host Memory for zero-copy transfers
    double* h_pinned_in;
    double* h_pinned_out;
};

// Lean External Object class registration
static lean_external_class* g_engine_class = nullptr;

static void engine_finalizer(void* ptr) {
    TwistorEngine* eng = static_cast<TwistorEngine*>(ptr);
    cudaFreeHost(eng->h_pinned_in);
    cudaFreeHost(eng->h_pinned_out);
    cudaFree(eng->d_Z_matrix);
    cudaFree(eng->d_B_t);
    cudaFree(eng->d_Z_out);
    cudaFree(eng->d_raw_in);
    cudaFree(eng->d_clean_out);
    cublasDestroy(eng->cublas);
    cudaStreamDestroy(eng->stream);
    delete eng;
}

static void engine_foreach(void* ptr, b_lean_obj_arg b) {
    // No nested Lean objects
}

extern "C" {

lean_obj_res cuda_init_twistor_engine(uint32_t N) {
    printf("C++: Inside cuda_init_twistor_engine, N = %d\n", N);
    fflush(stdout);
    if (g_engine_class == nullptr) {
        g_engine_class = lean_register_external_class(engine_finalizer, engine_foreach);
    }
    
    TwistorEngine* eng = new TwistorEngine();
    eng->N = N;
    
    CUDA_CHECK(cudaStreamCreate(&eng->stream));
    cublasCreate(&eng->cublas);
    cublasSetStream(eng->cublas, eng->stream);
    cublasSetMathMode(eng->cublas, CUBLAS_TENSOR_OP_MATH);
    
    // Allocate Device Memory
    CUDA_CHECK(cudaMalloc((void**)&eng->d_Z_matrix, 4 * N * sizeof(cuDoubleComplex)));
    CUDA_CHECK(cudaMalloc((void**)&eng->d_B_t, 4 * 4 * sizeof(cuDoubleComplex)));
    CUDA_CHECK(cudaMalloc((void**)&eng->d_Z_out, 4 * N * sizeof(cuDoubleComplex)));
    CUDA_CHECK(cudaMalloc((void**)&eng->d_raw_in, N * sizeof(double)));
    CUDA_CHECK(cudaMalloc((void**)&eng->d_clean_out, N * sizeof(double)));
    
    // Allocate Pinned Host Memory
    CUDA_CHECK(cudaMallocHost((void**)&eng->h_pinned_in, N * sizeof(double)));
    CUDA_CHECK(cudaMallocHost((void**)&eng->h_pinned_out, N * sizeof(double)));
    
    return lean_io_result_mk_ok(lean_alloc_external(g_engine_class, eng));
}

lean_obj_res cuda_execute_twistor_engine(lean_obj_arg engine_obj, double t, lean_obj_arg raw_pixels_obj) {
    TwistorEngine* eng = static_cast<TwistorEngine*>(lean_get_external_data(engine_obj));
    uint32_t N = eng->N;
    double* h_raw_pixels = lean_float_array_cptr(raw_pixels_obj);
    
    // 1. Copy Lean Array to Pinned Memory (Fast CPU copy)
    memcpy(eng->h_pinned_in, h_raw_pixels, N * sizeof(double));
    
    // 2. Async H2D Transfer
    CUDA_CHECK(cudaMemcpyAsync(eng->d_raw_in, eng->h_pinned_in, N * sizeof(double), cudaMemcpyHostToDevice, eng->stream));
    
    // 3. Prepare Boost Matrix
    double ch = std::cosh(t / 2.0);
    double sh = std::sinh(t / 2.0);
    cuDoubleComplex h_B_t[16] = {make_cuDoubleComplex(0,0)};
    h_B_t[0]  = make_cuDoubleComplex(ch + sh, 0); 
    h_B_t[5]  = make_cuDoubleComplex(ch - sh, 0); 
    h_B_t[10] = make_cuDoubleComplex(ch - sh, 0); 
    h_B_t[15] = make_cuDoubleComplex(ch + sh, 0); 
    CUDA_CHECK(cudaMemcpyAsync(eng->d_B_t, h_B_t, 16 * sizeof(cuDoubleComplex), cudaMemcpyHostToDevice, eng->stream));
    
    // 4. Launch Lift Kernel
    int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    twistor_lift_kernel<<<blocksPerGrid, threadsPerBlock, 0, eng->stream>>>(eng->d_raw_in, eng->d_Z_matrix, N);
    
    // 5. GEMM Tensor Cores
    cuDoubleComplex alpha = make_cuDoubleComplex(1.0, 0.0);
    cuDoubleComplex beta  = make_cuDoubleComplex(0.0, 0.0);
    cublasZgemm(eng->cublas, CUBLAS_OP_N, CUBLAS_OP_N,
                4, N, 4,
                &alpha, eng->d_B_t, 4,
                eng->d_Z_matrix, 4,
                &beta, eng->d_Z_out, 4);
                
    // 6. Trace Projection Kernel
    trace_projection_kernel<<<blocksPerGrid, threadsPerBlock, 0, eng->stream>>>(eng->d_Z_out, eng->d_clean_out, N);
    
    // 7. Async D2H Transfer
    CUDA_CHECK(cudaMemcpyAsync(eng->h_pinned_out, eng->d_clean_out, N * sizeof(double), cudaMemcpyDeviceToHost, eng->stream));
    
    // 8. Synchronize Stream to wait for completion
    CUDA_CHECK(cudaStreamSynchronize(eng->stream));
    
    // 9. Copy to Lean Array
    lean_object* clean_pixels_obj = lean_alloc_sarray(sizeof(double), N, N);
    double* h_clean_pixels = lean_float_array_cptr(clean_pixels_obj);
    memcpy(h_clean_pixels, eng->h_pinned_out, N * sizeof(double));
    
    // Release objects
    lean_dec(raw_pixels_obj);
    
    return clean_pixels_obj;
}

} // extern "C"
