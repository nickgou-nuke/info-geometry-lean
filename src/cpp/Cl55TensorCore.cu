#include <iostream>
#include <vector>
#include <random>
#include <cmath>
#include <cuda_runtime.h>
#include <mma.h>

using namespace nvcuda;

/* 
 * Cl(5,5) Tensor Core Hardware Implementation
 * 
 * In the split signature (5,5), the Clifford algebra Cl(5,5) is isomorphic to R(32).
 * Spinors are 32-dimensional real vectors.
 * 
 * To maximize Tensor Core utilization, we batch 32 spinors into a 32x32 matrix (X).
 * A global Cl(5,5) operator (A) is applied via dense matrix multiplication: Y = A * X.
 * 
 * Tensor Cores (wmma API) operate natively on 16x16x16 blocks.
 * A 32x32x32 GEMM is decomposed into 8 wmma operations per warp.
 */

const int CL55_DIM = 32;
const int WMMA_M = 16;
const int WMMA_N = 16;
const int WMMA_K = 16;

// Kernel: Computes Y = A * X using Tensor Cores
// A and X are dynamically loaded from global memory.
// A is 32x32 (the global Cl(5,5) operator)
// X is an array of 32x32 matrices (the astronomical spinor batches)
__global__ void cl55_tensor_core_flow_kernel(
    const half* __restrict__ A, 
    const half* __restrict__ X_batches, 
    float* __restrict__ Y_batches, 
    int num_batches) 
{
    // Each warp processes one 32x32x32 batch
    int batch_idx = blockIdx.x * (blockDim.x / 32) + (threadIdx.x / 32);
    if (batch_idx >= num_batches) return;

    // Pointer to this warp's input/output batches
    const half* X = X_batches + batch_idx * CL55_DIM * CL55_DIM;
    float* Y = Y_batches + batch_idx * CL55_DIM * CL55_DIM;

    // Fragments for 16x16 tiles
    wmma::fragment<wmma::matrix_a, WMMA_M, WMMA_N, WMMA_K, half, wmma::row_major> a_frag[2][2];
    wmma::fragment<wmma::matrix_b, WMMA_M, WMMA_N, WMMA_K, half, wmma::col_major> x_frag[2][2];
    wmma::fragment<wmma::accumulator, WMMA_M, WMMA_N, WMMA_K, float> y_frag[2][2];

    // Initialize accumulators
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            wmma::fill_fragment(y_frag[i][j], 0.0f);
        }
    }

    // Load A (Shared across all batches, but for simplicity loaded directly)
    // In production, A should be in __shared__ or constant memory.
    for (int i = 0; i < 2; i++) {
        for (int k = 0; k < 2; k++) {
            wmma::load_matrix_sync(a_frag[i][k], A + i * 16 * CL55_DIM + k * 16, CL55_DIM);
        }
    }

    // Load X (Col-major, since columns are independent spinors)
    for (int k = 0; k < 2; k++) {
        for (int j = 0; j < 2; j++) {
            wmma::load_matrix_sync(x_frag[k][j], X + k * 16 + j * 16 * CL55_DIM, CL55_DIM);
        }
    }

    // Multiply and Accumulate
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            for (int k = 0; k < 2; k++) {
                wmma::mma_sync(y_frag[i][j], a_frag[i][k], x_frag[k][j], y_frag[i][j]);
            }
        }
    }

    // Store the result
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            wmma::store_matrix_sync(Y + i * 16 * CL55_DIM + j * 16, y_frag[i][j], CL55_DIM, wmma::mem_row_major);
        }
    }
}

extern "C" void run_cl55_tensor_core(const half* h_A, const half* h_X, float* h_Y, int num_batches) {
    size_t a_size = CL55_DIM * CL55_DIM * sizeof(half);
    size_t x_size = num_batches * CL55_DIM * CL55_DIM * sizeof(half);
    size_t y_size = num_batches * CL55_DIM * CL55_DIM * sizeof(float);
    
    half *d_A, *d_X;
    float *d_Y;

    cudaMalloc(&d_A, a_size);
    cudaMalloc(&d_X, x_size);
    cudaMalloc(&d_Y, y_size);

    cudaMemcpy(d_A, h_A, a_size, cudaMemcpyHostToDevice);
    cudaMemcpy(d_X, h_X, x_size, cudaMemcpyHostToDevice);

    // 1 Warp (32 threads) processes 1 batch.
    // 8 warps per block = 256 threads.
    int threadsPerBlock = 256;
    int warpsPerBlock = threadsPerBlock / 32;
    int blocks = (num_batches + warpsPerBlock - 1) / warpsPerBlock;
    
    cl55_tensor_core_flow_kernel<<<blocks, threadsPerBlock>>>(d_A, d_X, d_Y, num_batches);
    
    cudaMemcpy(h_Y, d_Y, y_size, cudaMemcpyDeviceToHost);

    cudaFree(d_A);
    cudaFree(d_X);
    cudaFree(d_Y);
}

// Kernel: Computes Y = A * X using Tensor Cores and applies trace reduction
// Returns a single float per batch (the Gibbs-Fermi logit / trace observable).
__global__ void cl55_tensor_core_trace_kernel(
    const half* __restrict__ A, 
    const half* __restrict__ X_batches, 
    float* __restrict__ trace_out, 
    int num_batches) 
{
    int batch_idx = blockIdx.x * (blockDim.x / 32) + (threadIdx.x / 32);
    if (batch_idx >= num_batches) return;

    const half* X = X_batches + batch_idx * CL55_DIM * CL55_DIM;

    wmma::fragment<wmma::matrix_a, WMMA_M, WMMA_N, WMMA_K, half, wmma::row_major> a_frag[2][2];
    wmma::fragment<wmma::matrix_b, WMMA_M, WMMA_N, WMMA_K, half, wmma::col_major> x_frag[2][2];
    wmma::fragment<wmma::accumulator, WMMA_M, WMMA_N, WMMA_K, float> y_frag[2][2];

    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            wmma::fill_fragment(y_frag[i][j], 0.0f);
        }
    }

    for (int i = 0; i < 2; i++) {
        for (int k = 0; k < 2; k++) {
            wmma::load_matrix_sync(a_frag[i][k], A + i * 16 * CL55_DIM + k * 16, CL55_DIM);
        }
    }

    for (int k = 0; k < 2; k++) {
        for (int j = 0; j < 2; j++) {
            wmma::load_matrix_sync(x_frag[k][j], X + k * 16 + j * 16 * CL55_DIM, CL55_DIM);
        }
    }

    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            for (int k = 0; k < 2; k++) {
                wmma::mma_sync(y_frag[i][j], a_frag[i][k], x_frag[k][j], y_frag[i][j]);
            }
        }
    }

    // Instead of storing the full matrix, extract the trace directly from the fragments
    // In WMMA API, we must store to shared memory first to access individual elements
    __shared__ float shmem_Y[32][32];
    
    // The warp stores its fragments into shared memory
    int warp_id = threadIdx.x / 32;
    float* my_shmem = &shmem_Y[0][0]; // For a single warp per block this is fine
    // Note: If multiple warps run in the block, we need a 3D shared memory array
    // To simplify and avoid conflicts, we just use a local array per thread and store via standard API
    // Actually, each warp can write to a unique shared memory tile
    // For simplicity, we allocate dynamic shared memory or a fixed size enough for max warps
}

// Temporary complete trace kernel using a safe shared memory layout
__global__ void cl55_tensor_core_trace_safe_kernel(
    const half* __restrict__ A, 
    const half* __restrict__ X_batches, 
    float* __restrict__ trace_out, 
    int num_batches) 
{
    int batch_idx = blockIdx.x * (blockDim.x / 32) + (threadIdx.x / 32);
    if (batch_idx >= num_batches) return;
    int lane_id = threadIdx.x % 32;
    int warp_id = threadIdx.x / 32;

    extern __shared__ float shared_mem[];
    float* warp_shmem = shared_mem + warp_id * CL55_DIM * CL55_DIM;

    const half* X = X_batches + batch_idx * CL55_DIM * CL55_DIM;

    wmma::fragment<wmma::matrix_a, WMMA_M, WMMA_N, WMMA_K, half, wmma::row_major> a_frag[2][2];
    wmma::fragment<wmma::matrix_b, WMMA_M, WMMA_N, WMMA_K, half, wmma::col_major> x_frag[2][2];
    wmma::fragment<wmma::accumulator, WMMA_M, WMMA_N, WMMA_K, float> y_frag[2][2];

    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            wmma::fill_fragment(y_frag[i][j], 0.0f);
        }
    }

    for (int i = 0; i < 2; i++) {
        for (int k = 0; k < 2; k++) {
            wmma::load_matrix_sync(a_frag[i][k], A + i * 16 * CL55_DIM + k * 16, CL55_DIM);
        }
    }

    for (int k = 0; k < 2; k++) {
        for (int j = 0; j < 2; j++) {
            wmma::load_matrix_sync(x_frag[k][j], X + k * 16 + j * 16 * CL55_DIM, CL55_DIM);
        }
    }

    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            for (int k = 0; k < 2; k++) {
                wmma::mma_sync(y_frag[i][j], a_frag[i][k], x_frag[k][j], y_frag[i][j]);
            }
        }
    }

    // Store to shared memory for reduction
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            wmma::store_matrix_sync(warp_shmem + i * 16 * CL55_DIM + j * 16, y_frag[i][j], CL55_DIM, wmma::mem_row_major);
        }
    }

    // Compute trace: sum of diagonal elements (Y[d][d])
    // The Gibbs-Fermi Logit uses specific observables, for now we map it to the full trace
    float local_sum = 0.0f;
    if (lane_id < 32) {
        local_sum = warp_shmem[lane_id * CL55_DIM + lane_id];
    }
    
    // Warp-level reduction
    for (int offset = 16; offset > 0; offset /= 2) {
        local_sum += __shfl_down_sync(0xffffffff, local_sum, offset);
    }

    // Thread 0 of the warp writes the observable out
    if (lane_id == 0) {
        trace_out[batch_idx] = local_sum;
    }
}

extern "C" void run_cl55_tensor_core_trace(const half* h_A, const half* h_X, float* h_trace_out, int num_batches) {
    size_t a_size = CL55_DIM * CL55_DIM * sizeof(half);
    size_t x_size = num_batches * CL55_DIM * CL55_DIM * sizeof(half);
    size_t out_size = num_batches * sizeof(float);
    
    half *d_A, *d_X;
    float *d_trace_out;

    cudaMalloc(&d_A, a_size);
    cudaMalloc(&d_X, x_size);
    cudaMalloc(&d_trace_out, out_size);

    cudaMemcpy(d_A, h_A, a_size, cudaMemcpyHostToDevice);
    cudaMemcpy(d_X, h_X, x_size, cudaMemcpyHostToDevice);

    int threadsPerBlock = 256;
    int warpsPerBlock = threadsPerBlock / 32;
    int blocks = (num_batches + warpsPerBlock - 1) / warpsPerBlock;
    
    // Dynamic shared memory allocation: CL55_DIM * CL55_DIM * sizeof(float) per warp
    size_t shared_mem_size = warpsPerBlock * CL55_DIM * CL55_DIM * sizeof(float);

    cl55_tensor_core_trace_safe_kernel<<<blocks, threadsPerBlock, shared_mem_size>>>(d_A, d_X, d_trace_out, num_batches);
    
    cudaMemcpy(h_trace_out, d_trace_out, out_size, cudaMemcpyDeviceToHost);

    cudaFree(d_A);
    cudaFree(d_X);
    cudaFree(d_trace_out);
}

/*
 * Phase 3: Continuous Stream Processing (Zero-Latency Pipeline)
 * 
 * Uses CUDA Streams and Pinned (Page-Locked) Memory to overlap H2D transfer, 
 * Kernel Execution, and D2H transfer.
 */
class ContinuousCl55Stream {
private:
    int batches_per_frame;
    size_t a_size;
    size_t x_size;
    size_t out_size;
    
    half *d_A;
    half *h_A_pinned;
    
    // Triple buffering for X and out
    half *d_X[3];
    float *d_trace_out[3];
    half *h_X_pinned[3];
    float *h_trace_pinned[3];
    cudaStream_t streams[3];

    int current_frame;

public:
    ContinuousCl55Stream(int _batches_per_frame) : batches_per_frame(_batches_per_frame), current_frame(0) {
        a_size = CL55_DIM * CL55_DIM * sizeof(half);
        x_size = batches_per_frame * CL55_DIM * CL55_DIM * sizeof(half);
        out_size = batches_per_frame * sizeof(float);

        cudaMalloc(&d_A, a_size);
        cudaMallocHost(&h_A_pinned, a_size);

        for (int i = 0; i < 3; i++) {
            cudaStreamCreate(&streams[i]);
            cudaMalloc(&d_X[i], x_size);
            cudaMalloc(&d_trace_out[i], out_size);
            cudaMallocHost(&h_X_pinned[i], x_size);
            cudaMallocHost(&h_trace_pinned[i], out_size);
        }
    }

    ~ContinuousCl55Stream() {
        cudaFree(d_A);
        cudaFreeHost(h_A_pinned);
        for (int i = 0; i < 3; i++) {
            cudaStreamDestroy(streams[i]);
            cudaFree(d_X[i]);
            cudaFree(d_trace_out[i]);
            cudaFreeHost(h_X_pinned[i]);
            cudaFreeHost(h_trace_pinned[i]);
        }
    }

    // Set the global operator (A)
    void set_operator(const half* A_src) {
        memcpy(h_A_pinned, A_src, a_size);
        cudaMemcpy(d_A, h_A_pinned, a_size, cudaMemcpyHostToDevice);
    }

    // Process a single frame asynchronously
    // Returns a pointer to the Pinned Memory containing the trace results of the PREVIOUS frame
    // that just finished. The caller can safely read it.
    const float* process_frame_async(const half* frame_data) {
        int stream_idx = current_frame % 3;
        
        // Ensure the stream is ready (waits for the oldest frame to finish)
        cudaStreamSynchronize(streams[stream_idx]);
        
        // Copy the newly finished result out (from the previous cycle of this stream index)
        // Wait, since we synced, h_trace_pinned[stream_idx] is ready to be read by the host!
        // But we are about to overwrite it with the NEW frame.
        // Actually, the result we want to return is the one that just finished.
        // The host should read it before calling process_frame_async again.
        
        // Start the new frame pipeline
        memcpy(h_X_pinned[stream_idx], frame_data, x_size);
        cudaMemcpyAsync(d_X[stream_idx], h_X_pinned[stream_idx], x_size, cudaMemcpyHostToDevice, streams[stream_idx]);
        
        int threadsPerBlock = 256;
        int warpsPerBlock = threadsPerBlock / 32;
        int blocks = (batches_per_frame + warpsPerBlock - 1) / warpsPerBlock;
        size_t shared_mem_size = warpsPerBlock * CL55_DIM * CL55_DIM * sizeof(float);
        
        cl55_tensor_core_trace_safe_kernel<<<blocks, threadsPerBlock, shared_mem_size, streams[stream_idx]>>>(
            d_A, d_X[stream_idx], d_trace_out[stream_idx], batches_per_frame);
            
        cudaMemcpyAsync(h_trace_pinned[stream_idx], d_trace_out[stream_idx], out_size, cudaMemcpyDeviceToHost, streams[stream_idx]);
        
        // Return the pointer to the buffer of the PREVIOUS frame (which we know is finished since we synced stream (current_frame-2)%3)
        // Note: For the first 2 frames, the returned buffer contains garbage.
        int return_idx = (current_frame + 1) % 3;
        cudaStreamSynchronize(streams[return_idx]); // Ensure the previous frame actually finished so we can read it safely
        
        current_frame++;
        return h_trace_pinned[return_idx];
    }
};

int main() {
    // Astronomical dataset: 10 million spinors = ~312,500 batches of 32
    int total_spinors = 10000000;
    int num_batches = (total_spinors + CL55_DIM - 1) / CL55_DIM;
    
    std::cout << "Initializing Cl(5,5) Tensor Core pipeline...\n";
    std::cout << "Total Spinors: " << total_spinors << "\n";
    std::cout << "Batches (32x32): " << num_batches << "\n";

    size_t a_size = CL55_DIM * CL55_DIM * sizeof(half);
    size_t x_size = num_batches * CL55_DIM * CL55_DIM * sizeof(half);
    size_t y_size = num_batches * CL55_DIM * CL55_DIM * sizeof(float);

    half* h_A = (half*)malloc(a_size);
    half* h_X = (half*)malloc(x_size);
    float* h_Y = (float*)malloc(y_size);

    cudaEvent_t start, stop;
    cudaEventCreate(&start);
    cudaEventCreate(&stop);
    
    cudaEventRecord(start);
    run_cl55_tensor_core(h_A, h_X, h_Y, num_batches);
    cudaEventRecord(stop);
    
    cudaDeviceSynchronize();
    
    float ms = 0;
    cudaEventElapsedTime(&ms, start, stop);
    
    std::cout << "Execution completed in " << ms << " ms.\n";
    std::cout << "Effective Throughput: " << (double)total_spinors / (ms * 1e-3) / 1e9 << " Billion Spinors/sec.\n";

    free(h_A);
    free(h_X);
    free(h_Y);

    return 0;
}

extern "C" {
    void* create_continuous_stream(int batches_per_frame) {
        return new ContinuousCl55Stream(batches_per_frame);
    }

    void destroy_continuous_stream(void* ptr) {
        delete static_cast<ContinuousCl55Stream*>(ptr);
    }

    void stream_set_operator(void* ptr, const void* h_A) {
        static_cast<ContinuousCl55Stream*>(ptr)->set_operator(static_cast<const half*>(h_A));
    }

    const float* stream_process_frame(void* ptr, const void* h_X) {
        return static_cast<ContinuousCl55Stream*>(ptr)->process_frame_async(static_cast<const half*>(h_X));
    }
}
