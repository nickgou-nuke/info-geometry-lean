#include "twistor_ffi.h"
#include <cuda_runtime.h>
#include <cuComplex.h>
#include <iostream>
#include <cmath>

// Struct of Arrays (SoA) Device memory layout for Twistor Field
struct TwistorField_SoA_Device {
    uint32_t num_twistors;
    cuDoubleComplex* z00; 
    cuDoubleComplex* z10;
    cuDoubleComplex* z01;
    cuDoubleComplex* z11;
};

// Global constant memory for the Continuous Lorentz Boost Rotor (B_t) and its inverse (B_{-t})
__constant__ cuDoubleComplex const_B_t[4];     // [b00, b10, b01, b11]
__constant__ cuDoubleComplex const_B_t_inv[4];

// FMA-based Complex Multiplication
__device__ inline cuDoubleComplex mul_complex(cuDoubleComplex a, cuDoubleComplex b) {
    return cuCmul(a, b); // cuCmul utilizes fast instructions where possible
}
__device__ inline cuDoubleComplex add_complex(cuDoubleComplex a, cuDoubleComplex b) {
    return cuCadd(a, b);
}

// Batched Kernel for Tomita-Takesaki Modular Flow
__global__ void execute_modular_flow_kernel(TwistorField_SoA_Device field_in, TwistorField_SoA_Device field_out, uint32_t N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;

    // 1. Load the local Twistor / Clifford state (Quantum state) via coalesced SoA memory access
    cuDoubleComplex x00 = field_in.z00[idx];
    cuDoubleComplex x10 = field_in.z10[idx];
    cuDoubleComplex x01 = field_in.z01[idx];
    cuDoubleComplex x11 = field_in.z11[idx];

    // Load constant Rotors
    cuDoubleComplex b00 = const_B_t[0];
    cuDoubleComplex b10 = const_B_t[1];
    cuDoubleComplex b01 = const_B_t[2];
    cuDoubleComplex b11 = const_B_t[3];

    cuDoubleComplex binv00 = const_B_t_inv[0];
    cuDoubleComplex binv10 = const_B_t_inv[1];
    cuDoubleComplex binv01 = const_B_t_inv[2];
    cuDoubleComplex binv11 = const_B_t_inv[3];

    // 2. Hardware execution of (B_t * X) * B_{-t}
    // Step A: Y = B_t * X
    cuDoubleComplex y00 = add_complex(mul_complex(b00, x00), mul_complex(b01, x10));
    cuDoubleComplex y10 = add_complex(mul_complex(b10, x00), mul_complex(b11, x10));
    cuDoubleComplex y01 = add_complex(mul_complex(b00, x01), mul_complex(b01, x11));
    cuDoubleComplex y11 = add_complex(mul_complex(b10, x01), mul_complex(b11, x11));

    // Step B: Out = Y * B_{-t}
    cuDoubleComplex out00 = add_complex(mul_complex(y00, binv00), mul_complex(y01, binv10));
    cuDoubleComplex out10 = add_complex(mul_complex(y10, binv00), mul_complex(y11, binv10));
    cuDoubleComplex out01 = add_complex(mul_complex(y00, binv01), mul_complex(y01, binv11));
    cuDoubleComplex out11 = add_complex(mul_complex(y10, binv01), mul_complex(y11, binv11));

    // 3. Store result to the new "Now" (Coalesced write)
    field_out.z00[idx] = out00;
    field_out.z10[idx] = out10;
    field_out.z01[idx] = out01;
    field_out.z11[idx] = out11;
}

// ----------------------------------------------------------------------------
// FFI Implementation for Lean 4
// ----------------------------------------------------------------------------
extern "C" {

void cuda_execute_modular_flow(uint32_t N, double t, TwistorFieldState* field_in, TwistorFieldState* field_out) {
    // 1. Calculate the continuous Lorentz boost rotor elements for rapidity t
    // Assuming B_t = cosh(t/2) * I + sinh(t/2) * Gamma_3 (simplified example for z-boost)
    double ch = cosh(t / 2.0);
    double sh = sinh(t / 2.0);

    cuDoubleComplex host_B_t[4] = {
        make_cuDoubleComplex(ch + sh, 0.0), make_cuDoubleComplex(0.0, 0.0),
        make_cuDoubleComplex(0.0, 0.0),     make_cuDoubleComplex(ch - sh, 0.0)
    };
    
    // B_{-t} = J_mod(B_t)
    cuDoubleComplex host_B_t_inv[4] = {
        make_cuDoubleComplex(ch - sh, 0.0), make_cuDoubleComplex(0.0, 0.0),
        make_cuDoubleComplex(0.0, 0.0),     make_cuDoubleComplex(ch + sh, 0.0)
    };

    // Copy to constant memory
    cudaMemcpyToSymbol(const_B_t, host_B_t, 4 * sizeof(cuDoubleComplex));
    cudaMemcpyToSymbol(const_B_t_inv, host_B_t_inv, 4 * sizeof(cuDoubleComplex));

    // 2. Allocate and transfer Device memory for SoA (In production, memory is persistently allocated!)
    TwistorField_SoA_Device d_in, d_out;
    d_in.num_twistors = N; d_out.num_twistors = N;
    
    size_t size = N * sizeof(cuDoubleComplex);
    cudaMalloc(&d_in.z00, size); cudaMalloc(&d_in.z10, size);
    cudaMalloc(&d_in.z01, size); cudaMalloc(&d_in.z11, size);
    
    cudaMalloc(&d_out.z00, size); cudaMalloc(&d_out.z10, size);
    cudaMalloc(&d_out.z01, size); cudaMalloc(&d_out.z11, size);

    // Note: We need a mapping from the separated real/imag host arrays to cuDoubleComplex.
    // For a highly optimized FFI, Lean should directly hold an array of cuDoubleComplex (FloatArray in Lean)
    // Here we assume memory mapping or simple interleaved copy for prototype.
    // ... omitting the deep copy logic here for brevity ...

    // 3. Launch the Batched Modular Flow Kernel
    int threadsPerBlock = 256;
    int blocksPerGrid = (N + threadsPerBlock - 1) / threadsPerBlock;
    
    execute_modular_flow_kernel<<<blocksPerGrid, threadsPerBlock>>>(d_in, d_out, N);
    cudaDeviceSynchronize();

    // 4. Retrieve data and free
    // ... mapping back to host arrays ...

    cudaFree(d_in.z00); cudaFree(d_in.z10); cudaFree(d_in.z01); cudaFree(d_in.z11);
    cudaFree(d_out.z00); cudaFree(d_out.z10); cudaFree(d_out.z01); cudaFree(d_out.z11);
}

} // extern "C"
