#include "ZornFFI.h"
#include <cuda_runtime.h>
#include <iostream>

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
// The Grand Kernel: Tomita-Takesaki Modular Flow
// ---------------------------------------------------------
__global__ void execute_modular_flow_kernel(TwistorField_SoA field, int N) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;

    // 1. Зареждане на локалния Туистор X в регистрите на нишката (Coalesced Memory Access)
    cuDoubleComplex x00 = field.z00[idx];
    cuDoubleComplex x01 = field.z01[idx];
    cuDoubleComplex x10 = field.z10[idx];
    cuDoubleComplex x11 = field.z11[idx];

    // 2. Междинен резултат: Y = B_t * X
    cuDoubleComplex y00, y01, y10, y11;
    multiply_clplus(
        const_B_t[0], const_B_t[1], const_B_t[2], const_B_t[3], // B_t
        x00, x01, x10, x11,                                     // X
        y00, y01, y10, y11
    );

    // 3. Финален резултат: X' = Y * B_{-t} = B_t * X * B_{-t}
    cuDoubleComplex out00, out01, out10, out11;
    multiply_clplus(
        y00, y01, y10, y11,                                     // Y
        const_B_t_inv[0], const_B_t_inv[1], const_B_t_inv[2], const_B_t_inv[3], // B_{-t}
        out00, out01, out10, out11
    );

    // 4. Записване на новото термодинамично състояние обратно в паметта
    field.z00[idx] = out00;
    field.z01[idx] = out01;
    field.z10[idx] = out10;
    field.z11[idx] = out11;
}

// ---------------------------------------------------------
// Lean 4 FFI Входна точка
// ---------------------------------------------------------
extern "C" lean_obj_res cuda_execute_modular_flow(
    uint32_t N, double t, 
    lean_obj_arg z00_re, lean_obj_arg z00_im,
    lean_obj_arg z10_re, lean_obj_arg z10_im,
    lean_obj_arg z01_re, lean_obj_arg z01_im,
    lean_obj_arg z11_re, lean_obj_arg z11_im) 
{
    // Тук ще разопаковаме масивите (lean_float_array_data),
    // ще алокираме cudaMalloc, ще извикаме ядрото и ще върнем резултата към Lean.
    // Засега връщаме празен обект, за да може Lean да се компилира.
    return lean_io_result_mk_ok(lean_box(0)); 
}
