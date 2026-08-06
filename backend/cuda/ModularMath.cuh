#pragma once
#include "ZornCore.cuh"

// ============================================================================
// Modular Math ALU (Arithmetic Logic Unit for Zorn Algebra)
// ============================================================================

// FMA (Fused Multiply-Add) Complex Operations
__device__ __forceinline__ cuDoubleComplex mul_c(cuDoubleComplex a, cuDoubleComplex b) {
    return cuCmul(a, b);
}
__device__ __forceinline__ cuDoubleComplex add_c(cuDoubleComplex a, cuDoubleComplex b) {
    return cuCadd(a, b);
}
__device__ __forceinline__ cuDoubleComplex sub_c(cuDoubleComplex a, cuDoubleComplex b) {
    return cuCsub(a, b);
}

// 1. Умножение на ClPlus * ClPlus (Матрично умножение в регистрите)
__device__ __forceinline__ ClPlus mul_clplus(const ClPlus& A, const ClPlus& B) {
    ClPlus out;
    out.z00 = add_c(mul_c(A.z00, B.z00), mul_c(A.z01, B.z10));
    out.z01 = add_c(mul_c(A.z00, B.z01), mul_c(A.z01, B.z11));
    out.z10 = add_c(mul_c(A.z10, B.z00), mul_c(A.z11, B.z10));
    out.z11 = add_c(mul_c(A.z10, B.z01), mul_c(A.z11, B.z11));
    return out;
}

// 2. Инволюцията на Томита (J_mod) - Ермитово спрежение на ClPlus
__device__ __forceinline__ ClPlus J_mod(const ClPlus& X) {
    ClPlus out;
    out.z00 = cuConj(X.z00);
    out.z01 = cuConj(X.z10); // Transpose + Conjugate
    out.z10 = cuConj(X.z01);
    out.z11 = cuConj(X.z11);
    return out;
}

// 3. Модулярен Поток на Томита (B_t * X * B_{-t})
__device__ __forceinline__ ClPlus ModularFlow(const ClPlus& B_t, const ClPlus& X) {
    // Тъй като работим с KMS състояния, B_{-t} е J_mod(B_t)
    ClPlus B_t_inv = J_mod(B_t);
    return mul_clplus(mul_clplus(B_t, X), B_t_inv);
}

// 4. SplitNorm(O) - Нормата на сплит-октонион (Енергийният разрив)
// В Zorn алгебрата нормата е Детерминантата на матрицата
__device__ __forceinline__ double SplitNorm(const ZornMatrix& O) {
    // Det(Even) - Det(Odd) -> Хардуерен мапинг на квантовия разрив
    cuDoubleComplex det_even = sub_c(mul_c(O.even_part.z00, O.even_part.z11), 
                                     mul_c(O.even_part.z01, O.even_part.z10));
                                     
    cuDoubleComplex det_odd = sub_c(mul_c(O.odd_part.z00, O.odd_part.z11), 
                                    mul_c(O.odd_part.z01, O.odd_part.z10));
                                    
    return cuCreal(sub_c(det_even, det_odd));
}
