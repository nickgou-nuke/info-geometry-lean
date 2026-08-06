#pragma once
#include <lean/lean.h>
#include <stdint.h>
#include <cuComplex.h>

#ifdef __cplusplus
extern "C" {
#endif

// Хардуерно представяне на Туисторното поле (SoA)
struct TwistorField_SoA {
    int num_twistors;
    cuDoubleComplex* z00; 
    cuDoubleComplex* z10;
    cuDoubleComplex* z01;
    cuDoubleComplex* z11;
};

// Главната FFI функция, която Lean 4 ще извика
// Използваме b_obj_arg за масивите, за да не пипаме reference counter-а на Lean
lean_obj_res cuda_execute_modular_flow(uint32_t N, double t, 
                                       lean_obj_arg z00_re, lean_obj_arg z00_im,
                                       lean_obj_arg z10_re, lean_obj_arg z10_im,
                                       lean_obj_arg z01_re, lean_obj_arg z01_im,
                                       lean_obj_arg z11_re, lean_obj_arg z11_im);

#ifdef __cplusplus
}
#endif
