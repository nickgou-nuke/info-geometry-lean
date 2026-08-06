#ifndef TWISTOR_FFI_H
#define TWISTOR_FFI_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// Lean 4 represents Floats as C doubles.
// This structure maps exactly to the TwistorField_SoA layout.
typedef struct {
    uint32_t num_twistors;
    double* z00_real;
    double* z00_imag;
    double* z10_real;
    double* z10_imag;
    double* z01_real;
    double* z01_imag;
    double* z11_real;
    double* z11_imag;
} TwistorFieldState;

// The extern "C" function that Lean 4 will bind to via @[extern]
void cuda_execute_modular_flow(uint32_t N, double t, TwistorFieldState* field_in, TwistorFieldState* field_out);

#ifdef __cplusplus
}
#endif

#endif // TWISTOR_FFI_H
