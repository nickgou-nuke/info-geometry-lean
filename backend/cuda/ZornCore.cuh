#pragma once
#include <cuComplex.h>

// ============================================================================
// The Zorn Split-Octonion Hardware Algebra (8D)
// ============================================================================

// Четният сектор Cℓ+(1,3) изоморфен на M_2(C)
struct __device__ __host__ ClPlus {
    cuDoubleComplex z00;
    cuDoubleComplex z01;
    cuDoubleComplex z10;
    cuDoubleComplex z11;
};

// Нечетният сектор Cℓ-(1,3) (Физически вектори)
struct __device__ __host__ ClMinus {
    cuDoubleComplex z00;
    cuDoubleComplex z01;
    cuDoubleComplex z10;
    cuDoubleComplex z11;
};

// Пълният 8-мерен Zorn Сплит-Октонион (Квантовото състояние на Вселената)
// Съдържа скалари, вектори, бивектори, тривектори и псевдоскалари
struct __device__ __host__ ZornMatrix {
    ClPlus even_part;   // Spin(1,3) ротори и електромагнитно поле
    ClMinus odd_part;   // 4-вектори на енергия/импулс и пространство/време
};
