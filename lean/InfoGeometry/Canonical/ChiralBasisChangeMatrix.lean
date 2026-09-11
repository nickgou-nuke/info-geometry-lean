import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Chiral basis change matrix

The rational change of coordinates between the chiral Peirce--Witt basis
`(n₊, σᵢ₊, σⱼ₊, σₖ₊, n₋, σᵢ₋, σⱼ₋, σₖ₋)` and the native split-octonion
basis `(1, ℓ, i, iℓ, j, jℓ, k, kℓ)`.

This file stores the explicit forward and inverse matrices and certifies that
they are mutual inverses.
-/

def chiralToStandard : Matrix (Fin 8) (Fin 8) ℚ :=
  !![
    1 / 2,  0,      0,     0,     1 / 2,  0,     0,     0;
    1 / 2,  0,      0,     0,    -1 / 2,  0,     0,     0;
    0,     -1 / 2,  0,     0,     0,     1 / 2,  0,     0;
    0,      1 / 2,  0,     0,     0,     1 / 2,  0,     0;
    0,      0,     -1 / 2,  0,     0,     0,     1 / 2,  0;
    0,      0,      1 / 2,  0,     0,     0,     1 / 2,  0;
    0,      0,      0,    -1 / 2,  0,     0,     0,     1 / 2;
    0,      0,      0,     1 / 2,  0,     0,     0,     1 / 2
  ]

def standardToChiral : Matrix (Fin 8) (Fin 8) ℚ :=
  !![
    1,  1,  0,  0,  0,  0,  0,  0;
    0,  0, -1,  1,  0,  0,  0,  0;
    0,  0,  0,  0, -1,  1,  0,  0;
    0,  0,  0,  0,  0,  0, -1,  1;
    1, -1,  0,  0,  0,  0,  0,  0;
    0,  0,  1,  1,  0,  0,  0,  0;
    0,  0,  0,  0,  1,  1,  0,  0;
    0,  0,  0,  0,  0,  0,  1,  1
  ]

theorem chiralToStandard_mul_standardToChiral :
    chiralToStandard * standardToChiral = (1 : Matrix (Fin 8) (Fin 8) ℚ) := by
  native_decide

theorem standardToChiral_mul_chiralToStandard :
    standardToChiral * chiralToStandard = (1 : Matrix (Fin 8) (Fin 8) ℚ) := by
  native_decide

end InfoGeometry.Canonical
