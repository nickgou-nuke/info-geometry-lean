/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Carrier-Free 2×2 Matrix Realization of Cl(1,1)

This file proves the requested `Cl(1,1)` sign relations using mathlib matrices
directly.  It intentionally avoids a custom `structure Mat2`; the carrier is
the native `Matrix (Fin 2) (Fin 2) R`.

## Audit Protocol Map

- **BUCKET 1: CLOSED FINITE THEOREMS**:
  - `Carrier`, `I2`, `Z2`, `E1`, `E2`.
  - `mat_ext`.
  - `E1_sq_eq_I2`, `E2_sq_eq_neg_I2`, `E1_E2_anticommute`.
- **BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES**:
  - Matrix identities are proved over an arbitrary `CommRing R`.
- **BUCKET 3: OPEN CLOSURE DEBT**:
  - None for this finite carrier-free matrix layer.
-/

namespace InfoGeometry.Canonical.Mat2

open scoped Matrix

variable {R : Type*}

/-- Native `2 × 2` matrices over `R`. -/
abbrev Carrier (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- Extensionality for native `2 × 2` matrices. -/
theorem mat_ext {A B : Carrier R}
    (h00 : A 0 0 = B 0 0)
    (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0)
    (h11 : A 1 1 = B 1 1) :
    A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

variable [CommRing R]

/-- The `2 × 2` identity matrix. -/
def I2 : Carrier R :=
  1

/-- The `2 × 2` zero matrix. -/
def Z2 : Carrier R :=
  0

/-- Time-like split generator `diag(1,-1)`. -/
def E1 : Carrier R :=
  !![(1 : R), 0; 0, -1]

/-- Space-like split generator squaring to `-1`. -/
def E2 : Carrier R :=
  !![(0 : R), 1; -1, 0]

/-- The time-like generator squares to identity. -/
theorem E1_sq_eq_I2 :
    E1 (R := R) * E1 (R := R) = I2 (R := R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, I2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The space-like generator squares to negative identity. -/
theorem E2_sq_eq_neg_I2 :
    E2 (R := R) * E2 (R := R) = -I2 (R := R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E2, I2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two generators anticommute. -/
theorem E1_E2_anticommute :
    E1 (R := R) * E2 (R := R) + E2 (R := R) * E1 (R := R) = Z2 (R := R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E1, E2, Z2]

end InfoGeometry.Canonical.Mat2
