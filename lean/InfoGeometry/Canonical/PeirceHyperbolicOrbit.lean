/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import InfoGeometry.Canonical.ReflexiveMatrixCorner
import InfoGeometry.Canonical.PeirceRotorAction
import InfoGeometry.Canonical.PeirceWeightedTrace

/-! Hyperbolic projections in the existing active-corner representation.
Polynomial identities only: no spacetime metric or thermal-state claim. -/
namespace InfoGeometry.Canonical.PeirceHyperbolicOrbit
open ReflexiveNilpotentFlows PeirceRotorAction PeirceWeightedTrace
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

def hyperbolicMatrix (u v : R) : Matrix (Fin 2) (Fin 2) R :=
  !![u*u, -(u*v); u*v, -(v*v)]

def hyperbolicPlus (u v : R) (d B : A) : A :=
  pairMatrixLinear d B (hyperbolicMatrix u v)

theorem hyperbolicPlus_expansion (u v : R) (d B : A) :
    hyperbolicPlus u v d B =
      (u*u) • (d*B) - (v*v) • (B*d) - (u*v) • (d-B) := by
  simp [hyperbolicPlus, hyperbolicMatrix, pairMatrixLinear_apply,
    pairMatrixUnit, neg_smul, smul_sub]
  abel

theorem hyperbolicMatrix_sq (u v : R) (h : u*u-v*v=1) :
    hyperbolicMatrix u v * hyperbolicMatrix u v = hyperbolicMatrix u v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (u*u)*h
  · linear_combination -(u*v)*h
  · linear_combination (u*v)*h
  · linear_combination -(v*v)*h

theorem hyperbolicMatrix_displacement (u v : R) (h : u*u-v*v=1) :
    (hyperbolicMatrix u v - !![1, 0; 0, 0]) *
      (hyperbolicMatrix u v - !![1, 0; 0, 0]) =
      -(v*v) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (u*u-1)*h
  · linear_combination -(u*v)*h
  · linear_combination (u*v)*h
  · linear_combination -(v*v)*h

variable {d B : A} (hd : d*d=0) (hB : B*B=0)
  (hr : d*B*d=d) (hs : B*d*B=B)
include hd hB hr hs

theorem hyperbolicPlus_idempotent (u v : R) (h : u*u-v*v=1) :
    IsIdempotentElem (hyperbolicPlus u v d B) := by
  change pairMatrixLinear d B _ * pairMatrixLinear d B _ = _
  rw [← pairMatrixLinear_mul hd hB hr hs, hyperbolicMatrix_sq u v h]
  rfl

theorem hyperbolicPlus_displacement (u v : R) (h : u*u-v*v=1) :
    (hyperbolicPlus u v d B-d*B)*(hyperbolicPlus u v d B-d*B) =
      -(v*v) • support d B := by
  have hp : pairMatrixLinear d B (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) R) = d*B := by
    simp [pairMatrixLinear_apply, pairMatrixUnit]
  rw [hyperbolicPlus, ← hp, ← map_sub, ← pairMatrixLinear_mul hd hB hr hs,
    hyperbolicMatrix_displacement u v h, map_smul, pairMatrixLinear_one]

/-- Supported boost sandwich. The factors are inverse only after normalization;
no inverse or ambient-unit assertion is made for arbitrary parameters. -/
theorem hyperbolicPlus_boost_sandwich (u v : R) :
    (u • support d B + v • (d+B)) * (d*B) *
      (u • support d B - v • (d+B)) = hyperbolicPlus u v d B := by
  have hb (a b : R) : pairMatrixLinear d B !![a, b; b, a] =
      a • support d B + b • (d+B) := by
    simp [pairMatrixLinear_apply, pairMatrixUnit, support, smul_add]; abel
  have hp : pairMatrixLinear d B (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) R) = d*B := by
    simp [pairMatrixLinear_apply, pairMatrixUnit]
  rw [← hb u v, ← hp, sub_eq_add_neg, ← neg_smul, ← hb u (-v),
    ← pairMatrixLinear_mul hd hB hr hs, ← pairMatrixLinear_mul hd hB hr hs]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end InfoGeometry.Canonical.PeirceHyperbolicOrbit
