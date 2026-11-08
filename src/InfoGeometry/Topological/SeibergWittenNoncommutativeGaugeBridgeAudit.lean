/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Topological.SeibergWittenNoncommutativeGaugeBridge

/-!
# Audit: Раздел 143b — Калибровъчна Ковариантност на Зайберг–Витен и Спояващи Форми
Concrete `ℤ` checks for `InfoGeometry.Topological.SeibergWitten`.
-/

namespace InfoGeometry.Topological.SeibergWittenAudit

open InfoGeometry.Topological.SeibergWitten

def samplePsiInt : Mat2 ℤ := ⟨2, -1, 3, 1⟩
def sampleConnInt : Mat2 ℤ := ⟨0, 5, -5, 0⟩

theorem audit_mat2_mul_noncommutative_int :
    Mat2.mul ⟨1, 1, 0, 1⟩ ⟨1, 0, 1, 1⟩ ≠
      Mat2.mul (⟨1, 0, 1, 1⟩ : Mat2 ℤ) ⟨1, 1, 0, 1⟩ := by decide

theorem audit_soldering_form_det_and_trace_int :
    Mat2.det (Mat2.solderingForm (5 : ℤ) 2 1 3) = 5^2 - 3^2 - 2^2 + 1^2 ∧
    Mat2.det (Mat2.solderingForm (5 : ℤ) 2 1 3) = 13 ∧
    Mat2.trace (Mat2.solderingForm (5 : ℤ) 2 1 3) = 10 ∧
    Mat2.trace (Mat2.solderingForm (0 : ℤ) 2 1 3) = 0 := by decide

theorem audit_sw_quad_map_equivariant_int :
    let G := canonicalOrthogonalGaugeDataInt
    swQuadMap (Mat2.mul G.U samplePsiInt) 1 =
      Mat2.mul G.U (Mat2.mul (swQuadMap samplePsiInt 1) G.U_trans) := by decide

theorem audit_dirac_zero_deriv_covariance_int :
    let G := canonicalOrthogonalGaugeDataInt
    let d0 : ℤ → ℤ := fun _ => 0
    diracOp d0 (transformedConnection d0 sampleConnInt G) (Mat2.mul G.U samplePsiInt) =
      Mat2.mul G.U (diracOp d0 sampleConnInt samplePsiInt) := by decide

end InfoGeometry.Topological.SeibergWittenAudit
