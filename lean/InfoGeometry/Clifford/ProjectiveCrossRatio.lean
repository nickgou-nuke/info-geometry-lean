/-
Copyright (c) 2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/
import InfoGeometry.Clifford.DiscreteMoebiusGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.ModularCftBridge

/-!
# InfoGeometry.Clifford.ProjectiveCrossRatio

Coordinate-free discrete Moebius projective geometry on the Cantor boundary.

## Theorem 2 (Vanishing of the Projective Curvature Tensor)

The discrete Moebius projections acting on the Cantor-Dirac modular states have
zero algebraic curvature: the cross-ratio of four points is invariant under
PGL(2,Z) transformations.
-/

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.Clifford.ProjectiveCrossRatio

open InfoGeometry.Clifford.DiscreteMoebiusGroup
open InfoGeometry.Clifford.ModularCftBridge
open Matrix

def crossRatio (P1 P2 P3 P4 : ℂ) : ℂ :=
  (P1 - P3) * (P1 - P4)⁻¹ * (P2 - P4) * (P2 - P3)⁻¹

theorem moebius_diff (M : Matrix (Fin 2) (Fin 2) ℂ) (P Q : ℂ)
    (hCPD : M 1 0 * P + M 1 1 ≠ 0) (hCQD : M 1 0 * Q + M 1 1 ≠ 0) :
    ((M 0 0 * P + M 0 1) / (M 1 0 * P + M 1 1)) -
    ((M 0 0 * Q + M 0 1) / (M 1 0 * Q + M 1 1)) =
    (Matrix.det M * (P - Q)) / ((M 1 0 * P + M 1 1) * (M 1 0 * Q + M 1 1)) := by
  calc
    ((M 0 0 * P + M 0 1) / (M 1 0 * P + M 1 1)) - ((M 0 0 * Q + M 0 1) / (M 1 0 * Q + M 1 1))
        = ((M 0 0 * P + M 0 1) * (M 1 0 * Q + M 1 1) - (M 0 0 * Q + M 0 1) * (M 1 0 * P + M 1 1))
          / ((M 1 0 * P + M 1 1) * (M 1 0 * Q + M 1 1)) := by
          field_simp [show P * M 1 0 + M 1 1 ≠ 0 from by simpa [mul_comm, add_comm] using hCPD,
    show Q * M 1 0 + M 1 1 ≠ 0 from by simpa [mul_comm, add_comm] using hCQD]
    _ = ((M 0 0 * M 1 1 - M 0 1 * M 1 0) * (P - Q)) / ((M 1 0 * P + M 1 1) * (M 1 0 * Q + M 1 1)) := by ring_nf
    _ = (Matrix.det M * (P - Q)) / ((M 1 0 * P + M 1 1) * (M 1 0 * Q + M 1 1)) := by
      simp [Matrix.det_fin_two]

theorem crossRatio_moebius_invariant (M : Matrix (Fin 2) (Fin 2) ℂ)
    (P1 P2 P3 P4 : ℂ)
    (hdet : Matrix.det M ≠ 0)
    (hden1 : M 1 0 * P1 + M 1 1 ≠ 0)
    (hden2 : M 1 0 * P2 + M 1 1 ≠ 0)
    (hden3 : M 1 0 * P3 + M 1 1 ≠ 0)
    (hden4 : M 1 0 * P4 + M 1 1 ≠ 0)
    (hdistinct : P1 ≠ P3 ∧ P1 ≠ P4 ∧ P2 ≠ P4 ∧ P2 ≠ P3) :
    crossRatio ((M 0 0 * P1 + M 0 1) / (M 1 0 * P1 + M 1 1))
      ((M 0 0 * P2 + M 0 1) / (M 1 0 * P2 + M 1 1))
      ((M 0 0 * P3 + M 0 1) / (M 1 0 * P3 + M 1 1))
      ((M 0 0 * P4 + M 0 1) / (M 1 0 * P4 + M 1 1)) =
    crossRatio P1 P2 P3 P4 := by
  unfold crossRatio
  have h13 := moebius_diff M P1 P3 hden1 hden3
  have h14 := moebius_diff M P1 P4 hden1 hden4
  have h24 := moebius_diff M P2 P4 hden2 hden4
  have h23 := moebius_diff M P2 P3 hden2 hden3
  rw [h13, h14, h24, h23]
  field_simp [show P1 * M 1 0 + M 1 1 ≠ 0 from by simpa [mul_comm, add_comm] using hden1,
    show P2 * M 1 0 + M 1 1 ≠ 0 from by simpa [mul_comm, add_comm] using hden2,
    show P3 * M 1 0 + M 1 1 ≠ 0 from by simpa [mul_comm, add_comm] using hden3,
    show P4 * M 1 0 + M 1 1 ≠ 0 from by simpa [mul_comm, add_comm] using hden4]

theorem crossRatio_T_invariant (P1 P2 P3 P4 : ℂ) :
    crossRatio (moebiusAction modularT P1) (moebiusAction modularT P2)
      (moebiusAction modularT P3) (moebiusAction modularT P4) =
    crossRatio P1 P2 P3 P4 := by
  simp [moebiusAction, moebius_T_action, modularT, crossRatio]

theorem crossRatio_S_invariant (P1 P2 P3 P4 : ℂ)
    (hden1 : P1 ≠ 0) (hden2 : P2 ≠ 0) (hden3 : P3 ≠ 0) (hden4 : P4 ≠ 0)
    (hdistinct : P1 ≠ P3 ∧ P1 ≠ P4 ∧ P2 ≠ P4 ∧ P2 ≠ P3) :
    crossRatio (moebiusAction modularS P1) (moebiusAction modularS P2)
      (moebiusAction modularS P3) (moebiusAction modularS P4) =
    crossRatio P1 P2 P3 P4 := by
  apply crossRatio_moebius_invariant modularS P1 P2 P3 P4
  · simp [modularS]
  · simpa [modularS] using hden1
  · simpa [modularS] using hden2
  · simpa [modularS] using hden3
  · simpa [modularS] using hden4
  · exact hdistinct

end InfoGeometry.Clifford.ProjectiveCrossRatio
