
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Topology.AmplituhedronGeneralTwistorExpansion
import InfoGeometry.Topology.PlabicBoundaryMeasurement
import Mathlib.Tactic

open Matrix
open scoped BigOperators
open InfoGeometry.Amplituhedron
open PlabicBoundaryMeasurement

/-!
# Finite twistor-bracket identities for a `2 × 4` matrix family

For the map `C ↦ C Z`, this module proves determinant factorization formulas
and resulting signs of six brackets, assuming total positivity of the six
ordered minors of `C` and positive determinant of `Z`.  It does not define the
full scattering amplituhedron, a plabic graph measurement, a canonical form,
or locality/unitarity statements.
-/

namespace AmplituhedronTwistorProjection

variable {R : Type*} [CommRing R]

theorem twistorBracket_skew (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) (a b : Fin 4) :
    twistorBracket Y Z b a = - twistorBracket Y Z a b := by
  dsimp [twistorBracket, det4]
  simp
  ring

theorem twistorBracket_01 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 0 1 = minor2 C 2 3 * det4 Z := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorProj_fin4_apply]
  ring

theorem twistorBracket_02 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 0 2 = - (minor2 C 1 3 * det4 Z) := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorProj_fin4_apply]
  ring

theorem twistorBracket_03 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 0 3 = minor2 C 1 2 * det4 Z := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorProj_fin4_apply]
  ring

theorem twistorBracket_12 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 1 2 = minor2 C 0 3 * det4 Z := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorProj_fin4_apply]
  ring

theorem twistorBracket_13 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 1 3 = - (minor2 C 0 2 * det4 Z) := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorProj_fin4_apply]
  ring

theorem twistorBracket_23 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 2 3 = minor2 C 0 1 * det4 Z := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorProj_fin4_apply]
  ring

theorem twistorBracket_boundary_01_pos {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    0 < twistorBracket (twistorProj C Z) Z 0 1 := by
  rw [twistorBracket_01]
  exact mul_pos hC.2.2.2.2.2 hZ

theorem twistorBracket_boundary_12_pos {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    0 < twistorBracket (twistorProj C Z) Z 1 2 := by
  rw [twistorBracket_12]
  exact mul_pos hC.2.2.1 hZ

theorem twistorBracket_boundary_23_pos {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    0 < twistorBracket (twistorProj C Z) Z 2 3 := by
  rw [twistorBracket_23]
  exact mul_pos hC.1 hZ

theorem twistorBracket_boundary_03_pos {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    0 < twistorBracket (twistorProj C Z) Z 0 3 := by
  rw [twistorBracket_03]
  exact mul_pos hC.2.2.2.1 hZ

/-- The four cyclic adjacent brackets are positive under the stated matrix
    hypotheses.  This is a sign lemma, without a claim that these inequalities
    characterize a physical amplituhedron boundary. -/
theorem amplituhedron_boundary_facets_pos
    {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    0 < twistorBracket (twistorProj C Z) Z 0 1 ∧
    0 < twistorBracket (twistorProj C Z) Z 1 2 ∧
    0 < twistorBracket (twistorProj C Z) Z 2 3 ∧
    0 < twistorBracket (twistorProj C Z) Z 0 3 :=
  ⟨twistorBracket_boundary_01_pos hC hZ,
   twistorBracket_boundary_12_pos hC hZ,
   twistorBracket_boundary_23_pos hC hZ,
   twistorBracket_boundary_03_pos hC hZ⟩

theorem twistorBracket_chord_02_neg
    {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    twistorBracket (twistorProj C Z) Z 0 2 < 0 := by
  rw [twistorBracket_02]
  have : 0 < minor2 C 1 3 * det4 Z := mul_pos hC.2.2.2.2.1 hZ
  linarith

theorem twistorBracket_chord_13_neg
    {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    twistorBracket (twistorProj C Z) Z 1 3 < 0 := by
  rw [twistorBracket_13]
  have : 0 < minor2 C 0 2 * det4 Z := mul_pos hC.2.1 hZ
  linarith

/-- Positive parameters in the explicit matrix family give the four cyclic
    adjacent bracket inequalities after projection by an oriented `4 × 4`
    matrix. -/
theorem twistor_bracket_signs_from_positive_parameters
    {t₁ t₂ t₃ t₄ : ℝ} (h1 : 0 < t₁) (h2 : 0 < t₂) (h3 : 0 < t₃) (h4 : 0 < t₄)
    {Z : Matrix (Fin 4) (Fin 4) ℝ} (hZ : 0 < det4 Z) :
    let C := boundaryMeasurementMatrix t₁ t₂ t₃ t₄
    0 < twistorBracket (twistorProj C Z) Z 0 1 ∧
    0 < twistorBracket (twistorProj C Z) Z 1 2 ∧
    0 < twistorBracket (twistorProj C Z) Z 2 3 ∧
    0 < twistorBracket (twistorProj C Z) Z 0 3 :=
  amplituhedron_boundary_facets_pos (PlabicBoundaryMeasurement.boundaryMeasurement_totally_positive h1 h2 h3 h4) hZ

end AmplituhedronTwistorProjection
