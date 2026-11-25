/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralSkewIncidence
import InfoGeometry.Clifford.Soldering
import InfoGeometry.Topology.AmplituhedronGeneralTwistorExpansion

/-!
# Real epsilon incidence pairings and Plücker minors

For the repository's epsilon matrix `[[0,1],[-1,0]]`, the ordered positive–
negative incidence pairing is **minus twice** the determinant bracket.
Reversing the two graph signs changes that sign. The actual cross pairings
satisfy the three-term Plücker relation through the existing `minor2` owner.
Epsilon has zero kernel, so its only mirror-fixed incidence state is zero.
These are real algebraic statements, without a physical CPT interpretation.
-/

noncomputable section

namespace InfoGeometry.Twistor.DiracSpinorBrackets

open scoped Matrix
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralSkewIncidence
open InfoGeometry.Twistor.RealTwistorIncidence
open InfoGeometry.Amplituhedron

local notation "ε" => InfoGeometry.Clifford.Soldering.epsilon
local notation "δ" => dotProductEquiv ℝ (Fin 2)

/-- The existing real epsilon matrix is skew under transpose. -/
theorem epsilon_transpose : εᵀ = -ε := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Clifford.Soldering.epsilon, Matrix.transpose_apply]

/-- Epsilon acts by the real quarter turn `(u₀,u₁) ↦ (u₁,-u₀)`. -/
theorem epsilon_mulVec (u : Fin 2 → ℝ) : ε *ᵥ u = ![u 1, -u 0] := by
  ext i
  fin_cases i <;>
    simp [Clifford.Soldering.epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Epsilon has no nonzero kernel vector. -/
theorem epsilon_mulVec_eq_zero_iff (u : Fin 2 → ℝ) : ε *ᵥ u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h₀ := congrFun h (0 : Fin 2)
    have h₁ := congrFun h (1 : Fin 2)
    have hu₁ : u 1 = 0 := by simpa [epsilon_mulVec] using h₀
    have hu₀ : u 0 = 0 := by simpa [epsilon_mulVec] using h₁
    ext i
    fin_cases i
    · exact hu₀
    · exact hu₁
  · rintro rfl
    simp

/-- The native dual-to-vector epsilon map has the same zero-kernel test. -/
theorem epsilonSharp_eq_zero_iff (u : Fin 2 → ℝ) :
    matrixSharp ε (δ u) = 0 ↔ u = 0 := by
  rw [matrixSharp_apply, epsilon_mulVec_eq_zero_iff]

/-- With positive graph first and negative graph second, the determinant
bracket appears with coefficient `-2`. -/
theorem epsilon_cross_pairing (u v : Fin 2 → ℝ) :
    canonicalNeutralBilin
        (incidenceMap (matrixSharp ε) (δ u))
        (incidenceMap (matrixSharp (-ε)) (δ v)) =
      -2 * (u 0 * v 1 - u 1 * v 0) := by
  rw [matrix_incidence_cross_pairing ε epsilon_transpose]
  simp [Clifford.Soldering.epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- Reversing both graph signs, while keeping spinor order, gives `+2`. -/
theorem epsilon_reverse_cross_pairing (u v : Fin 2 → ℝ) :
    canonicalNeutralBilin
        (incidenceMap (matrixSharp (-ε)) (δ u))
        (incidenceMap (matrixSharp ε) (δ v)) =
      2 * (u 0 * v 1 - u 1 * v 0) := by
  simp only [canonicalNeutralBilin_apply, incidenceMap_apply, matrixSharp_apply,
    dotProductEquiv_apply_apply]
  simp [Clifford.Soldering.epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- Two columns of a native two-row matrix give its existing `minor2`. -/
theorem epsilon_cross_pairing_eq_minor {n : ℕ}
    (C : Matrix (Fin 2) (Fin n) ℝ) (a b : Fin n) :
    canonicalNeutralBilin
        (incidenceMap (matrixSharp ε) (δ (fun i => C i a)))
        (incidenceMap (matrixSharp (-ε)) (δ (fun i => C i b))) =
      -2 * minor2 C a b := by
  rw [epsilon_cross_pairing]
  rfl

/-- The actual incidence pairings inherit the three-term Plücker identity.
No division by a pairing or nonvanishing assumption is required. -/
theorem epsilon_cross_pairing_plucker {n : ℕ}
    (C : Matrix (Fin 2) (Fin n) ℝ) (a b c d : Fin n) :
    canonicalNeutralBilin
        (incidenceMap (matrixSharp ε) (δ (fun i => C i a)))
        (incidenceMap (matrixSharp (-ε)) (δ (fun i => C i c))) *
      canonicalNeutralBilin
        (incidenceMap (matrixSharp ε) (δ (fun i => C i b)))
        (incidenceMap (matrixSharp (-ε)) (δ (fun i => C i d))) =
    canonicalNeutralBilin
        (incidenceMap (matrixSharp ε) (δ (fun i => C i a)))
        (incidenceMap (matrixSharp (-ε)) (δ (fun i => C i b))) *
      canonicalNeutralBilin
        (incidenceMap (matrixSharp ε) (δ (fun i => C i c)))
        (incidenceMap (matrixSharp (-ε)) (δ (fun i => C i d))) +
    canonicalNeutralBilin
        (incidenceMap (matrixSharp ε) (δ (fun i => C i a)))
        (incidenceMap (matrixSharp (-ε)) (δ (fun i => C i d))) *
      canonicalNeutralBilin
        (incidenceMap (matrixSharp ε) (δ (fun i => C i b)))
        (incidenceMap (matrixSharp (-ε)) (δ (fun i => C i c))) := by
  simp only [epsilon_cross_pairing_eq_minor]
  rw [mul_mul_mul_comm (-2 : ℝ) (minor2 C a c) (-2) (minor2 C b d),
    mul_mul_mul_comm (-2 : ℝ) (minor2 C a b) (-2) (minor2 C c d),
    mul_mul_mul_comm (-2 : ℝ) (minor2 C a d) (-2) (minor2 C b c),
    ← mul_add, plucker_relation_general C a b c d]

/-- A positive epsilon graph state is mirror fixed exactly at zero spinor. -/
theorem epsilon_incidence_fixed_iff (u : Fin 2 → ℝ) :
    diracMirror (incidenceMap (matrixSharp ε) (δ u)) =
        incidenceMap (matrixSharp ε) (δ u) ↔ u = 0 := by
  rw [diracMirror_incidence_fixed_iff, epsilonSharp_eq_zero_iff]

/-- The fixed epsilon graph state itself is the zero phase-space vector. -/
theorem epsilon_incidence_fixed_eq_zero (u : Fin 2 → ℝ)
    (h : diracMirror (incidenceMap (matrixSharp ε) (δ u)) =
      incidenceMap (matrixSharp ε) (δ u)) :
    incidenceMap (matrixSharp ε) (δ u) = 0 := by
  have hu := (epsilon_incidence_fixed_iff u).mp h
  subst u
  simp

/-- A nonzero one-edge cross-pairing witnesses the normalization sign. -/
theorem epsilon_cross_pairing_basis :
    canonicalNeutralBilin
        (incidenceMap (matrixSharp ε) (δ ![1, 0]))
        (incidenceMap (matrixSharp (-ε)) (δ ![0, 1])) = -2 := by
  rw [epsilon_cross_pairing]
  norm_num

/-- Mirroring both endpoints changes the explicit nonzero edge value to `2`. -/
theorem epsilon_mirror_pairing_basis :
    canonicalNeutralBilin
        (diracMirror (incidenceMap (matrixSharp ε) (δ ![1, 0])))
        (diracMirror (incidenceMap (matrixSharp (-ε)) (δ ![0, 1]))) = 2 := by
  rw [diracMirror_anti_isometry, epsilon_cross_pairing_basis]
  norm_num

end InfoGeometry.Twistor.DiracSpinorBrackets
