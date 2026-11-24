/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import InfoGeometry.Krein.Metric

/-!
# Reflection pairing and real Weil--Krein evaluation blocks

The reflection law pairs eigenvalues; it does not constrain their real parts.
The real counterexample below makes this distinction explicit. In real shifted
spectral coordinates, critical reflection negates only the first coordinate.

The cross-pairing reuses
`InfoGeometry.Krein.hessian_indefinite_formCoord` on raw coordinates. These
elementary identities do not require completeness of the inner-product seed.
For a realification of complex evaluations the seed is two-dimensional, so the
full real evaluation block has dimension four, not two.

The final pullback theorem names the evaluation-surjectivity hypothesis needed
to transfer a negative block to a test space. It does not construct a Mellin
evaluation map or prove that it is surjective. Neither a Weil explicit formula
nor an RH/GRH implication is asserted here.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore

section Reflection

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- An involutive reflection reversing an endomorphism anticommutes with it. -/
theorem anticommute_of_reflection
    (J D : Module.End k V) (hJ : J * J = 1) (hD : J * D * J = -D) :
    D * J = -(J * D) := by
  calc
    D * J = (J * J) * D * J := by rw [hJ, one_mul]
    _ = J * (J * D * J) := by simp only [mul_assoc]
    _ = J * (-D) := by rw [hD]
    _ = -(J * D) := mul_neg _ _

/-- The mirror transports an eigen-equation from `w` to `-w`. -/
theorem reflection_eigen_equation
    (J D : Module.End k V) (hJ : J * J = 1) (hD : J * D * J = -D)
    {v : V} {w : k} (hv : D v = w • v) :
    D (J v) = (-w) • J v := by
  have hDJ := anticommute_of_reflection J D hJ hD
  calc
    D (J v) = (D * J) v := rfl
    _ = (-(J * D)) v := by rw [hDJ]
    _ = -(J (D v)) := rfl
    _ = (-w) • J v := by rw [hv, map_smul, neg_smul]

/-- Native Mathlib eigenvectors remain nonzero under the involutive mirror. -/
theorem reflection_hasEigenvector
    (J D : Module.End k V) (hJ : J * J = 1) (hD : J * D * J = -D)
    {v : V} {w : k} (hv : D.HasEigenvector w v) :
    D.HasEigenvector (-w) (J v) := by
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    exact reflection_eigen_equation J D hJ hD hv.apply_eq_smul
  · intro hzero
    have hJJ : J (J v) = v := by
      simpa using congrArg (fun T : Module.End k V => T v) hJ
    apply hv.2
    rw [← hJJ, hzero, map_zero]

/-- Reflection symmetry is compatible with a strictly positive real eigenvalue.
This is a counterexample to inferring critical-line support from that symmetry. -/
theorem reflection_law_allows_positive_real_eigenvalue :
    ∃ (J D : Module.End ℝ (ℝ × ℝ)) (v : ℝ × ℝ),
      J * J = 1 ∧ J * D * J = -D ∧ D.HasEigenvector 1 v := by
  let J : Module.End ℝ (ℝ × ℝ) := (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap
  let D : Module.End ℝ (ℝ × ℝ) :=
    (LinearMap.id : Module.End ℝ ℝ).prodMap (-LinearMap.id)
  refine ⟨J, D, (1, 0), ?_, ?_, ?_⟩
  · ext <;> rfl
  · ext <;> simp [J, D, Module.End.mul_apply]
  · refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      simp [D]
    · intro h
      have := congrArg Prod.fst h
      simp at this

end Reflection

/-- The critical reflection in real shifted spectral coordinates fixes exactly
the first-coordinate-zero locus. It is not simultaneous sign reversal. -/
theorem critical_reflection_fixed_iff (sigma height : ℝ) :
    ((-sigma, height) : ℝ × ℝ) = (sigma, height) ↔ sigma = 0 := by
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    dsimp at hfirst
    linarith
  · rintro rfl
    simp

/-- Simultaneous sign reversal fixes only the origin of the real spectral plane. -/
theorem spectral_negation_fixed_iff (sigma height : ℝ) :
    ((-sigma, -height) : ℝ × ℝ) = (sigma, height) ↔ sigma = 0 ∧ height = 0 := by
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    have hsecond := congrArg Prod.snd h
    dsimp at hfirst hsecond
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    simp

section CrossPairing

open InfoGeometry.Krein (hessian_indefinite_formCoord)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Each coordinate sheet is isotropic for the neutral cross-pairing. -/
theorem coordinate_sheets_isotropic (x y : E) :
    hessian_indefinite_formCoord (x, (0 : E)) (y, 0) = 0 ∧
      hessian_indefinite_formCoord ((0 : E), x) (0, y) = 0 := by
  simp [hessian_indefinite_formCoord]

/-- A diagonal evaluation has the positive doubled norm square. -/
theorem diagonal_cross_pairing (x : E) :
    hessian_indefinite_formCoord (x, x) (x, x) = 2 * ‖x‖ ^ 2 := by
  simp only [hessian_indefinite_formCoord, real_inner_self_eq_norm_sq]
  ring

/-- An antidiagonal evaluation has the negative doubled norm square. -/
theorem antidiagonal_cross_pairing (x : E) :
    hessian_indefinite_formCoord (x, -x) (x, -x) = -(2 * ‖x‖ ^ 2) := by
  simp only [hessian_indefinite_formCoord, inner_neg_right, real_inner_self_eq_norm_sq]
  ring

/-- Both strict signs occur as soon as the evaluation seed is nonzero. -/
theorem cross_pairing_has_both_signs {x : E} (hx : x ≠ 0) :
    0 < hessian_indefinite_formCoord (x, x) (x, x) ∧
      hessian_indefinite_formCoord (x, -x) (x, -x) < 0 := by
  have hnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  rw [diagonal_cross_pairing, antidiagonal_cross_pairing]
  constructor <;> linarith

/-- A bound on the remaining contributions preserves an isolated negative
direction. Applying this to an infinite zero sum needs an analytic tail bound. -/
theorem negative_pair_of_remainder_bound (x : E) (remainder : ℝ)
    (hbound : remainder < 2 * ‖x‖ ^ 2) :
    hessian_indefinite_formCoord (x, -x) (x, -x) + remainder < 0 := by
  rw [antidiagonal_cross_pairing]
  linarith only [hbound]

/-- Surjectivity onto a nontrivial real evaluation block rules out positivity
of its pulled-back cross-form. No surjectivity of Mellin evaluations is assumed
silently; it is the explicit hypothesis `hsurj`. -/
theorem not_nonneg_cross_pairing_pullback
    {T : Type*} [AddCommGroup T] [Module ℝ T] [Nontrivial E]
    (evaluation : T →ₗ[ℝ] E × E) (hsurj : Function.Surjective evaluation) :
    ¬ ∀ f : T,
      0 ≤ hessian_indefinite_formCoord (evaluation f) (evaluation f) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  obtain ⟨f, hf⟩ := hsurj (x, -x)
  intro hnonneg
  have hpos := hnonneg f
  rw [hf] at hpos
  exact (not_le_of_gt (cross_pairing_has_both_signs hx).2) hpos

end CrossPairing

end InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore
