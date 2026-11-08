/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.KleinPresentedGroup

/-!
# Cellular chain calculation for the Klein bottle polygon

The standard one-vertex CW presentation has one 0-cell, two 1-cells `a,b`,
and one 2-cell attached along `a b a⁻¹ b`. The exponent-sum vector of this
word is `(0, 2)`. The algebraic chain model below uses `∂₁ = 0` and
`∂₂(x) = (0, 2x)`. This file formalizes the chain model and its homology; it
does not construct the CW attachment.

The algebraic chain complex below is indexed by the degrees of this polygon
presentation and computes its algebraic homology. The file does not construct
the CW attachment or assert a homeomorphism from the repository's Brillouin
orbit quotient to the polygon CW realization.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinBottleCWChain

abbrev C0 := Fin 1 → ℝ
abbrev C1 := Fin 2 → ℝ
abbrev C2 := Fin 1 → ℝ
abbrev C3 := Fin 0 → ℝ

/-- The free-group exponent hom sends the two presentation generators to the
standard basis vectors of the additive exponent lattice. -/
def exponentMap :
    InfoGeometry.Canonical.KleinPresentedGroup.KleinFree →*
      Multiplicative (Fin 2 → ℤ) :=
  FreeGroup.lift fun g =>
    match g with
    | .a => Multiplicative.ofAdd ![1, 0]
    | .b => Multiplicative.ofAdd ![0, 1]

/-- Abelianized exponent sum of each generator in the owner relator. -/
def relatorExponentSum (i : Fin 2) : ℤ :=
  (Multiplicative.toAdd
    (exponentMap InfoGeometry.Canonical.KleinPresentedGroup.kleinRelator)) i

/-- The actual free-group relator in `KleinPresentedGroup` has exponent vector
`(0, 2)`. -/
theorem relator_exponent_sum : relatorExponentSum = ![0, 2] := by
  funext i
  fin_cases i <;>
    simp [relatorExponentSum, exponentMap,
      InfoGeometry.Canonical.KleinPresentedGroup.kleinRelator,
      InfoGeometry.Canonical.KleinPresentedGroup.genA,
      InfoGeometry.Canonical.KleinPresentedGroup.genB]

/-- The chain boundary from the two 1-cells to the unique vertex. -/
def boundary₁ : C1 →ₗ[ℝ] C0 := 0

/-- The algebraic boundary associated with the exponent-sum vector of the
Klein-bottle relator. The coefficient identification is proved below. -/
def boundary₂ : C2 →ₗ[ℝ] C1 where
  toFun x i := if i = 0 then 0 else 2 * x 0
  map_add' x y := by
    funext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]
      ring
  map_smul' c x := by
    funext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]
      ring

/-- Boundary coefficients are the real images of the relator exponent sums. -/
theorem boundary₂_apply_eq_relatorExponentSum (x : C2) :
    boundary₂ x = fun i => (relatorExponentSum i : ℝ) * x 0 := by
  funext i
  have hi := congrFun relator_exponent_sum i
  rw [hi]
  fin_cases i <;> simp [boundary₂]

/-- The two-dimensional model has no 3-cells. -/
def boundary₃ : C3 →ₗ[ℝ] C2 := 0

/-- The cellular differentials compose to zero. -/
theorem boundary₁_comp_boundary₂ : boundary₁.comp boundary₂ = 0 := by
  ext
  simp [boundary₁]

/-- The top two differentials also compose to zero; the degree-three carrier
is zero for this two-dimensional presentation. -/
theorem boundary₂_comp_boundary₃ : boundary₂.comp boundary₃ = 0 := by
  ext x i
  simp [boundary₃]

/-- The degree-two boundaries are cycles in degree one. -/
theorem degreeOneBoundaries_le_cycles :
    LinearMap.range boundary₂ ≤ LinearMap.ker boundary₁ := by
  rw [LinearMap.range_le_ker_iff]
  simpa [LinearMap.comp_apply] using boundary₁_comp_boundary₂

/-- The degree-two boundary, regarded as a map into the degree-one cycle
space. Its range is the boundary subspace used in first homology. -/
def boundary₂IntoCycles : C2 →ₗ[ℝ] LinearMap.ker boundary₁ where
  toFun x := ⟨boundary₂ x, degreeOneBoundaries_le_cycles ⟨x, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- The degree-three boundaries are cycles in degree two. -/
theorem degreeTwoBoundaries_le_cycles :
    LinearMap.range boundary₃ ≤ LinearMap.ker boundary₂ := by
  rw [LinearMap.range_le_ker_iff]
  simpa [LinearMap.comp_apply] using boundary₂_comp_boundary₃

theorem boundary₂_injective : Function.Injective boundary₂ := by
  intro x y h
  have h₁ := congrFun h (1 : Fin 2)
  simp [boundary₂] at h₁
  funext i
  fin_cases i
  exact h₁

theorem boundary₂_ker_eq_bot : LinearMap.ker boundary₂ = ⊥ :=
  LinearMap.ker_eq_bot.mpr boundary₂_injective

/-- Zeroth homology of the algebraic chain model. -/
abbrev H0 := C0 ⧸ LinearMap.range boundary₁

/-- First homology as cycles modulo the image of the induced boundary map. -/
abbrev H1 := LinearMap.ker boundary₁ ⧸
  LinearMap.range boundary₂IntoCycles

/-- Second homology `ker ∂₂ / range ∂₃` of the explicit truncated chain. -/
abbrev H2 := LinearMap.ker boundary₂ ⧸
  (LinearMap.range boundary₃).comap (LinearMap.ker boundary₂).subtype

theorem H0_finrank : Module.finrank ℝ H0 = 1 := by
  have hC0 : Module.finrank ℝ C0 = 1 := by simp [C0]
  have hq : Module.finrank ℝ (C0 ⧸ (⊥ : Submodule ℝ C0)) = 1 := by
    have h := Submodule.finrank_quotient_add_finrank
      (⊥ : Submodule ℝ C0)
    rw [finrank_bot] at h
    omega
  change Module.finrank ℝ (C0 ⧸ LinearMap.range boundary₁) = 1
  rw [show boundary₁ = 0 by rfl, LinearMap.range_zero]
  simpa [C0] using hq

theorem H2_finrank : Module.finrank ℝ H2 = 0 := by
  change Module.finrank ℝ
    (LinearMap.ker boundary₂ ⧸
      (LinearMap.range boundary₃).comap (LinearMap.ker boundary₂).subtype) = 0
  have hboundary : (LinearMap.range boundary₃).comap
      (⊥ : Submodule ℝ C2).subtype = ⊥ := by
    simp [boundary₃]
  rw [boundary₂_ker_eq_bot, hboundary]
  apply Module.finrank_zero_iff.mpr
  infer_instance

theorem boundary₂_range_finrank :
    Module.finrank ℝ (LinearMap.range boundary₂) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker boundary₂
  rw [boundary₂_ker_eq_bot, finrank_bot] at h
  have hC2 : Module.finrank ℝ C2 = 1 := by simp [C2]
  omega

theorem H1_finrank : Module.finrank ℝ H1 = 1 := by
  have hinj : Function.Injective boundary₂IntoCycles := by
    intro x y h
    apply boundary₂_injective
    exact congrArg Subtype.val h
  have hRange : Module.finrank ℝ (LinearMap.range boundary₂IntoCycles) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker boundary₂IntoCycles
    rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot] at h
    have hC2 : Module.finrank ℝ C2 = 1 := by simp [C2]
    omega
  have hCycles : Module.finrank ℝ (LinearMap.ker boundary₁) = 2 := by
    rw [show LinearMap.ker boundary₁ = ⊤ by simp [boundary₁]]
    simp [C1]
  have hquot := Submodule.finrank_quotient_add_finrank
    (LinearMap.range boundary₂IntoCycles)
  rw [hRange, hCycles] at hquot
  change Module.finrank ℝ
      (LinearMap.ker boundary₁ ⧸ LinearMap.range boundary₂IntoCycles) = 1
  omega

/-- The alternating sum of the cellular chain ranks is zero. -/
theorem cellular_chain_euler_characteristic :
    (Module.finrank ℝ C0 : ℤ) - Module.finrank ℝ C1 +
      Module.finrank ℝ C2 = 0 := by
  have hC0 : Module.finrank ℝ C0 = 1 := by simp [C0]
  have hC1 : Module.finrank ℝ C1 = 2 := by
    simp [C1]
  have hC2 : Module.finrank ℝ C2 = 1 := by simp [C2]
  omega

/-- The alternating homology-rank sum equals the alternating chain-rank sum. -/
theorem homology_euler_characteristic :
    (Module.finrank ℝ H0 : ℤ) - Module.finrank ℝ H1 +
      Module.finrank ℝ H2 =
    (Module.finrank ℝ C0 : ℤ) - Module.finrank ℝ C1 +
      Module.finrank ℝ C2 := by
  rw [H0_finrank, H1_finrank, H2_finrank]
  norm_num

/-- Both equal Euler sums vanish for this explicit finite chain model. -/
theorem homology_euler_characteristic_zero :
    (Module.finrank ℝ H0 : ℤ) - Module.finrank ℝ H1 +
      Module.finrank ℝ H2 = 0 := by
  rw [homology_euler_characteristic, cellular_chain_euler_characteristic]

end InfoGeometry.Topology.KleinBottleCWChain
