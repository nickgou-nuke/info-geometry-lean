/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Epistemology.RiemannianSubmersion
import InfoGeometry.Export.LeanJuliaVerifiedInterop
import InfoGeometry.Canonical.NaturalGradientSubmersionFlow

/-!
# Dimension and cost theorems for submersion splits

For a `SubmersionSplit V` with projectors `projH`, `projV` we show that the ranges are
complementary submodules, so `finrank V = finrank (range projH) + finrank (range projV)`.
The cubic cost model `cubicCostModel d = d ^ 3` is then evaluated on these *actual* finranks:
restricting to the horizontal range never costs more, costs strictly less when both
ranges are nontrivial, and the excess is the exact binomial remainder.
-/

namespace InfoGeometry.Epistemology.SubmersionSplitFinrank

open InfoGeometry.Epistemology.RiemannianSubmersion
open InfoGeometry.Export.LeanJuliaVerifiedInterop
open InfoGeometry.Canonical.NaturalGradientSubmersionFlow
open InfoGeometry.Canonical.SuperGrassmannianManifold

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The vertical range is exactly the kernel of the horizontal projector. -/
theorem range_projV_eq_ker_projH (S : SubmersionSplit V) :
    LinearMap.range S.projV = LinearMap.ker S.projH := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact S.orthoHV y
  · intro hx
    exact ⟨x, vertical_of_horizontal_zero S x hx⟩

/-- The horizontal range is exactly the kernel of the vertical projector. -/
theorem range_projH_eq_ker_projV (S : SubmersionSplit V) :
    LinearMap.range S.projH = LinearMap.ker S.projV := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact S.orthoVH y
  · intro hx
    exact ⟨x, horizontal_of_vertical_zero S x hx⟩

/-- A vector in the horizontal range is fixed by `projH`. -/
theorem projH_of_mem_range (S : SubmersionSplit V) {x : V}
    (hx : x ∈ LinearMap.range S.projH) : S.projH x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact S.idemH y

/-- The horizontal and vertical ranges are complementary submodules. -/
theorem isCompl_range_projH_range_projV (S : SubmersionSplit V) :
    IsCompl (LinearMap.range S.projH) (LinearMap.range S.projV) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hH hV
    rw [range_projV_eq_ker_projH, LinearMap.mem_ker] at hV
    rw [← projH_of_mem_range S hH, hV]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [← S.sum_id x]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x)

/-- Dimension split: `finrank V = finrank (range projH) + finrank (range projV)`. -/
theorem finrank_split (S : SubmersionSplit V) [FiniteDimensional ℝ V] :
    Module.finrank ℝ V =
      Module.finrank ℝ (LinearMap.range S.projH) + Module.finrank ℝ (LinearMap.range S.projV) :=
  (Submodule.finrank_add_eq_of_isCompl (isCompl_range_projH_range_projV S)).symm

/-- The horizontal range has dimension at most `finrank V`. -/
theorem finrank_range_projH_le (S : SubmersionSplit V) [FiniteDimensional ℝ V] :
    Module.finrank ℝ (LinearMap.range S.projH) ≤ Module.finrank ℝ V := by
  rw [finrank_split S]
  exact Nat.le_add_right _ _

/-- Restricting the cubic cost to the horizontal range never increases it. -/
theorem cost_horizontal_le (S : SubmersionSplit V) [FiniteDimensional ℝ V] :
    cubicCostModel (Module.finrank ℝ (LinearMap.range S.projH)) ≤
      cubicCostModel (Module.finrank ℝ V) :=
  cubicCostModel_mono (finrank_range_projH_le S)

/-- A nontrivial submodule of a finite-dimensional space has positive finrank. -/
theorem finrank_pos_of_ne_bot [FiniteDimensional ℝ V] {p : Submodule ℝ V} (hp : p ≠ ⊥) :
    0 < Module.finrank ℝ p :=
  Nat.pos_of_ne_zero fun h => hp (Submodule.finrank_eq_zero.mp h)

/-- With both ranges nontrivial, the horizontal cost is strictly smaller. -/
theorem cost_horizontal_lt (S : SubmersionSplit V) [FiniteDimensional ℝ V]
    (hH : LinearMap.range S.projH ≠ ⊥) (hV : LinearMap.range S.projV ≠ ⊥) :
    cubicCostModel (Module.finrank ℝ (LinearMap.range S.projH)) <
      cubicCostModel (Module.finrank ℝ V) := by
  rw [finrank_split S]
  exact cubicCostModel_strict_add _ _ (finrank_pos_of_ne_bot hH) (finrank_pos_of_ne_bot hV)

/-- Exact binomial excess of the full cost over the horizontal cost, in actual finranks. -/
theorem cost_binomial_excess (S : SubmersionSplit V) [FiniteDimensional ℝ V] :
    cubicCostModel (Module.finrank ℝ V) =
      cubicCostModel (Module.finrank ℝ (LinearMap.range S.projH)) +
        3 * Module.finrank ℝ (LinearMap.range S.projH) ^ 2 *
          Module.finrank ℝ (LinearMap.range S.projV) +
        3 * Module.finrank ℝ (LinearMap.range S.projH) *
          Module.finrank ℝ (LinearMap.range S.projV) ^ 2 +
        Module.finrank ℝ (LinearMap.range S.projV) ^ 3 := by
  rw [finrank_split S, ← cubicCostModel_add_expansion]
  simp only [add_assoc]

/-- Para-complex specialization: `finrank V = finrank (range P⁺) + finrank (range P⁻)`. -/
theorem finrank_paraComplex_split [FiniteDimensional ℝ V] (K : V →ₗ[ℝ] V)
    (hK : ParaComplexStructure K) :
    Module.finrank ℝ V =
      Module.finrank ℝ (LinearMap.range (paraProjectorPlus K)) +
        Module.finrank ℝ (LinearMap.range (paraProjectorMinus K)) :=
  finrank_split (paraComplexSubmersionSplit K hK)

/-! ### Witness: the coordinate swap on `Fin 2 → ℝ` -/

/-- The coordinate swap `v ↦ v ∘ swap 0 1` on `Fin 2 → ℝ`. -/
noncomputable def swapK : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearMap.funLeft ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

/-- The coordinate swap is a para-complex structure. -/
theorem swapK_paraComplex : ParaComplexStructure swapK :=
  ⟨fun v => by
    ext i
    simp [swapK, LinearMap.funLeft_apply]⟩

/-- `P⁺` sends the basis vector `e₀` to `(1/2, 1/2)`; its `0`-coordinate is `1/2`. -/
theorem swapK_plus_e0 :
    paraProjectorPlus swapK (Pi.single 0 1) 0 = 1 / 2 := by
  simp [paraProjectorPlus, swapK, LinearMap.funLeft_apply]

/-- `P⁻` sends the basis vector `e₀` to `(1/2, -1/2)`; its `0`-coordinate is `1/2`. -/
theorem swapK_minus_e0 :
    paraProjectorMinus swapK (Pi.single 0 1) 0 = 1 / 2 := by
  simp [paraProjectorMinus, swapK, LinearMap.funLeft_apply]

/-- A linear map whose value at `e₀` has nonzero `0`-coordinate has nontrivial range. -/
theorem range_ne_bot_of_coord (f : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (hf : f (Pi.single 0 1) 0 = 1 / 2) : LinearMap.range f ≠ ⊥ := by
  intro h
  have hmem := LinearMap.mem_range_self f (Pi.single 0 1)
  rw [h, Submodule.mem_bot] at hmem
  rw [hmem] at hf
  norm_num at hf

/-- The horizontal range of the swap split is nontrivial. -/
theorem swap_range_plus_ne_bot : LinearMap.range (paraProjectorPlus swapK) ≠ ⊥ :=
  range_ne_bot_of_coord _ swapK_plus_e0

/-- The vertical range of the swap split is nontrivial. -/
theorem swap_range_minus_ne_bot : LinearMap.range (paraProjectorMinus swapK) ≠ ⊥ :=
  range_ne_bot_of_coord _ swapK_minus_e0

/-- Strict horizontal cost saving holds for the swap split on `Fin 2 → ℝ`. -/
theorem swap_cost_horizontal_lt :
    cubicCostModel (Module.finrank ℝ (LinearMap.range (paraProjectorPlus swapK))) <
      cubicCostModel (Module.finrank ℝ (Fin 2 → ℝ)) :=
  cost_horizontal_lt (paraComplexSubmersionSplit swapK swapK_paraComplex)
    swap_range_plus_ne_bot swap_range_minus_ne_bot

/-- The dimensions of `P⁺`'s range and `P⁻`'s range for the swap add up to `2`. -/
theorem swap_finrank_sum :
    Module.finrank ℝ (LinearMap.range (paraProjectorPlus swapK)) +
      Module.finrank ℝ (LinearMap.range (paraProjectorMinus swapK)) = 2 := by
  rw [← finrank_paraComplex_split swapK swapK_paraComplex, Module.finrank_fin_fun]

/-- Each range of the swap split has dimension exactly one. -/
theorem swap_finrank_plus_eq_one :
    Module.finrank ℝ (LinearMap.range (paraProjectorPlus swapK)) = 1 := by
  have hp := finrank_pos_of_ne_bot swap_range_plus_ne_bot
  have hm := finrank_pos_of_ne_bot swap_range_minus_ne_bot
  have hs := swap_finrank_sum
  omega

/-- Concrete strict cost saving: `cubicCostModel 1 < cubicCostModel 2`. -/
theorem swap_cost_one_lt_two : cubicCostModel 1 < cubicCostModel 2 := by
  have h := swap_cost_horizontal_lt
  rwa [swap_finrank_plus_eq_one, Module.finrank_fin_fun] at h

end InfoGeometry.Epistemology.SubmersionSplitFinrank
