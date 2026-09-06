import proofs.TopologicalMetasurfaceSupercurrent
import proofs.PrimonCuntzTower

/-!
# Cuntz-to-`p6m` wallpaper interface

Finite Lean bridge for the proposed interface
`O_p -> p6m` at the photonic metasurface.

* prime sectors `p = 2, 3, 5` have arities `2, 3, 5`;
* toy Cuntz projector weights sum to the sector arity;
* the `p = 3` sector has three color slots;
* the `p = 5` sector is arithmetically frustrated against sixfold symmetry;
* the macroscopic `p6m` count is still `active O(5,5) + 1`;
* Wilson/AB swirl count remains `3`.
-/

noncomputable section

namespace CuntzP6MWallpaperBoundary

/-- The three primon sectors used by the finite resolution toy. -/
inductive PrimeSector where
  | p2
  | p3
  | p5
  deriving DecidableEq, Repr

/-- Arity of the finite Cuntz sector. -/
def sectorArity : PrimeSector → ℕ
  | .p2 => 2
  | .p3 => 3
  | .p5 => 5

@[simp] theorem sectorArity_p2 : sectorArity PrimeSector.p2 = 2 := rfl
@[simp] theorem sectorArity_p3 : sectorArity PrimeSector.p3 = 3 := rfl
@[simp] theorem sectorArity_p5 : sectorArity PrimeSector.p5 = 5 := rfl

/-- Unit toy projector weight.  Summing the weights models Cuntz completeness. -/
def projectorWeight (_s : PrimeSector) (_i : ℕ) : ℕ := 1

/-- Finite Cuntz completeness toy: `p` unit projectors sum to `p`. -/
theorem toy_cuntz_projector_completeness (s : PrimeSector) :
    ((List.range (sectorArity s)).map (projectorWeight s)).sum = sectorArity s := by
  cases s <;> rfl

/-- The `p = 3` sector has exactly the three color-mask slots. -/
theorem p3_color_mask_slot_count :
    (List.range (sectorArity PrimeSector.p3)).length = 3 := by
  rfl

/-- The `p = 5` sector is arithmetically distinct from sixfold symmetry. -/
theorem p5_sixfold_frustration : sectorArity PrimeSector.p5 ≠ 6 := by
  decide

/-- Toy lithographic resolution scale: wavelength divided by refractive index. -/
def lithographicFeatureSize (lam n : ℝ) : ℝ := lam / n

@[simp] theorem lithographicFeatureSize_eq (lam n : ℝ) :
    lithographicFeatureSize lam n = lam / n := rfl

/-- Toy holonomy sum: unit micro-swirls reconstruct the sector arity. -/
def holonomyWeight (_s : PrimeSector) (_i : ℕ) : ℕ := 1

theorem localized_holonomy_sum (s : PrimeSector) :
    ((List.range (sectorArity s)).map (holonomyWeight s)).sum = sectorArity s := by
  cases s <;> rfl

/-- Finite kernel for the Cuntz/`p6m` compatibility bookkeeping. -/
theorem finite_cuntz_p6m_boundary_kernel :
    sectorArity PrimeSector.p2 = 2 ∧
    sectorArity PrimeSector.p3 = 3 ∧
    sectorArity PrimeSector.p5 = 5 ∧
    (List.range (sectorArity PrimeSector.p3)).length = 3 ∧
    sectorArity PrimeSector.p5 ≠ 6 ∧
    ((List.range (sectorArity PrimeSector.p3)).map (projectorWeight PrimeSector.p3)).sum = 3 ∧
    TopologicalMetasurfaceSupercurrent.quantizedSwirlCount = 3 ∧
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m =
        O55GradedGeneratorBasis.activeGradedGeneratorCount + 1 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact p3_color_mask_slot_count
  constructor
  · exact p5_sixfold_frustration
  constructor
  · simpa using toy_cuntz_projector_completeness PrimeSector.p3
  constructor
  · exact TopologicalMetasurfaceSupercurrent.quantized_swirl_count_eq_three
  · exact WallpaperO55FrozenSelectionBridge.p6m_psa_count_matches_active_o55_plus_base

/-- Capstone: finite Cuntz-to-wallpaper bookkeeping compiles. -/
theorem cuntz_p6m_wallpaper_boundary_synthesis
    (lam n : ℝ) :
    sectorArity PrimeSector.p2 = 2 ∧
    sectorArity PrimeSector.p3 = 3 ∧
    sectorArity PrimeSector.p5 = 5 ∧
    (∀ s : PrimeSector,
      ((List.range (sectorArity s)).map (projectorWeight s)).sum = sectorArity s) ∧
    (List.range (sectorArity PrimeSector.p3)).length = 3 ∧
    sectorArity PrimeSector.p5 ≠ 6 ∧
    lithographicFeatureSize lam n = lam / n ∧
    ((List.range (sectorArity PrimeSector.p3)).map (holonomyWeight PrimeSector.p3)).sum = 3 ∧
    TopologicalMetasurfaceSupercurrent.quantizedSwirlCount = 3 := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact toy_cuntz_projector_completeness
  constructor
  · exact p3_color_mask_slot_count
  constructor
  · exact p5_sixfold_frustration
  constructor
  · exact lithographicFeatureSize_eq lam n
  constructor
  · simpa using localized_holonomy_sum PrimeSector.p3
  · exact TopologicalMetasurfaceSupercurrent.quantized_swirl_count_eq_three

end CuntzP6MWallpaperBoundary

end noncomputable section
