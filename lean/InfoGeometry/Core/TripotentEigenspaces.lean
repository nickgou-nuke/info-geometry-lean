/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentAdjoint

/-!
# Native eigenspaces of the tripotent adjoint

The five existing projector ranges are exactly the native eigenspaces of the
inner derivation. This supplies the missing converse to the owned forward
weight theorem. Multiplication and the Lie bracket add weights; a weight
outside the five labels forces the element to vanish.
-/

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem fiveGradeValue_real_injective :
    Function.Injective (fun k : FiveGrade => (fiveGradeValue k : ℝ)) := by
  intro i j hij
  cases i <;> cases j <;> first | rfl | norm_num [fiveGradeValue] at hij

/-- An eigenvector has zero component at every distinct weight. -/
theorem fiveGradeProjector_eq_zero_of_eigen_ne {t x : A} {r : ℝ}
    (ht : t * t * t = t) (hx : LieAlgebra.ad ℝ A t x = r • x)
    (k : FiveGrade) (hkr : (fiveGradeValue k : ℝ) ≠ r) :
    fiveGradeProjector t k x = 0 := by
  have hc : fiveGradeProjector t k (LieAlgebra.ad ℝ A t x) =
      LieAlgebra.ad ℝ A t (fiveGradeProjector t k x) :=
    congrArg (fun f : Module.End ℝ A => f x) (fiveGradeProjector_commute_ad ht k).eq
  rw [hx, map_smul] at hc
  have hy : LieAlgebra.ad ℝ A t (fiveGradeProjector t k x) =
      (fiveGradeValue k : ℝ) • fiveGradeProjector t k x :=
    mem_fiveGradeRange_implies_adjoint_eigen ht k ⟨x, rfl⟩
  have hs : ((fiveGradeValue k : ℝ) - r) • fiveGradeProjector t k x = 0 := by
    rw [sub_smul, ← hy, ← hc, sub_self]
  exact (smul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr hkr)

/-- The five owned ranges coincide with native eigenspaces, in both directions. -/
theorem fiveGradeRange_eq_eigenspace {t : A} (ht : t * t * t = t)
    (k : FiveGrade) :
    fiveGradeRange t k =
      (LieAlgebra.ad ℝ A t).eigenspace (fiveGradeValue k : ℝ) := by
  ext x
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · exact mem_fiveGradeRange_implies_adjoint_eigen ht k
  · intro hx
    apply (mem_fiveGradeRange_iff_projector_fixed ht k).mpr
    have hz (j : FiveGrade) (hj : j ≠ k) : fiveGradeProjector t j x = 0 :=
      fiveGradeProjector_eq_zero_of_eigen_ne ht hx j
        (fun h => hj (fiveGradeValue_real_injective h))
    have hrec := fiveGrade_recompose_decompose t x
    change fiveGradeProjector t .negTwo x + fiveGradeProjector t .negOne x +
        fiveGradeProjector t .zero x + fiveGradeProjector t .posOne x +
        fiveGradeProjector t .posTwo x = x at hrec
    cases k with
    | negTwo =>
        simpa only [hz .negOne (by decide), hz .zero (by decide),
          hz .posOne (by decide), hz .posTwo (by decide), add_zero] using hrec
    | negOne =>
        simpa only [hz .negTwo (by decide), hz .zero (by decide),
          hz .posOne (by decide), hz .posTwo (by decide), zero_add, add_zero] using hrec
    | zero =>
        simpa only [hz .negTwo (by decide), hz .negOne (by decide),
          hz .posOne (by decide), hz .posTwo (by decide), zero_add, add_zero] using hrec
    | posOne =>
        simpa only [hz .negTwo (by decide), hz .negOne (by decide),
          hz .zero (by decide), hz .posTwo (by decide), zero_add, add_zero] using hrec
    | posTwo =>
        simpa only [hz .negTwo (by decide), hz .negOne (by decide),
          hz .zero (by decide), hz .posOne (by decide), zero_add] using hrec

/-- No eigenspace at a weight outside the five labels contains a nonzero element. -/
theorem eigenspace_eq_bot_of_not_mem_fiveGradeValue {t : A} {r : ℝ}
    (ht : t * t * t = t)
    (hr : r ∉ Set.range (fun k : FiveGrade => (fiveGradeValue k : ℝ))) :
    (LieAlgebra.ad ℝ A t).eigenspace r = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx' := Module.End.mem_eigenspace_iff.mp hx
  have hz (k : FiveGrade) : fiveGradeProjector t k x = 0 :=
    fiveGradeProjector_eq_zero_of_eigen_ne ht hx' k (fun h => hr ⟨k, h⟩)
  have hrec := fiveGrade_recompose_decompose t x
  change fiveGradeProjector t .negTwo x + fiveGradeProjector t .negOne x +
      fiveGradeProjector t .zero x + fiveGradeProjector t .posOne x +
      fiveGradeProjector t .posTwo x = x at hrec
  simpa only [hz, zero_add] using hrec.symm

/-- The derivation rule adds weights for the full associative product. -/
theorem mul_mem_eigenspace_add {t x y : A} {r s : ℝ}
    (hx : x ∈ (LieAlgebra.ad ℝ A t).eigenspace r)
    (hy : y ∈ (LieAlgebra.ad ℝ A t).eigenspace s) :
    x * y ∈ (LieAlgebra.ad ℝ A t).eigenspace (r + s) := by
  apply Module.End.mem_eigenspace_iff.mpr
  exact commutatorAction_product_component
    (Module.End.mem_eigenspace_iff.mp hx) (Module.End.mem_eigenspace_iff.mp hy)

/-- The native commutator Lie bracket adds the same weights. -/
theorem lie_mem_eigenspace_add {t x y : A} {r s : ℝ}
    (hx : x ∈ (LieAlgebra.ad ℝ A t).eigenspace r)
    (hy : y ∈ (LieAlgebra.ad ℝ A t).eigenspace s) :
    ⁅x, y⁆ ∈ (LieAlgebra.ad ℝ A t).eigenspace (r + s) := by
  apply Module.End.mem_eigenspace_iff.mpr
  exact commutatorAction_bracket_component
    (Module.End.mem_eigenspace_iff.mp hx) (Module.End.mem_eigenspace_iff.mp hy)

/-- Native weight addition yields multiplication closure for the existing ranges. -/
theorem mul_mem_fiveGradeRange {t x y : A} {i j k : FiveGrade}
    (ht : t * t * t = t) (hk : fiveGradeValue i + fiveGradeValue j = fiveGradeValue k)
    (hx : x ∈ fiveGradeRange t i) (hy : y ∈ fiveGradeRange t j) :
    x * y ∈ fiveGradeRange t k := by
  rw [fiveGradeRange_eq_eigenspace ht] at hx hy ⊢
  have hsum : (fiveGradeValue i : ℝ) + (fiveGradeValue j : ℝ) =
      (fiveGradeValue k : ℝ) := by exact_mod_cast hk
  exact hsum ▸ mul_mem_eigenspace_add hx hy

theorem lie_mem_fiveGradeRange {t x y : A} {i j k : FiveGrade}
    (ht : t * t * t = t) (hk : fiveGradeValue i + fiveGradeValue j = fiveGradeValue k)
    (hx : x ∈ fiveGradeRange t i) (hy : y ∈ fiveGradeRange t j) :
    ⁅x, y⁆ ∈ fiveGradeRange t k := by
  rw [fiveGradeRange_eq_eigenspace ht] at hx hy ⊢
  have hsum : (fiveGradeValue i : ℝ) + (fiveGradeValue j : ℝ) =
      (fiveGradeValue k : ℝ) := by exact_mod_cast hk
  exact hsum ▸ lie_mem_eigenspace_add hx hy

/-- A product vanishes if the sum of its weights is outside the five-weight set. -/
theorem mul_eq_zero_of_weight_not_mem {t x y : A} {r s : ℝ}
    (ht : t * t * t = t)
    (hx : x ∈ (LieAlgebra.ad ℝ A t).eigenspace r)
    (hy : y ∈ (LieAlgebra.ad ℝ A t).eigenspace s)
    (hrs : r + s ∉ Set.range (fun k : FiveGrade => (fiveGradeValue k : ℝ))) :
    x * y = 0 := by
  have h := mul_mem_eigenspace_add hx hy
  rw [eigenspace_eq_bot_of_not_mem_fiveGradeValue ht hrs] at h
  exact (Submodule.mem_bot ℝ).mp h

theorem lie_eq_zero_of_weight_not_mem {t x y : A} {r s : ℝ}
    (ht : t * t * t = t)
    (hx : x ∈ (LieAlgebra.ad ℝ A t).eigenspace r)
    (hy : y ∈ (LieAlgebra.ad ℝ A t).eigenspace s)
    (hrs : r + s ∉ Set.range (fun k : FiveGrade => (fiveGradeValue k : ℝ))) :
    ⁅x, y⁆ = 0 := by
  have h := lie_mem_eigenspace_add hx hy
  rw [eigenspace_eq_bot_of_not_mem_fiveGradeValue ht hrs] at h
  exact (Submodule.mem_bot ℝ).mp h

end InfoGeometry.Core.TripotentAdjoint
