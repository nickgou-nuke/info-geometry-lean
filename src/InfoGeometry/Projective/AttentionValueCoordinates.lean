/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic

/-!
# Homogeneous coordinates for attention-value readout

The carrier is `Option D → ℝ`: `none` is mass, `some d` is a value coordinate.
The decoder is a native linear map. Projective equality uses Mathlib's actual
`Projectivization`, not merely an unbundled ratio identity. Dehomogenization is
total as a Lean function, but its geometric chart requires nonzero mass.

This is a value-space construction, not a replacement for the existing
positive-reference Gibbs-ray owner or deterministic routing representation.
No claim that the exponential map on logits is projective-linear is made.
-/

noncomputable section

namespace InfoGeometry.Projective.AttentionValueCoordinates

open scoped BigOperators

variable {J D : Type*}

/-- The standard affine chart representative `(1,v)`. -/
def affineLift (v : D → ℝ) : Option D → ℝ
  | none => 1
  | some d => v d

@[simp] theorem affineLift_none (v : D → ℝ) : affineLift v none = 1 := rfl
@[simp] theorem affineLift_some (v : D → ℝ) (d : D) :
    affineLift v (some d) = v d := rfl

theorem affineLift_ne_zero (v : D → ℝ) : affineLift v ≠ 0 := by
  intro h
  have hn := congrFun h none
  simp at hn

/-- One linear map records both total mass and the value readout. -/
def homogeneousDecoder [Fintype J] (V : J → D → ℝ) :
    (J → ℝ) →ₗ[ℝ] (Option D → ℝ) where
  toFun p := ∑ j, p j • affineLift (V j)
  map_add' p q := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c p := by simp [mul_smul, Finset.smul_sum]

@[simp] theorem homogeneousDecoder_none [Fintype J]
    (V : J → D → ℝ) (p : J → ℝ) :
    homogeneousDecoder V p none = ∑ j, p j := by
  simp [homogeneousDecoder]

@[simp] theorem homogeneousDecoder_some [Fintype J]
    (V : J → D → ℝ) (p : J → ℝ) (d : D) :
    homogeneousDecoder V p (some d) = (∑ j, p j • V j) d := by
  simp [homogeneousDecoder]

/-- Equality of homogeneous readouts is exactly equality of mass and output. -/
theorem homogeneousDecoder_eq_iff [Fintype J]
    (V : J → D → ℝ) (p q : J → ℝ) :
    homogeneousDecoder V p = homogeneousDecoder V q ↔
      (∑ j, p j) = (∑ j, q j) ∧
      (∑ j, p j • V j) = (∑ j, q j • V j) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using congrFun h none
    · funext d
      simpa using congrFun h (some d)
  · rintro ⟨hm, hv⟩
    funext od
    cases od with
    | none => simpa using hm
    | some d => simpa using congrFun hv d

/-- The decoder kernel is the space of zero-mass, zero-readout perturbations. -/
theorem mem_ker_homogeneousDecoder_iff [Fintype J]
    (V : J → D → ℝ) (δ : J → ℝ) :
    δ ∈ (homogeneousDecoder V).ker ↔
      (∑ j, δ j) = 0 ∧ (∑ j, δ j • V j) = 0 := by
  rw [LinearMap.mem_ker, ← map_zero (homogeneousDecoder V), homogeneousDecoder_eq_iff]
  simp

/-- The standard chart formula; geometric use is restricted to `x none ≠ 0`. -/
def dehomogenize (x : Option D → ℝ) : D → ℝ :=
  fun d => x (some d) / x none

theorem dehomogenize_smul (c : ℝ) (hc : c ≠ 0) (x : Option D → ℝ) :
    dehomogenize (c • x) = dehomogenize x := by
  funext d
  simp only [dehomogenize, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

/-- Normalizing before decoding equals dehomogenizing after linear decoding. -/
theorem dehomogenize_homogeneousDecoder [Fintype J]
    (V : J → D → ℝ) (w : J → ℝ) :
    dehomogenize (homogeneousDecoder V w) =
      ∑ j, (w j / (∑ k, w k)) • V j := by
  funext d
  simp only [dehomogenize, homogeneousDecoder_some, homogeneousDecoder_none,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem homogeneousDecoder_ne_zero [Fintype J]
    (V : J → D → ℝ) (w : J → ℝ) (hmass : (∑ j, w j) ≠ 0) :
    homogeneousDecoder V w ≠ 0 := by
  intro h
  apply hmass
  simpa using congrFun h none

/-- The homogeneous output is total mass times its normalized chart representative. -/
theorem homogeneousDecoder_eq_mass_smul [Fintype J]
    (V : J → D → ℝ) (w : J → ℝ) (hmass : (∑ j, w j) ≠ 0) :
    homogeneousDecoder V w =
      (∑ j, w j) • affineLift (dehomogenize (homogeneousDecoder V w)) := by
  funext od
  cases od with
  | none => simp
  | some d =>
      simp only [Pi.smul_apply, affineLift_some, smul_eq_mul, dehomogenize,
        homogeneousDecoder_none]
      field_simp [hmass]

/-- Equality in native real projective space, with both nonzero obligations proved. -/
theorem projective_normalization [Fintype J]
    (V : J → D → ℝ) (w : J → ℝ) (hmass : (∑ j, w j) ≠ 0) :
    Projectivization.mk ℝ (homogeneousDecoder V w)
        (homogeneousDecoder_ne_zero V w hmass) =
      Projectivization.mk ℝ
        (affineLift (dehomogenize (homogeneousDecoder V w))) (affineLift_ne_zero _) := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  exact ⟨∑ j, w j, (homogeneousDecoder_eq_mass_smul V w hmass).symm⟩

/-- Native affine independence is linear independence of the homogeneous lifts. -/
theorem affineIndependent_iff_linearIndependent_lift (V : J → D → ℝ) :
    AffineIndependent ℝ V ↔ LinearIndependent ℝ (fun j => affineLift (V j)) := by
  classical
  rw [affineIndependent_iff, linearIndependent_iff']
  constructor
  · intro ha s w hw
    have hm : ∑ j ∈ s, w j = 0 := by
      simpa using congrFun hw none
    have hv : ∑ j ∈ s, w j • V j = 0 := by
      funext d
      simpa using congrFun hw (some d)
    exact ha s w hm hv
  · intro hl s w hm hv
    apply hl s w
    funext od
    cases od with
    | none => simpa using hm
    | some d => simpa using congrFun hv d

/-- The dimension bound for an affinely independent value family. -/
theorem affineIndependent_card_le [Fintype J] [Fintype D]
    (V : J → D → ℝ) (hV : AffineIndependent ℝ V) :
    Fintype.card J ≤ Fintype.card D + 1 := by
  have h := ((affineIndependent_iff_linearIndependent_lift V).mp hV).fintype_card_le_finrank
  simpa [Module.finrank_pi] using h

/-- Equal mass and equal value readout determine coefficients on a fixed simplex. -/
theorem coordinates_unique [Fintype J] (V : J → D → ℝ)
    (hV : AffineIndependent ℝ V) (p q : J → ℝ)
    (hmass : (∑ j, p j) = ∑ j, q j)
    (hvalue : (∑ j, p j • V j) = ∑ j, q j • V j) : p = q := by
  funext j
  exact hV.eq_of_sum_eq_sum hmass hvalue j (Finset.mem_univ j)

end InfoGeometry.Projective.AttentionValueCoordinates
