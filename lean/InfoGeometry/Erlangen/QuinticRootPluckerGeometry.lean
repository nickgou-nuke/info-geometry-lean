/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent

/-!
# Ordered quintic roots and their two decomposable bivectors

This file formalizes finite algebra on an ordered five-tuple of roots.  It
keeps separate (1) the star bivector `1 ∧ r`, whose coordinates are root
differences and whose image is a linear coboundary subspace, and (2) the
Vandermonde bivector `r ∧ r²`, whose coordinates have degree three.  These
are root-space constructions; this file does not assert a map from unordered
quintic coefficients or a projective/Galois descent theorem.
-/

noncomputable section

namespace InfoGeometry.Erlangen.QuinticRootPluckerGeometry

abbrev RootTuple (R : Type*) := Fin 5 → R

/-- Coordinates of the star bivector `1 ∧ r`. -/
def starDifference {R : Type*} [Sub R] (r : RootTuple R)
    (i j : Fin 5) : R := r j - r i

/-- Coordinates of `r ∧ r²`; these are cubic in the roots. -/
def vandermondeBivector {R : Type*} [CommRing R] (r : RootTuple R)
    (i j : Fin 5) : R := r i * r j * (r j - r i)

/-- Root dilation has weight one on each star difference. -/
theorem starDifference_smul {R : Type*} [Ring R] (c : R)
    (r : RootTuple R) (i j : Fin 5) :
    starDifference (fun k => c * r k) i j = c * starDifference r i j := by
  simp [starDifference, mul_sub]

/-- Translation of all roots leaves the star difference bivector unchanged. -/
theorem starDifference_translate {R : Type*} [AddCommGroup R]
    (r : RootTuple R) (t : R) (i j : Fin 5) :
    starDifference (fun k => r k + t) i j = starDifference r i j := by
  simp [starDifference, add_sub_add_right_eq_sub]

/-- The star differences are an exact simplicial coboundary. -/
theorem starDifference_coboundary {R : Type*} [AddCommGroup R]
    (r : RootTuple R) (i j k : Fin 5) :
    starDifference r i j + starDifference r j k = starDifference r i k := by
  change (r j - r i) + (r k - r j) = r k - r i
  calc
    (r j - r i) + (r k - r j) = r k - r i := by abel

/-- The star bivector vanishes precisely on constant root tuples. -/
theorem starDifference_all_zero_iff_constant {R : Type*} [AddCommGroup R]
    (r : RootTuple R) :
    (∀ i j : Fin 5, starDifference r i j = 0) ↔ ∃ a : R, ∀ i, r i = a := by
  constructor
  · intro h
    refine ⟨r 0, ?_⟩
    intro i
    have hi := h 0 i
    simp [starDifference] at hi
    exact sub_eq_zero.mp hi
  · rintro ⟨a, ha⟩ i j
    simp [starDifference, ha]

/-- On the sum-zero hyperplane over a characteristic-zero field, the star
bivector has no nonzero kernel. This is the algebraic guard needed before
projectivizing this homogeneous map. -/
theorem starDifference_zero_of_sum_zero {K : Type*} [Field K] [CharZero K]
    (r : RootTuple K) (hzero : ∀ i j, starDifference r i j = 0)
    (hsum : ∑ i : Fin 5, r i = 0) : r = 0 := by
  obtain ⟨a, ha⟩ := (starDifference_all_zero_iff_constant r).mp hzero
  have hfive : (5 : K) * a = 0 := by
    calc
      (5 : K) * a = ∑ _i : Fin 5, a := by simp
      _ = ∑ i : Fin 5, r i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ha i]
      _ = 0 := hsum
  have ha0 : a = 0 := (mul_eq_zero.mp hfive).resolve_left (by norm_num)
  funext i
  rw [ha i, ha0]
  rfl

/-- Linear coordinate map for the star-difference bivector. The codomain keeps
all ordered pairs; antisymmetry and the diagonal zero are consequences of
the definition rather than hidden quotient conventions. -/
def starDifferenceLinearMap (K : Type*) [Ring K] :
    RootTuple K →ₗ[K] (Fin 5 × Fin 5 → K) where
  toFun r ij := r ij.2 - r ij.1
  map_add' r s := by
    funext ij
    simp only [Pi.add_apply]
    abel
  map_smul' c r := by
    funext ij
    simp only [Pi.smul_apply, smul_eq_mul]
    noncomm_ring

/-- The Tschirnhaus sum-zero subspace of ordered root coordinates. -/
def centeredRootSubspace (K : Type*) [Field K] :
    Submodule K (RootTuple K) where
  carrier := {r | ∑ i : Fin 5, r i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs
    change (∑ i : Fin 5, (r + s) i) = 0
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, hr, hs, add_zero]
  smul_mem' := by
    intro c r hr
    change (∑ i : Fin 5, (c • r) i) = 0
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hr, mul_zero]

/-- On a characteristic-zero field, the star-difference map restricted to
the centered root subspace is injective. This is the linear-algebraic form of
removing the diagonal kernel before projective descent. -/
theorem starDifferenceLinearMap_injective_centered
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective
      ((starDifferenceLinearMap K).comp (centeredRootSubspace K).subtype) := by
  intro r s hrs
  apply Subtype.ext
  change starDifferenceLinearMap K r.1 = starDifferenceLinearMap K s.1 at hrs
  have hdiff : ∀ i j : Fin 5, starDifference r.1 i j =
      starDifference s.1 i j := by
    intro i j
    simpa [starDifference, starDifferenceLinearMap] using congrFun hrs (i, j)
  have hzero : ∀ i j, starDifference (r.1 - s.1) i j = 0 := by
    intro i j
    change (r.1 j - s.1 j) - (r.1 i - s.1 i) = 0
    have hdiff' := hdiff i j
    change r.1 j - r.1 i = s.1 j - s.1 i at hdiff'
    linear_combination hdiff'
  have hsum : ∑ i : Fin 5, (r.1 - s.1) i = 0 := by
    change (∑ i : Fin 5, (r.1 i - s.1 i)) = 0
    rw [Finset.sum_sub_distrib, r.2, s.2, sub_self]
  exact sub_eq_zero.mp
    (starDifference_zero_of_sum_zero (r.1 - s.1) hzero hsum)

/-- Root dilation has weight three on the Vandermonde bivector. -/
theorem vandermondeBivector_smul {R : Type*} [CommRing R] (c : R)
    (r : RootTuple R) (i j : Fin 5) :
    vandermondeBivector (fun k => c * r k) i j =
      c ^ 3 * vandermondeBivector r i j := by
  simp [vandermondeBivector, mul_sub]
  ring

/-- The cubic bivector is decomposable: its four-index Plücker relation
holds because it is the wedge of `r` and the coordinatewise square of `r`. -/
theorem vandermondeBivector_plucker {R : Type*} [CommRing R]
    (r : RootTuple R) (i j k l : Fin 5) :
    vandermondeBivector r i j * vandermondeBivector r k l -
      vandermondeBivector r i k * vandermondeBivector r j l +
      vandermondeBivector r i l * vandermondeBivector r j k = 0 := by
  simp only [vandermondeBivector]
  ring

/-- Despite being decomposable, the cubic coordinates are generally not a
1-coboundary. The exact cyclic expression is the product of three root
differences. -/
theorem vandermondeBivector_coboundary {R : Type*} [CommRing R]
    (r : RootTuple R) (i j k : Fin 5) :
    vandermondeBivector r i j + vandermondeBivector r j k -
      vandermondeBivector r i k =
        (r j - r i) * (r k - r j) * (r k - r i) := by
  simp only [vandermondeBivector]
  ring

/-- A concrete counterexample to the claim that the cubic bivector remains
in the star-difference coboundary subspace: roots `(0,1,2)` give cyclic sum 2. -/
theorem vandermondeBivector_not_always_coboundary :
    ∃ r : RootTuple ℤ,
      vandermondeBivector r 0 1 + vandermondeBivector r 1 2 -
        vandermondeBivector r 0 2 ≠ 0 := by
  refine ⟨fun i => (i : ℤ), ?_⟩
  norm_num [vandermondeBivector]

open InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
open InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ

/-- The star-difference bivector of the owner's explicit Klein root tuple. -/
def kleinOrbitStarDifference (z : ℂ × ℂ) (i j : Fin 5) : ℂ :=
  starDifference (kleinBrioschiRootTuple z) i j

/-- The owner's projective invariance of its root tuple induces projective
invariance of the ordered-root star bivector on the same nondegenerate chart. -/
theorem kleinOrbitStarDifference_scale (c : ℂ) (z : ℂ × ℂ)
    (hc : c ≠ 0) (hT : kleinIcosahedralEdgeT z.1 z.2 ≠ 0)
    (i j : Fin 5) :
    kleinOrbitStarDifference (c * z.1, c * z.2) i j =
      kleinOrbitStarDifference z i j := by
  change starDifference (kleinBrioschiRootTuple (c * z.1, c * z.2)) i j = _
  rw [kleinBrioschiRootTuple_scale c z hc hT]
  rfl

/-- Under the checked order-five generator, the star bivector follows the
same cyclic reindexing as the five ordered roots. -/
theorem kleinOrbitStarDifference_equivariant (z : ℂ × ℂ) (i j : Fin 5) :
    kleinOrbitStarDifference (kleinOrderFiveStep z) i j =
      kleinOrbitStarDifference z (kleinResolventCycleSucc i)
        (kleinResolventCycleSucc j) := by
  simp [kleinOrbitStarDifference, starDifference,
    kleinBrioschiRootTuple_equivariant]

end InfoGeometry.Erlangen.QuinticRootPluckerGeometry
