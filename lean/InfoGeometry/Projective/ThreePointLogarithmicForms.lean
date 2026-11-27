/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.CrossRatio
import InfoGeometry.Projective.Quadrics.PluckerKlein
import InfoGeometry.Projective.AmplituhedronBostConnesSynthesis
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Native logarithmic forms and the four-point projective coordinate

The homogeneous coordinate uses the existing Plücker minors and agrees with
the existing affine cross-ratio. Native `LinearMap` covectors and
`AlternatingMap` two-forms realize the three-point Arnold relation using the
existing rational Arnold syzygy.

These are finite coordinate identities and ordinary derivative identities.
No configuration-manifold de Rham comparison, global logarithm, twisted
intersection pairing, or scattering-amplitude representation is asserted.
Division is total in Lean; the Arnold and projective-chart statements name
their pole-exclusion hypotheses.
-/

noncomputable section

namespace InfoGeometry.Projective.ThreePointLogarithmicForms

open InfoGeometry.Projective.Quadrics.PluckerKlein
open InfoGeometry.Projective.AmplituhedronBostConnesSynthesis

section ProjectiveCoordinate

variable {K : Type*} [Field K]

/-- For the two rows of four homogeneous columns, use `p01*p23/(p02*p13)`. -/
def homogeneousCrossRatio (x y : Fin 4 → K) : K :=
  (pluckerCoord x y 0 1 * pluckerCoord x y 2 3) /
    (pluckerCoord x y 0 2 * pluckerCoord x y 1 3)

/-- The complementary letter follows from the existing Plücker relation. -/
theorem one_sub_homogeneousCrossRatio (x y : Fin 4 → K)
    (h02 : pluckerCoord x y 0 2 ≠ 0) (h13 : pluckerCoord x y 1 3 ≠ 0) :
    1 - homogeneousCrossRatio x y =
      (pluckerCoord x y 0 3 * pluckerCoord x y 1 2) /
        (pluckerCoord x y 0 2 * pluckerCoord x y 1 3) := by
  unfold homogeneousCrossRatio
  field_simp [h02, h13]
  linear_combination -plucker_klein_relation x y

/-- Affine columns recover the repository's existing cross-ratio convention. -/
theorem homogeneousCrossRatio_affine (z : Fin 4 → K) :
    homogeneousCrossRatio z (fun _ => 1) =
      InfoGeometry.Projective.crossRatio (z 0) (z 1) (z 2) (z 3) := by
  simp [homogeneousCrossRatio, pluckerCoord, InfoGeometry.Projective.crossRatio]

/-- The columns `(0, z, 1, infinity)` have cross-ratio `z`. -/
theorem homogeneousCrossRatio_normalized (z : K) :
    homogeneousCrossRatio ![0, z, 1, 1] ![1, 1, 1, 0] = z := by
  simp [homogeneousCrossRatio, pluckerCoord]

/-- Nonvanishing numerator and denominator minors exclude the zero letter. -/
theorem homogeneousCrossRatio_ne_zero (x y : Fin 4 → K)
    (h01 : pluckerCoord x y 0 1 ≠ 0) (h23 : pluckerCoord x y 2 3 ≠ 0)
    (h02 : pluckerCoord x y 0 2 ≠ 0) (h13 : pluckerCoord x y 1 3 ≠ 0) :
    homogeneousCrossRatio x y ≠ 0 :=
  div_ne_zero (mul_ne_zero h01 h23) (mul_ne_zero h02 h13)

/-- Nonvanishing complementary minors exclude the unit letter. -/
theorem homogeneousCrossRatio_ne_one (x y : Fin 4 → K)
    (h02 : pluckerCoord x y 0 2 ≠ 0) (h13 : pluckerCoord x y 1 3 ≠ 0)
    (h03 : pluckerCoord x y 0 3 ≠ 0) (h12 : pluckerCoord x y 1 2 ≠ 0) :
    homogeneousCrossRatio x y ≠ 1 := by
  have h : 1 - homogeneousCrossRatio x y ≠ 0 := by
    rw [one_sub_homogeneousCrossRatio x y h02 h13]
    exact div_ne_zero (mul_ne_zero h03 h12) (mul_ne_zero h02 h13)
  intro hx
  exact h (by simp [hx])

end ProjectiveCoordinate

section NativeForms

variable {K : Type*} [Field K]

/-- Coordinate evaluation as a native covector on the three-point carrier. -/
def coordinateCovector (i : Fin 3) : (Fin 3 → K) →ₗ[K] K where
  toFun v := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateCovector_apply (i : Fin 3) (v : Fin 3 → K) :
    coordinateCovector i v = v i := rfl

/-- The logarithmic difference covector `(dz_i - dz_j) / (z_i - z_j)`. -/
def edgeForm (z : Fin 3 → K) (i j : Fin 3) : (Fin 3 → K) →ₗ[K] K :=
  (1 / (z i - z j)) • (coordinateCovector i - coordinateCovector j)

@[simp] theorem edgeForm_apply (z v : Fin 3 → K) (i j : Fin 3) :
    edgeForm z i j v = (1 / (z i - z j)) * (v i - v j) := rfl

theorem edgeForm_apply_div (z v : Fin 3 → K) (i j : Fin 3) :
    edgeForm z i j v = (v i - v j) / (z i - z j) := by
  rw [edgeForm_apply]
  ring

/-- Evaluation of the exterior product of two covectors. -/
def wedgeEval {V : Type*} [AddCommGroup V] [Module K V]
    (a b : V →ₗ[K] K) (v w : V) : K := a v * b w - a w * b v

/-- Exterior product into the native carrier of alternating two-forms. -/
def wedge {V : Type*} [AddCommGroup V] [Module K V]
    (a b : V →ₗ[K] K) : V [⋀^Fin 2]→ₗ[K] K where
  toFun v := wedgeEval a b (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp [wedgeEval, Function.update] <;> ring
  map_update_smul' v i c x := by
    fin_cases i <;>
      simp [wedgeEval, Function.update, map_smul, smul_eq_mul] <;> ring
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j <;> simp_all [wedgeEval]

@[simp] theorem wedge_apply {V : Type*} [AddCommGroup V] [Module K V]
    (a b : V →ₗ[K] K) (v : Fin 2 → V) :
    wedge a b v = a (v 0) * b (v 1) - a (v 1) * b (v 0) := rfl

/-- The native numerator factors through the existing rational Arnold syzygy. -/
theorem arnold_eval (z v w : Fin 3 → K)
    (h01 : z 0 ≠ z 1) (h12 : z 1 ≠ z 2) (h20 : z 2 ≠ z 0) :
    wedgeEval (edgeForm z 0 1) (edgeForm z 1 2) v w +
      wedgeEval (edgeForm z 1 2) (edgeForm z 2 0) v w +
      wedgeEval (edgeForm z 2 0) (edgeForm z 0 1) v w = 0 := by
  let D : K := (v 0 - v 1) * (w 1 - w 2) - (v 1 - v 2) * (w 0 - w 1)
  have hfactor :
      wedgeEval (edgeForm z 0 1) (edgeForm z 1 2) v w +
        wedgeEval (edgeForm z 1 2) (edgeForm z 2 0) v w +
        wedgeEval (edgeForm z 2 0) (edgeForm z 0 1) v w =
      ((1 / (z 0 - z 1)) * (1 / (z 1 - z 2)) +
        (1 / (z 1 - z 2)) * (1 / (z 2 - z 0)) +
        (1 / (z 2 - z 0)) * (1 / (z 0 - z 1))) * D := by
    simp only [wedgeEval, edgeForm_apply]
    dsimp [D]
    ring
  have hcoeff :
      (1 / (z 0 - z 1)) * (1 / (z 1 - z 2)) +
        (1 / (z 1 - z 2)) * (1 / (z 2 - z 0)) +
        (1 / (z 2 - z 0)) * (1 / (z 0 - z 1)) = 0 := by
    simpa only [arnoldRational] using
      arnold_rational_field_syzygy (z 0) (z 1) (z 2) h01 h12 h20
  rw [hfactor, hcoeff, zero_mul]

/-- Arnold's relation is an equality of genuine alternating two-forms. -/
theorem arnold_relation (z : Fin 3 → K)
    (h01 : z 0 ≠ z 1) (h12 : z 1 ≠ z 2) (h20 : z 2 ≠ z 0) :
    wedge (edgeForm z 0 1) (edgeForm z 1 2) +
      wedge (edgeForm z 1 2) (edgeForm z 2 0) +
      wedge (edgeForm z 2 0) (edgeForm z 0 1) = 0 := by
  ext v
  exact arnold_eval z (v 0) (v 1) h01 h12 h20

end NativeForms

section LogarithmicCalculus

variable {K : Type*} [NontriviallyNormedField K]

/-- Pullback coefficient for the difference of two differentiable coordinates.
At a zero difference this is only a totalized algebraic identity; a geometric
logarithmic form is restricted to the nonzero-difference locus. -/
theorem logDeriv_difference {f g : K → K} {x f' g' : K}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    logDeriv (fun t => f t - g t) x = (f' - g') / (f x - g x) := by
  rw [logDeriv_apply, (hf.sub hg).deriv]

/-- A regular quotient pulls a logarithmic derivative back to a difference. -/
theorem logDeriv_ratio {f g : K → K} {x : K}
    (hf : f x ≠ 0) (hg : g x ≠ 0)
    (hdf : DifferentiableAt K f x) (hdg : DifferentiableAt K g x) :
    logDeriv (fun t => f t / g t) x = logDeriv f x - logDeriv g x := by
  exact logDeriv_div x hf hg hdf hdg

end LogarithmicCalculus

end InfoGeometry.Projective.ThreePointLogarithmicForms
