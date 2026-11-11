/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PfaffianFour
import InfoGeometry.Projective.KleinQuadricIncidence
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Plücker linear complexes and their alternating forms

A complex is indexed by its polar representative `C` in the existing
six-coordinate Klein carrier. Its equation on a line `P` is
`incidenceForm C P = 0`. The corresponding alternating form on the native
module `Fin 4 → R` has matrix
`skew4 C.p23 (-C.p13) C.p12 C.p03 (-C.p02) C.p01`.

The determinant is the square of the existing Klein quadratic. Over a field,
the form is nondegenerate exactly off the Klein cone. Every nonzero point then
has a three-dimensional polar hyperplane, containing the point itself.

Source: Plücker, *Neue Geometrie des Raumes*, first-degree complexes,
§1 nos. 26–27 (PDF pp. 45–46) and no. 45 (pp. 65–67), in the supplied
modern republication. See `docs/PLUCKER_LINEAR_COMPLEX_CONTRACT.md` for the
coordinate conversion and precise scope.
-/

noncomputable section

namespace InfoGeometry.Projective.PluckerLinearComplex

open InfoGeometry.Canonical.Pfaffian
open KleinQuadric

section CommRing

variable {R : Type*} [CommRing R]

/-- The alternating matrix associated to the polar coordinates of a complex. -/
def complexMatrix (C : Plucker6 R) : Matrix (Fin 4) (Fin 4) R :=
  skew4 C.p23 (-C.p13) C.p12 C.p03 (-C.p02) C.p01

/-- A linear complex as a genuine Mathlib bilinear form. -/
def complexForm (C : Plucker6 R) : LinearMap.BilinForm R (Fin 4 → R) :=
  (complexMatrix C).toBilin'

/-- The established Pfaffian determinant theorem gives the complex discriminant. -/
theorem complexMatrix_det (C : Plucker6 R) :
    (complexMatrix C).det = (Plucker6.kleinQ C) ^ 2 := by
  rw [complexMatrix, ← pfaffian4_sq_eq_det]
  congr 1
  simp only [pfaffian4, Plucker6.kleinQ]
  ring

/-- Alternation, including in characteristic two, is proved directly. -/
theorem complexForm_isAlt (C : Plucker6 R) : (complexForm C).IsAlt := by
  intro x
  simp [complexForm, Matrix.toBilin'_apply, complexMatrix, skew4,
    Fin.sum_univ_four]
  ring

/-- The point-plane incidence relation is reciprocal. -/
theorem complexForm_zero_iff_swap (C : Plucker6 R) (x y : Fin 4 → R) :
    complexForm C x y = 0 ↔ complexForm C y x = 0 :=
  (complexForm_isAlt C).eq_iff

/-- Rescaling a complex representative rescales its actual bilinear form. -/
theorem complexForm_scale (c : R) (C : Plucker6 R) :
    complexForm (Plucker6.scale c C) = c • complexForm C := by
  ext x y
  simp [complexForm, complexMatrix, skew4, Plucker6.scale,
    Matrix.toBilin'_apply, Fin.sum_univ_four]
  ring

/-- The polar submodule of a point representative. -/
def polarSubmodule (C : Plucker6 R) (x : Fin 4 → R) : Submodule R (Fin 4 → R) :=
  LinearMap.ker (complexForm C x)

/-- Every point is incident with its own polar submodule. -/
theorem mem_polarSubmodule_self (C : Plucker6 R) (x : Fin 4 → R) :
    x ∈ polarSubmodule C x :=
  (complexForm_isAlt C).self_eq_zero x

end CommRing

section Field

variable {K : Type*} [Field K]

/-- A nonzero change of point representative preserves its polar subspace. -/
theorem polarSubmodule_smul_point (C : Plucker6 K) (x : Fin 4 → K)
    {c : K} (hc : c ≠ 0) :
    polarSubmodule C (c • x) = polarSubmodule C x := by
  ext y
  change complexForm C (c • x) y = 0 ↔ complexForm C x y = 0
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero]
  simp [hc]

/-- A nonzero change of complex representative preserves every polar subspace. -/
theorem polarSubmodule_scale (C : Plucker6 K) (x : Fin 4 → K)
    {c : K} (hc : c ≠ 0) :
    polarSubmodule (Plucker6.scale c C) x = polarSubmodule C x := by
  ext y
  change complexForm (Plucker6.scale c C) x y = 0 ↔ complexForm C x y = 0
  rw [complexForm_scale]
  simp [hc]

/-- A nonspecial complex is exactly a nondegenerate alternating form. -/
theorem complexForm_nondegenerate_iff (C : Plucker6 K) :
    (complexForm C).Nondegenerate ↔ Plucker6.kleinQ C ≠ 0 := by
  rw [complexForm, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero,
    complexMatrix_det]
  simp

/-- Off the Klein cone, a nonzero point defines a nonzero covector. -/
theorem complexForm_apply_ne_zero (C : Plucker6 K)
    (hC : Plucker6.kleinQ C ≠ 0) {x : Fin 4 → K} (hx : x ≠ 0) :
    complexForm C x ≠ 0 := by
  intro h
  apply hx
  exact ((complexForm_nondegenerate_iff C).2 hC).1 x
    (fun y => congrArg (fun f : Module.Dual K (Fin 4 → K) => f y) h)

/-- The polar of a nonzero point in a nonspecial complex is a vector
hyperplane of dimension three. -/
theorem finrank_polarSubmodule (C : Plucker6 K)
    (hC : Plucker6.kleinQ C ≠ 0) {x : Fin 4 → K} (hx : x ≠ 0) :
    Module.finrank K (polarSubmodule C x) = 3 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (complexForm_apply_ne_zero C hC hx)
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  change Module.finrank K (LinearMap.ker (complexForm C x)) = 3
  omega

end Field

end InfoGeometry.Projective.PluckerLinearComplex
