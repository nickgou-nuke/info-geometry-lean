/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.PluckerLinearComplexGeometry

/-!
# Homogeneous pencils of Plücker linear complexes

The two scalar parameters include the member at infinity. The established
Klein quadratic expansion controls degeneracy; the new form controls actual
line-complex membership. No number or reality of roots is assumed.
-/

noncomputable section

namespace InfoGeometry.Projective.PluckerComplexPencil

open KleinQuadric PluckerLinearComplex PluckerLinearComplexGeometry
open ExteriorKleinTwoPlaneQuotient ExteriorKleinTwoPlaneIncidence

section CommRing

variable {R : Type*} [CommRing R]

/-- Addition of polar representatives is addition of their bilinear forms. -/
theorem complexForm_add (C D : Plucker6 R) :
    complexForm (Plucker6.add C D) = complexForm C + complexForm D := by
  ext x y
  simp [complexForm, complexMatrix, InfoGeometry.Canonical.Pfaffian.skew4,
    Plucker6.add, Matrix.toBilin'_apply, Fin.sum_univ_four]
  ring

/-- The discriminant polynomial in homogeneous pencil parameters. -/
theorem kleinQ_homogeneous_pencil (C D : Plucker6 R) (s t : R) :
    Plucker6.kleinQ (Plucker6.add (Plucker6.scale s C) (Plucker6.scale t D)) =
      s ^ 2 * Plucker6.kleinQ C + s * t * Plucker6.polar C D +
        t ^ 2 * Plucker6.kleinQ D := by
  have h := Plucker6.kleinQ_add_scale (1 : R)
    (Plucker6.scale s C) (Plucker6.scale t D)
  have hscale : Plucker6.scale (1 : R) (Plucker6.scale t D) =
      Plucker6.scale t D := by
    cases D
    simp [Plucker6.scale]
  rw [hscale, Plucker6.kleinQ_scale, Plucker6.kleinQ_scale,
    Plucker6.polar_scale_left, Plucker6.polar_scale_right] at h
  simpa only [one_mul, one_pow, mul_assoc] using h

end CommRing

/-- Nonspecial members are exactly the nonzeros of the homogeneous quadratic. -/
theorem pencil_nondegenerate_iff {K : Type*} [Field K]
    (C D : Plucker6 K) (s t : K) :
    (complexForm (Plucker6.add (Plucker6.scale s C) (Plucker6.scale t D))).Nondegenerate ↔
      s ^ 2 * Plucker6.kleinQ C + s * t * Plucker6.polar C D +
        t ^ 2 * Plucker6.kleinQ D ≠ 0 := by
  rw [complexForm_nondegenerate_iff, kleinQ_homogeneous_pencil]

/-- Evaluation of a homogeneous pencil on the native real four-space. -/
theorem nativeComplexForm_pencil (C D : Plucker6 ℝ) (s t : ℝ)
    (x y : InfoGeometry.Canonical.FierzKleinFoundation.Vec4) :
    nativeComplexForm (Plucker6.add (Plucker6.scale s C) (Plucker6.scale t D)) x y =
      s * nativeComplexForm C x y + t * nativeComplexForm D x y := by
  change complexForm (Plucker6.add (Plucker6.scale s C) (Plucker6.scale t D))
    (nativeCoordinates x) (nativeCoordinates y) = _
  rw [complexForm_add, complexForm_scale, complexForm_scale]
  rfl

/-- Every line common to the generators belongs to every pencil member. -/
theorem mem_lineComplex_pencil_of_mem (C D : Plucker6 ℝ) (s t : ℝ)
    {P : RealTwoPlane} (hC : P ∈ lineComplex C) (hD : P ∈ lineComplex D) :
    P ∈ lineComplex (Plucker6.add (Plucker6.scale s C) (Plucker6.scale t D)) := by
  intro x hx y hy
  rw [nativeComplexForm_pencil, hC x hx y hy, hD x hx y hy]
  simp

/-- Replacing the second generator by a member with nonzero second
coefficient preserves the actual congruence of common lines. -/
theorem lineComplex_inter_pencil (C D : Plucker6 ℝ) (s t : ℝ) (ht : t ≠ 0) :
    lineComplex C ∩
        lineComplex (Plucker6.add (Plucker6.scale s C) (Plucker6.scale t D)) =
      lineComplex C ∩ lineComplex D := by
  ext P
  constructor
  · rintro ⟨hC, hP⟩
    refine ⟨hC, ?_⟩
    intro x hx y hy
    have h := hP x hx y hy
    rw [nativeComplexForm_pencil, hC x hx y hy, mul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left ht
  · rintro ⟨hC, hD⟩
    exact ⟨hC, mem_lineComplex_pencil_of_mem C D s t hC hD⟩

/-- A nonzero real root member has a directrix; its common lines with the
other generator consequently meet that directrix. -/
theorem special_pencil_exists_directrix (C D : Plucker6 ℝ) (s t : ℝ)
    (hne : complexMatrix (Plucker6.add (Plucker6.scale s C) (Plucker6.scale t D)) ≠ 0)
    (hroot : s ^ 2 * Plucker6.kleinQ C + s * t * Plucker6.polar C D +
      t ^ 2 * Plucker6.kleinQ D = 0) :
    ∃ A : RealTwoPlane,
      LinearMap.ker
        (nativeComplexForm (Plucker6.add (Plucker6.scale s C) (Plucker6.scale t D))) = A.1 ∧
      ∀ P : RealTwoPlane, P ∈ lineComplex C → P ∈ lineComplex D → PlanesIncident A P := by
  have hQ := (kleinQ_homogeneous_pencil C D s t).trans hroot
  obtain ⟨A, hker, hinc⟩ := special_complex_exists_directrix _ hne hQ
  refine ⟨A, hker, ?_⟩
  intro P hC hD
  exact (hinc P).mp (mem_lineComplex_pencil_of_mem C D s t hC hD)

end InfoGeometry.Projective.PluckerComplexPencil
