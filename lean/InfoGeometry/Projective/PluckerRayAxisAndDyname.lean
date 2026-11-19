/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.KleinQuadric
import InfoGeometry.Projective.KleinQuadricPlucker
import InfoGeometry.Projective.PluckerMatrixAction
import InfoGeometry.Projective.PluckerLinearComplex
import InfoGeometry.Projective.PluckerAffineScrew

/-!
# Plücker Ray–Axis Coordinates, Dynames, and Linear Complex Conjugacy

This module formalizes Archetypes `PL₁` (`§1, Nos. 1–16`), `PL₂` (`§2, Nos. 17–25`),
and `PL₃` (`Abth. I, §1, Nos. 26–61`) of Julius Plücker's *Neue Geometrie des Raumes*
(`Liniengeometriev1.pdf`, pp. 23–74):

* Exact bridge between `KleinQuadric.Plucker6` and `KleinQuadricPlucker.Plucker6`,
  ray coordinates (`rayPlucker`), axis coordinates via `axisDualEquiv`, and the
  polynomial-ring identity showing that all fifteen `2 × 2` minors between ray and axis
  coordinates vanish whenever four point–plane incidences hold (`ray_axis_minors_eq_of_four_incidences`).
* Conjugate-imaginary line decomposition (`rayPlucker_conj_line`), separating lines
  of the first kind (intersecting real carrier, `A.kleinQ = 0`) and skew second-kind pairs.
* Affine rigid covariance under translations and `SO(3)` rotations, plus homogeneous
  degree-`n` preservation for complex cones and conics (`homogeneousFun_comp_linear`).
* Mechanics of dynames (`dyname_add_kleinQ`, `exists_two_finite_forces_for_dyname`),
  showing every nonzero force/couple dyname splits into two finite forces.
* Linear complexes: matrix null-system conjugate polar identity
  `axisDualEquiv (transform (complexMatrix C) P) = (C.polar P) • C - C.kleinQ • P`,
  five-line uniqueness (`finrank_fiveLineComplexSubmodule`), and the canonical central axis
  slope law (`canonicalCentralComplex_slope`).
-/

namespace InfoGeometry.Projective.PluckerRayAxisAndDyname

open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Projective.PluckerLinearComplex
open InfoGeometry.Projective.PluckerAffineScrew
open Matrix

section RayAxisDuality

/-- Canonical coordinate equivalence between the two Plücker 6-vector records in
`InfoGeometry.Projective`. -/
def plucker6Equiv {R : Type*} :
    KleinQuadric.Plucker6 R ≃ KleinQuadricPlucker.Plucker6 R where
  toFun P := ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
  invFun P := ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma plucker6Equiv_kleinQ {R : Type*} [Ring R] (P : KleinQuadric.Plucker6 R) :
    (plucker6Equiv P).kleinQ = P.kleinQ := by
  cases P
  dsimp [plucker6Equiv, Plucker6.kleinQ, KleinQuadricPlucker.Plucker6.kleinQ]

/-- Plücker ray coordinates of the line joining two homogeneous points `x, y : Fin 4 → R`
(`Plücker No. 2`, `p. 24`). -/
def rayPlucker {R : Type*} [Ring R] (x y : Fin 4 → R) : KleinQuadric.Plucker6 R where
  p01 := x 0 * y 1 - x 1 * y 0
  p02 := x 0 * y 2 - x 2 * y 0
  p03 := x 0 * y 3 - x 3 * y 0
  p12 := x 1 * y 2 - x 2 * y 1
  p13 := x 1 * y 3 - x 3 * y 1
  p23 := x 2 * y 3 - x 3 * y 2

/-- Ray–axis duality involution mapping `(p01, p02, p03, p12, p13, p23)` to
`(p23, -p13, p12, p03, -p02, p01)` (`Plücker Nos. 4–8`, `pp. 26–29`). -/
def axisDualEquiv {R : Type*} [Ring R] :
    KleinQuadric.Plucker6 R ≃ KleinQuadric.Plucker6 R where
  toFun P := ⟨P.p23, -P.p13, P.p12, P.p03, -P.p02, P.p01⟩
  invFun P := ⟨P.p23, -P.p13, P.p12, P.p03, -P.p02, P.p01⟩
  left_inv P := by cases P; simp
  right_inv P := by cases P; simp

@[simp]
lemma axisDualEquiv_symm_apply {R : Type*} [Ring R] (P : KleinQuadric.Plucker6 R) :
    (axisDualEquiv : KleinQuadric.Plucker6 R ≃ _).symm P = axisDualEquiv P := by
  cases P
  dsimp [axisDualEquiv]

/-- Ray coordinates of the axis cut out by two homogeneous planes `u, v : Fin 4 → R`. -/
def axisAsRayPlucker {R : Type*} [Ring R] (u v : Fin 4 → R) : KleinQuadric.Plucker6 R :=
  axisDualEquiv (rayPlucker u v)

theorem rayPlucker_kleinQ {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    (rayPlucker x y).kleinQ = 0 := by
  simp [rayPlucker, Plucker6.kleinQ]
  ring

theorem axisAsRayPlucker_kleinQ {R : Type*} [CommRing R] (u v : Fin 4 → R) :
    (axisAsRayPlucker u v).kleinQ = 0 := by
  simp [axisAsRayPlucker, axisDualEquiv, rayPlucker, Plucker6.kleinQ]
  ring

theorem axisDualEquiv_kleinQ {R : Type*} [CommRing R] (P : KleinQuadric.Plucker6 R) :
    (axisDualEquiv P).kleinQ = P.kleinQ := by
  simp [axisDualEquiv, Plucker6.kleinQ]
  ring

theorem axisDualEquiv_polar {R : Type*} [CommRing R] (P Q : KleinQuadric.Plucker6 R) :
    (axisDualEquiv P).polar (axisDualEquiv Q) = P.polar Q := by
  simp [Plucker6.polar, Plucker6.add, axisDualEquiv, Plucker6.kleinQ]
  ring

private lemma minor_overlap_identity {R : Type*} [CommRing R]
    (xa xb xc xd ya yb yc yd ua ub uc ud va vb vc vd : R)
    (hux : ua * xa + ub * xb + uc * xc + ud * xd = 0)
    (huy : ua * ya + ub * yb + uc * yc + ud * yd = 0)
    (hvx : va * xa + vb * xb + vc * xc + vd * xd = 0)
    (hvy : va * ya + vb * yb + vc * yc + vd * yd = 0) :
    (xa * yb - xb * ya) * (ua * vd - ud * va) =
      (xb * yc - xc * yb) * (uc * vd - ud * vc) := by
  have h :
      (xa * yb - xb * ya) * (ua * vd - ud * va) -
        (xb * yc - xc * yb) * (uc * vd - ud * vc) =
      vd * (yb * (ua * xa + ub * xb + uc * xc + ud * xd) -
            xb * (ua * ya + ub * yb + uc * yc + ud * yd)) -
      ud * (yb * (va * xa + vb * xb + vc * xc + vd * xd) -
            xb * (va * ya + vb * yb + vc * yc + vd * yd)) := by ring
  exact sub_eq_zero.mp (by rw [h, hux, huy, hvx, hvy]; ring)

private lemma minor_disjoint_identity {R : Type*} [CommRing R]
    (xa xb xc xd ya yb yc yd ua ub uc ud va vb vc vd : R)
    (hux : ua * xa + ub * xb + uc * xc + ud * xd = 0)
    (huy : ua * ya + ub * yb + uc * yc + ud * yd = 0)
    (hvx : va * xa + vb * xb + vc * xc + vd * xd = 0)
    (hvy : va * ya + vb * yb + vc * yc + vd * yd = 0) :
    (xa * yb - xb * ya) * (ua * vb - ub * va) =
      (xc * yd - xd * yc) * (uc * vd - ud * vc) := by
  have h1 : uc * xc + ud * xd = -(ua * xa + ub * xb) :=
    eq_neg_of_add_eq_zero_right (by linear_combination hux)
  have h2 : uc * yc + ud * yd = -(ua * ya + ub * yb) :=
    eq_neg_of_add_eq_zero_right (by linear_combination huy)
  have h3 : vc * xc + vd * xd = -(va * xa + vb * xb) :=
    eq_neg_of_add_eq_zero_right (by linear_combination hvx)
  have h4 : vc * yc + vd * yd = -(va * ya + vb * yb) :=
    eq_neg_of_add_eq_zero_right (by linear_combination hvy)
  have hcb1 :
      (xa * yb - xb * ya) * (ua * vb - ub * va) =
      (ua * xa + ub * xb) * (va * ya + vb * yb) -
        (ua * ya + ub * yb) * (va * xa + vb * xb) := by ring
  have hcb2 :
      (xc * yd - xd * yc) * (uc * vd - ud * vc) =
      (uc * xc + ud * xd) * (vc * yc + vd * yd) -
        (uc * yc + ud * yd) * (vc * xc + vd * xd) := by ring
  rw [hcb1, hcb2, h1, h2, h3, h4]
  ring

private lemma ray_axis_minors_lt {R : Type*} [CommRing R] (x y u v : Fin 4 → R)
    (hux : ∑ k, u k * x k = 0) (huy : ∑ k, u k * y k = 0)
    (hvx : ∑ k, v k * x k = 0) (hvy : ∑ k, v k * y k = 0) :
    ∀ {i j : Fin 6}, i < j →
      coordinates (rayPlucker x y) i * coordinates (axisAsRayPlucker u v) j =
        coordinates (rayPlucker x y) j * coordinates (axisAsRayPlucker u v) i := by
  have sux : u 0 * x 0 + u 1 * x 1 + u 2 * x 2 + u 3 * x 3 = 0 := by
    simpa [Fin.sum_univ_four, add_assoc] using hux
  have suy : u 0 * y 0 + u 1 * y 1 + u 2 * y 2 + u 3 * y 3 = 0 := by
    simpa [Fin.sum_univ_four, add_assoc] using huy
  have svx : v 0 * x 0 + v 1 * x 1 + v 2 * x 2 + v 3 * x 3 = 0 := by
    simpa [Fin.sum_univ_four, add_assoc] using hvx
  have svy : v 0 * y 0 + v 1 * y 1 + v 2 * y 2 + v 3 * y 3 = 0 := by
    simpa [Fin.sum_univ_four, add_assoc] using hvy
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals dsimp [coordinates, rayPlucker, axisAsRayPlucker, axisDualEquiv]
  · -- (0, 1): x01 * (-u13) = x02 * u23
    have hm := minor_overlap_identity
      (x 1) (x 0) (x 2) (x 3) (y 1) (y 0) (y 2) (y 3)
      (u 1) (u 0) (u 2) (u 3) (v 1) (v 0) (v 2) (v 3)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination hm
  · -- (0, 2): x01 * u12 = x03 * u23
    have hm := minor_overlap_identity
      (x 1) (x 0) (x 3) (x 2) (y 1) (y 0) (y 3) (y 2)
      (u 1) (u 0) (u 3) (u 2) (v 1) (v 0) (v 3) (v 2)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination -hm
  · -- (0, 3): x01 * u03 = x12 * u23
    have hm := minor_overlap_identity
      (x 0) (x 1) (x 2) (x 3) (y 0) (y 1) (y 2) (y 3)
      (u 0) (u 1) (u 2) (u 3) (v 0) (v 1) (v 2) (v 3) sux suy svx svy
    linear_combination hm
  · -- (0, 4): x01 * (-u02) = x13 * u23
    have hm := minor_overlap_identity
      (x 0) (x 1) (x 3) (x 2) (y 0) (y 1) (y 3) (y 2)
      (u 0) (u 1) (u 3) (u 2) (v 0) (v 1) (v 3) (v 2)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination -hm
  · -- (0, 5): x01 * u01 = x23 * u23
    exact minor_disjoint_identity
      (x 0) (x 1) (x 2) (x 3) (y 0) (y 1) (y 2) (y 3)
      (u 0) (u 1) (u 2) (u 3) (v 0) (v 1) (v 2) (v 3) sux suy svx svy
  · -- (1, 2): x02 * u12 = x03 * (-u13)
    have hm := minor_overlap_identity
      (x 2) (x 0) (x 3) (x 1) (y 2) (y 0) (y 3) (y 1)
      (u 2) (u 0) (u 3) (u 1) (v 2) (v 0) (v 3) (v 1)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination hm
  · -- (1, 3): x02 * u03 = x12 * (-u13)
    have hm := minor_overlap_identity
      (x 0) (x 2) (x 1) (x 3) (y 0) (y 2) (y 1) (y 3)
      (u 0) (u 2) (u 1) (u 3) (v 0) (v 2) (v 1) (v 3)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination hm
  · -- (1, 4): x02 * (-u02) = x13 * (-u13)
    have hm := minor_disjoint_identity
      (x 0) (x 2) (x 1) (x 3) (y 0) (y 2) (y 1) (y 3)
      (u 0) (u 2) (u 1) (u 3) (v 0) (v 2) (v 1) (v 3)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination -hm
  · -- (1, 5): x02 * u01 = x23 * (-u13)
    have hm := minor_overlap_identity
      (x 0) (x 2) (x 3) (x 1) (y 0) (y 2) (y 3) (y 1)
      (u 0) (u 2) (u 3) (u 1) (v 0) (v 2) (v 3) (v 1)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination hm
  · -- (2, 3): x03 * u03 = x12 * u12
    exact minor_disjoint_identity
      (x 0) (x 3) (x 1) (x 2) (y 0) (y 3) (y 1) (y 2)
      (u 0) (u 3) (u 1) (u 2) (v 0) (v 3) (v 1) (v 2)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
  · -- (2, 4): x03 * (-u02) = x13 * u12
    have hm := minor_overlap_identity
      (x 0) (x 3) (x 1) (x 2) (y 0) (y 3) (y 1) (y 2)
      (u 0) (u 3) (u 1) (u 2) (v 0) (v 3) (v 1) (v 2)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination -hm
  · -- (2, 5): x03 * u01 = x23 * u12
    have hm := minor_overlap_identity
      (x 0) (x 3) (x 2) (x 1) (y 0) (y 3) (y 2) (y 1)
      (u 0) (u 3) (u 2) (u 1) (v 0) (v 3) (v 2) (v 1)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination hm
  · -- (3, 4): x12 * (-u02) = x13 * u03
    have hm := minor_overlap_identity
      (x 2) (x 1) (x 3) (x 0) (y 2) (y 1) (y 3) (y 0)
      (u 2) (u 1) (u 3) (u 0) (v 2) (v 1) (v 3) (v 0)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination -hm
  · -- (3, 5): x12 * u01 = x23 * u03
    have hm := minor_overlap_identity
      (x 1) (x 2) (x 3) (x 0) (y 1) (y 2) (y 3) (y 0)
      (u 1) (u 2) (u 3) (u 0) (v 1) (v 2) (v 3) (v 0)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination -hm
  · -- (4, 5): x13 * u01 = x23 * (-u02)
    have hm := minor_overlap_identity
      (x 1) (x 3) (x 2) (x 0) (y 1) (y 3) (y 2) (y 0)
      (u 1) (u 3) (u 2) (u 0) (v 1) (v 3) (v 2) (v 0)
      (by linear_combination sux) (by linear_combination suy)
      (by linear_combination svx) (by linear_combination svy)
    linear_combination -hm

/-- All fifteen `2 × 2` minors between ray coordinates of two points `x, y` and
axis-dual coordinates of two planes `u, v` vanish whenever each point lies on each plane
(`Plücker Nos. 4–8`, `pp. 26–29`). -/
theorem ray_axis_minors_eq_of_four_incidences {R : Type*} [CommRing R] (x y u v : Fin 4 → R)
    (hux : ∑ k, u k * x k = 0) (huy : ∑ k, u k * y k = 0)
    (hvx : ∑ k, v k * x k = 0) (hvy : ∑ k, v k * y k = 0)
    (i j : Fin 6) :
    coordinates (rayPlucker x y) i * coordinates (axisAsRayPlucker u v) j =
      coordinates (rayPlucker x y) j * coordinates (axisAsRayPlucker u v) i := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact ray_axis_minors_lt x y u v hux huy hvx hvy hij
  · ring
  · exact (ray_axis_minors_lt x y u v hux huy hvx hvy hij).symm

/-- Over any field, four incidences `u·x = u·y = v·x = v·y = 0` imply ray coordinates and
axis-dual coordinates are proportional as elements of `ℙ⁵`. -/
theorem ray_axis_proportional_of_four_incidences {K : Type*} [Field K] (x y u v : Fin 4 → K)
    (hux : ∑ k, u k * x k = 0) (huy : ∑ k, u k * y k = 0)
    (hvx : ∑ k, v k * x k = 0) (hvy : ∑ k, v k * y k = 0)
    (j₀ : Fin 6) (hj₀ : coordinates (axisAsRayPlucker u v) j₀ ≠ 0) :
    ∃ c : K, ∀ i : Fin 6,
      coordinates (rayPlucker x y) i = c * coordinates (axisAsRayPlucker u v) i := by
  refine ⟨coordinates (rayPlucker x y) j₀ / coordinates (axisAsRayPlucker u v) j₀, fun i => ?_⟩
  have h := ray_axis_minors_eq_of_four_incidences x y u v hux huy hvx hvy i j₀
  field_simp [hj₀]
  exact h

end RayAxisDuality

section ConjugateImaginaryAndCovariance

/-- Lift a real Plücker 6-vector into `ℂ`. -/
def realToComplexPlucker (P : KleinQuadric.Plucker6 ℝ) : KleinQuadric.Plucker6 ℂ where
  p01 := (P.p01 : ℂ)
  p02 := (P.p02 : ℂ)
  p03 := (P.p03 : ℂ)
  p12 := (P.p12 : ℂ)
  p13 := (P.p13 : ℂ)
  p23 := (P.p23 : ℂ)

/-- Real-part projection of a complex Plücker 6-vector. -/
def rePlucker (P : KleinQuadric.Plucker6 ℂ) : KleinQuadric.Plucker6 ℝ where
  p01 := P.p01.re
  p02 := P.p02.re
  p03 := P.p03.re
  p12 := P.p12.re
  p13 := P.p13.re
  p23 := P.p23.re

/-- Imaginary-part projection of a complex Plücker 6-vector. -/
def imPlucker (P : KleinQuadric.Plucker6 ℂ) : KleinQuadric.Plucker6 ℝ where
  p01 := P.p01.im
  p02 := P.p02.im
  p03 := P.p03.im
  p12 := P.p12.im
  p13 := P.p13.im
  p23 := P.p23.im

/-- Entrywise complex conjugate of a complex Plücker 6-vector. -/
def conjPlucker (P : KleinQuadric.Plucker6 ℂ) : KleinQuadric.Plucker6 ℂ where
  p01 := starRingEnd ℂ P.p01
  p02 := starRingEnd ℂ P.p02
  p03 := starRingEnd ℂ P.p03
  p12 := starRingEnd ℂ P.p12
  p13 := starRingEnd ℂ P.p13
  p23 := starRingEnd ℂ P.p23

/-- A conjugate-imaginary pair of points `a ± i b` joins along `-2 i` times the real ray
joining `a` and `b` (`Plücker Nos. 14–16`, `p. 34`). -/
theorem rayPlucker_conj_line (a b : Fin 4 → ℝ) :
    rayPlucker (fun i => (a i : ℂ) + Complex.I * (b i : ℂ))
      (fun i => (a i : ℂ) - Complex.I * (b i : ℂ)) =
      Plucker6.scale (-2 * Complex.I) (realToComplexPlucker (rayPlucker a b)) := by
  ext <;> apply Complex.ext <;>
    simp [rayPlucker, Plucker6.scale, realToComplexPlucker] <;> ring

/-- For any complex line `P`, its real mutual invariant with its complex conjugate `P̄` equals
`2 ((Re P).kleinQ + (Im P).kleinQ)`, which vanishes iff `P` is a complex line of the first kind
(carrying a real line / intersecting its conjugate) (`No. 16`). -/
theorem polar_conjPlucker_eq (P : KleinQuadric.Plucker6 ℂ) :
    P.polar (conjPlucker P) =
      (((2 * ((rePlucker P).kleinQ + (imPlucker P).kleinQ)) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [Plucker6.polar, Plucker6.add, Plucker6.kleinQ, conjPlucker, rePlucker, imPlucker]
    ring
  · simp [Plucker6.polar, Plucker6.add, Plucker6.kleinQ, conjPlucker, rePlucker, imPlucker]
    ring

private lemma crossProduct_coord (a b : Vec3) :
    crossProduct a b 0 = a 1 * b 2 - a 2 * b 1 ∧
      crossProduct a b 1 = a 2 * b 0 - a 0 * b 2 ∧
      crossProduct a b 2 = a 0 * b 1 - a 1 * b 0 :=
  ⟨rfl, rfl, rfl⟩

private lemma dotProduct_fin3 (a b : Vec3) :
    a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  rw [dotProduct, Fin.sum_univ_three]

/-- Affine translation of 3D direction–moment coordinates shifts the moment by `t × d` and
leaves `d ⬝ᵥ m` invariant (`Plücker Nos. 17–24`, `p. 37`). -/
def affineTranslateDirMom (t : Vec3) (p : Vec3 × Vec3) : Vec3 × Vec3 :=
  (p.1, p.2 + crossProduct t p.1)

theorem affineTranslateDirMom_dot_invariant (t d m : Vec3) :
    (affineTranslateDirMom t (d, m)).1 ⬝ᵥ (affineTranslateDirMom t (d, m)).2 = d ⬝ᵥ m := by
  rcases crossProduct_coord t d with ⟨hc0, hc1, hc2⟩
  simp only [affineTranslateDirMom, dotProduct_fin3, Pi.add_apply, hc0, hc1, hc2]
  ring

theorem affineTranslateDirMom_kleinQ_invariant (t d m : Vec3) :
    (directionMomentEquiv.symm (affineTranslateDirMom t (d, m))).kleinQ =
      (directionMomentEquiv.symm (d, m)).kleinQ := by
  rw [kleinQ_directionMoment, kleinQ_directionMoment, affineTranslateDirMom_dot_invariant]

/-- Embed a `3 × 3` orthogonal matrix `Q` into a `4 × 4` block projective transformation fixing `x₀`. -/
def embedLinear3IntoFin4 {R : Type*} [Ring R] (Q : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => Q i' j') j) i

theorem rotation_dot_invariant (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Qᵀ * Q = 1) (d m : Vec3) :
    (Q *ᵥ d) ⬝ᵥ (Q *ᵥ m) = d ⬝ᵥ m := by
  rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hQ,
    Matrix.vecMul_one]

/-- Homogeneous functions of degree `n` on `K⁴` preserve exact homogeneous degree `n` under every
linear transformation (projective invariance of complex cones and conics, `No. 18`). -/
def IsHomogeneousDeg {R : Type*} [CommRing R] (n : ℕ) (F : (Fin 4 → R) → R) : Prop :=
  ∀ (c : R) (x : Fin 4 → R), F (c • x) = c ^ n * F x

theorem homogeneousFun_comp_linear {R : Type*} [CommRing R] (n : ℕ)
    (F : (Fin 4 → R) → R) (hF : IsHomogeneousDeg n F) (A : Matrix (Fin 4) (Fin 4) R) :
    IsHomogeneousDeg n (fun x => F (A *ᵥ x)) := by
  intro c x
  simpa [Matrix.mulVec_smul] using hF c (A *ᵥ x)

end ConjugateImaginaryAndCovariance

section DynameAndForceSplitting

/-- A sum of two Plücker 6-vectors has Klein quadratic form equal to the sum of their Klein forms
plus their mutual polar invariant (`Plücker §2, Nos. 17–25`, `pp. 37–44`). -/
theorem dyname_add_kleinQ {R : Type*} [CommRing R] (P Q : KleinQuadric.Plucker6 R) :
    (P.add Q).kleinQ = P.kleinQ + Q.kleinQ + P.polar Q := by
  dsimp [Plucker6.polar]
  ring

/-- The resultant of two single forces `P, Q` (both on the Klein quadric) is again a single force
iff their lines of action are incident (`Plücker No. 22`). -/
theorem dyname_isKlein_iff_incident_of_forces {R : Type*} [CommRing R]
    {P Q : KleinQuadric.Plucker6 R} (hP : P.IsKlein) (hQ : Q.IsKlein) :
    (P.add Q).IsKlein ↔ P.Incident Q := by
  rw [Plucker6.IsKlein, Plucker6.Incident, dyname_add_kleinQ, hP, hQ, zero_add, zero_add]

private lemma vec3_dot_self_eq_zero_iff (v : Vec3) : v ⬝ᵥ v = 0 → v = 0 := by
  intro h0
  rw [dotProduct_fin3] at h0
  have hv0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have hv2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  ext i
  fin_cases i <;> assumption

private lemma orthogonal_vec3_exists (m : Vec3) :
    ∃ u : Vec3, u ≠ 0 ∧ m ⬝ᵥ u = 0 := by
  by_cases h01 : m 0 = 0 ∧ m 1 = 0
  · refine ⟨![1, 0, 0], ?_, ?_⟩
    · intro h
      have h0 : (1 : ℝ) = 0 := by simpa using congrFun h 0
      norm_num at h0
    · rw [dotProduct_fin3]
      change m 0 * 1 + m 1 * 0 + m 2 * 0 = 0
      simp [h01.1]
  · refine ⟨![-m 1, m 0, 0], ?_, ?_⟩
    · intro h
      have h0 : -m 1 = 0 := by simpa using congrFun h 0
      have h1 : m 0 = 0 := by simpa using congrFun h 1
      exact h01 ⟨h1, by linarith⟩
    · rw [dotProduct_fin3]
      change m 0 * (-m 1) + m 1 * m 0 + m 2 * 0 = 0
      ring

private lemma crossProduct_self_dot (a b : Vec3) :
    (crossProduct a b) ⬝ᵥ a = 0 := by
  rcases crossProduct_coord a b with ⟨hc0, hc1, hc2⟩
  rw [dotProduct_fin3, hc0, hc1, hc2]
  ring

private lemma crossProduct_eq_zero_dot_self {m u : Vec3} (hm : m ≠ 0) (hu : u ≠ 0)
    (hmu : m ⬝ᵥ u = 0) :
    crossProduct m u ≠ 0 := by
  intro hzero
  have hm2 : m ⬝ᵥ m ≠ 0 := fun h0 => hm (vec3_dot_self_eq_zero_iff m h0)
  have hu2 : u ⬝ᵥ u ≠ 0 := fun h0 => hu (vec3_dot_self_eq_zero_iff u h0)
  rcases crossProduct_coord m u with ⟨hc0, hc1, hc2⟩
  have hid :
      (crossProduct m u) ⬝ᵥ (crossProduct m u) =
        (m ⬝ᵥ m) * (u ⬝ᵥ u) - (m ⬝ᵥ u) ^ 2 := by
    simp only [dotProduct_fin3, hc0, hc1, hc2]
    ring
  rw [hzero, hmu] at hid
  simp only [dotProduct_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at hid
  exact (mul_ne_zero hm2 hu2) hid.symm

private lemma two_smul_crossProduct_orthogonal {m u : Vec3} (hmu : m ⬝ᵥ u = 0)
    (hu2 : u ⬝ᵥ u ≠ 0) :
    let e : Vec3 := ((2 * (u ⬝ᵥ u))⁻¹) • crossProduct m u
    (crossProduct u e + crossProduct u e) = m := by
  intro e
  have hmu' : m 0 * u 0 + m 1 * u 1 + m 2 * u 2 = 0 := by
    simpa [dotProduct_fin3] using hmu
  let D : ℝ := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2
  have hDeq : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = D := by simp only [D]; ring
  have hD : D ≠ 0 := by
    intro h0
    apply hu2
    rw [dotProduct_fin3, hDeq, h0]
  rcases crossProduct_coord u e with ⟨hue0, hue1, hue2⟩
  rcases crossProduct_coord m u with ⟨hmu0, hmu1, hmu2⟩
  have he0 : e 0 = (2 * D)⁻¹ * (m 1 * u 2 - m 2 * u 1) := by
    simp [e, dotProduct_fin3, hDeq, hmu0]
  have he1 : e 1 = (2 * D)⁻¹ * (m 2 * u 0 - m 0 * u 2) := by
    simp [e, dotProduct_fin3, hDeq, hmu1]
  have he2 : e 2 = (2 * D)⁻¹ * (m 0 * u 1 - m 1 * u 0) := by
    simp [e, dotProduct_fin3, hDeq, hmu2]
  ext i
  fin_cases i
  · change crossProduct u e 0 + crossProduct u e 0 = m 0
    rw [hue0, he1, he2]; field_simp [hD]; simp only [D]; linear_combination -2 * u 0 * hmu'
  · change crossProduct u e 1 + crossProduct u e 1 = m 1
    rw [hue1, he0, he2]; field_simp [hD]; simp only [D]; linear_combination -2 * u 1 * hmu'
  · change crossProduct u e 2 + crossProduct u e 2 = m 2
    rw [hue2, he0, he1]; field_simp [hD]; simp only [D]; linear_combination -2 * u 2 * hmu'

private lemma crossProduct_self_dot_right (a b : Vec3) :
    (crossProduct a b) ⬝ᵥ b = 0 := by
  rcases crossProduct_coord a b with ⟨hc0, hc1, hc2⟩
  rw [dotProduct_fin3, hc0, hc1, hc2]
  ring

private lemma splitForces_props (d m u : Vec3) (hmu : m ⬝ᵥ u = 0) (hu2 : u ⬝ᵥ u ≠ 0) :
    let e : Vec3 := ((2 * (u ⬝ᵥ u))⁻¹) • crossProduct m u
    let d₁ := ((2 : ℝ)⁻¹) • d + e
    let d₂ := ((2 : ℝ)⁻¹) • d - e
    let m₁ := crossProduct u d₁
    let m₂ := crossProduct (-u) d₂
    d₁ ⬝ᵥ m₁ = 0 ∧ d₂ ⬝ᵥ m₂ = 0 ∧ d₁ + d₂ = d ∧ m₁ + m₂ = m := by
  intro e d₁ d₂ m₁ m₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dotProduct_comm]; exact crossProduct_self_dot_right u d₁
  · rw [dotProduct_comm]; exact crossProduct_self_dot_right (-u) d₂
  · ext i; simp only [d₁, d₂, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  · have hlin : m₁ + m₂ = crossProduct u e + crossProduct u e := by
      rcases crossProduct_coord u d₁ with ⟨h10, h11, h12⟩
      rcases crossProduct_coord (-u) d₂ with ⟨h20, h21, h22⟩
      rcases crossProduct_coord u e with ⟨he0, he1, he2⟩
      ext i
      fin_cases i
      · change m₁ 0 + m₂ 0 = crossProduct u e 0 + crossProduct u e 0
        dsimp only [m₁, m₂]; rw [h10, h20, he0]
        simp [d₁, d₂]; ring
      · change m₁ 1 + m₂ 1 = crossProduct u e 1 + crossProduct u e 1
        dsimp only [m₁, m₂]; rw [h11, h21, he1]
        simp [d₁, d₂]; ring
      · change m₁ 2 + m₂ 2 = crossProduct u e 2 + crossProduct u e 2
        dsimp only [m₁, m₂]; rw [h12, h22, he2]
        simp [d₁, d₂]; ring
    rw [hlin]
    exact two_smul_crossProduct_orthogonal hmu hu2

/-- Every nonzero real dyname `(d, m)` decomposes into the sum of two finite forces
`(d₁, m₁)` and `(d₂, m₂)` with `d₁ ≠ 0`, `d₂ ≠ 0`, `d₁ ⬝ᵥ m₁ = 0`, and `d₂ ⬝ᵥ m₂ = 0`
(`Plücker No. 23`, `p. 43`). -/
theorem exists_two_finite_forces_for_dyname (d m : Vec3) (hdm : d ≠ 0 ∨ m ≠ 0) :
    ∃ (d₁ m₁ d₂ m₂ : Vec3),
      d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ d₁ ⬝ᵥ m₁ = 0 ∧ d₂ ⬝ᵥ m₂ = 0 ∧
      d₁ + d₂ = d ∧ m₁ + m₂ = m := by
  by_cases hm : m = 0
  · subst hm
    have hd : d ≠ 0 := hdm.elim id fun h => absurd rfl h
    refine ⟨((2 : ℝ)⁻¹) • d, 0, ((2 : ℝ)⁻¹) • d, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact smul_ne_zero (by norm_num) hd
    · exact smul_ne_zero (by norm_num) hd
    · simp
    · simp
    · ext i; simp; ring
    · simp
  · rcases orthogonal_vec3_exists m with ⟨u₀, hu₀_ne, hmu₀⟩
    have hu₀_sq : u₀ ⬝ᵥ u₀ ≠ 0 := fun h0 => hu₀_ne (vec3_dot_self_eq_zero_iff u₀ h0)
    let e₁ : Vec3 := ((2 * (u₀ ⬝ᵥ u₀))⁻¹) • crossProduct m u₀
    have he₁_ne : e₁ ≠ 0 :=
      smul_ne_zero (inv_ne_zero (mul_ne_zero (by norm_num) hu₀_sq))
        (crossProduct_eq_zero_dot_self hm hu₀_ne hmu₀)
    by_cases hgood1 : ((2 : ℝ)⁻¹) • d + e₁ ≠ 0 ∧ ((2 : ℝ)⁻¹) • d - e₁ ≠ 0
    · rcases splitForces_props d m u₀ hmu₀ hu₀_sq with ⟨h1, h2, h3, h4⟩
      exact ⟨((2 : ℝ)⁻¹) • d + e₁, crossProduct u₀ (((2 : ℝ)⁻¹) • d + e₁),
        ((2 : ℝ)⁻¹) • d - e₁, crossProduct (-u₀) (((2 : ℝ)⁻¹) • d - e₁),
        hgood1.1, hgood1.2, h1, h2, h3, h4⟩
    · by_cases hd : d = 0
      · exfalso
        apply hgood1
        rw [hd, smul_zero, zero_add, zero_sub]
        exact ⟨he₁_ne, neg_ne_zero.mpr he₁_ne⟩
      · have he1_pm : e₁ = -(((2 : ℝ)⁻¹) • d) ∨ e₁ = ((2 : ℝ)⁻¹) • d := by
          by_cases ha : ((2 : ℝ)⁻¹) • d + e₁ = 0
          · left; exact eq_neg_of_add_eq_zero_right ha
          · have hb : ((2 : ℝ)⁻¹) • d - e₁ = 0 := by tauto
            right; exact (sub_eq_zero.mp hb).symm
        let u₂ : Vec3 := (2 : ℝ) • u₀
        have hmu₂ : m ⬝ᵥ u₂ = 0 := by simp [u₂, dotProduct_smul, hmu₀]
        have hu₂_sq : u₂ ⬝ᵥ u₂ ≠ 0 := by
          have : u₂ ⬝ᵥ u₂ = 4 * (u₀ ⬝ᵥ u₀) := by
            simp [u₂, dotProduct_smul, smul_dotProduct]; ring
          rw [this]
          exact mul_ne_zero (by norm_num) hu₀_sq
        rcases splitForces_props d m u₂ hmu₂ hu₂_sq with ⟨h1, h2, h3, h4⟩
        let e₂ : Vec3 := ((2 * (u₂ ⬝ᵥ u₂))⁻¹) • crossProduct m u₂
        have he₂_half : e₂ = ((2 : ℝ)⁻¹) • e₁ := by
          have hsq : u₂ ⬝ᵥ u₂ = 4 * (u₀ ⬝ᵥ u₀) := by
            simp [u₂, dotProduct_smul, smul_dotProduct]; ring
          have hu₀_sum : u₀ 0 * u₀ 0 + u₀ 1 * u₀ 1 + u₀ 2 * u₀ 2 ≠ 0 := by
            simpa [dotProduct_fin3] using hu₀_sq
          rcases crossProduct_coord m u₀ with ⟨hcm0, hcm1, hcm2⟩
          rcases crossProduct_coord m u₂ with ⟨hc₂0, hc₂1, hc₂2⟩
          ext i
          fin_cases i
          · change ((2 * (u₂ ⬝ᵥ u₂))⁻¹ * crossProduct m u₂ 0) =
              (2 : ℝ)⁻¹ * ((2 * (u₀ ⬝ᵥ u₀))⁻¹ * crossProduct m u₀ 0)
            rw [hsq, dotProduct_fin3, hc₂0, hcm0]
            simp only [u₂, Pi.smul_apply, smul_eq_mul]
            field_simp [hu₀_sum]; ring
          · change ((2 * (u₂ ⬝ᵥ u₂))⁻¹ * crossProduct m u₂ 1) =
              (2 : ℝ)⁻¹ * ((2 * (u₀ ⬝ᵥ u₀))⁻¹ * crossProduct m u₀ 1)
            rw [hsq, dotProduct_fin3, hc₂1, hcm1]
            simp only [u₂, Pi.smul_apply, smul_eq_mul]
            field_simp [hu₀_sum]; ring
          · change ((2 * (u₂ ⬝ᵥ u₂))⁻¹ * crossProduct m u₂ 2) =
              (2 : ℝ)⁻¹ * ((2 * (u₀ ⬝ᵥ u₀))⁻¹ * crossProduct m u₀ 2)
            rw [hsq, dotProduct_fin3, hc₂2, hcm2]
            simp only [u₂, Pi.smul_apply, smul_eq_mul]
            field_simp [hu₀_sum]; ring
        have hpos1 : ((2 : ℝ)⁻¹) • d + e₂ ≠ 0 := by
          rcases he1_pm with heq | heq <;> rw [he₂_half, heq]
          · have : ((2 : ℝ)⁻¹) • d + ((2 : ℝ)⁻¹) • (-(((2 : ℝ)⁻¹) • d)) = ((4 : ℝ)⁻¹) • d := by
              ext i; simp; ring
            rw [this]; exact smul_ne_zero (by norm_num) hd
          · have : ((2 : ℝ)⁻¹) • d + ((2 : ℝ)⁻¹) • (((2 : ℝ)⁻¹) • d) = ((3 / 4 : ℝ)) • d := by
              ext i; simp; ring
            rw [this]; exact smul_ne_zero (by norm_num) hd
        have hpos2 : ((2 : ℝ)⁻¹) • d - e₂ ≠ 0 := by
          rcases he1_pm with heq | heq <;> rw [he₂_half, heq]
          · have : ((2 : ℝ)⁻¹) • d - ((2 : ℝ)⁻¹) • (-(((2 : ℝ)⁻¹) • d)) = ((3 / 4 : ℝ)) • d := by
              ext i; simp; ring
            rw [this]; exact smul_ne_zero (by norm_num) hd
          · have : ((2 : ℝ)⁻¹) • d - ((2 : ℝ)⁻¹) • (((2 : ℝ)⁻¹) • d) = ((4 : ℝ)⁻¹) • d := by
              ext i; simp; ring
            rw [this]; exact smul_ne_zero (by norm_num) hd
        exact ⟨((2 : ℝ)⁻¹) • d + e₂, crossProduct u₂ (((2 : ℝ)⁻¹) • d + e₂),
          ((2 : ℝ)⁻¹) • d - e₂, crossProduct (-u₂) (((2 : ℝ)⁻¹) • d - e₂),
          hpos1, hpos2, h1, h2, h3, h4⟩

end DynameAndForceSplitting

section LinearComplexConjugacyAndUniqueness

/-- Conjugate polar line of `P` with respect to a linear complex `C` (`Plücker Nos. 30–36`). -/
def conjugatePolar {R : Type*} [CommRing R] (C P : KleinQuadric.Plucker6 R) :
    KleinQuadric.Plucker6 R :=
  axisDualEquiv (PluckerMatrixAction.transform (PluckerLinearComplex.complexMatrix C) P)

/-- Exact null-system formula: the conjugate polar of `P` wrt `C` equals `(C.polar P) • C - C.kleinQ • P`
(`Plücker Abth. I §1, Eqs. (32)–(36)`). -/
theorem conjugatePolar_eq {R : Type*} [CommRing R] (C P : KleinQuadric.Plucker6 R) :
    conjugatePolar C P =
      (Plucker6.scale (C.polar P) C).add (Plucker6.scale (-C.kleinQ) P) := by
  apply coordinates.injective
  ext i
  fin_cases i <;>
    simp [conjugatePolar, axisDualEquiv, PluckerMatrixAction.transform,
      PluckerLinearComplex.complexMatrix, InfoGeometry.Canonical.Pfaffian.skew4,
      PluckerMatrixAction.secondCompound, PluckerMatrixAction.coordinatePair,
      PluckerMatrixAction.coordinates, Plucker6.polar, Plucker6.add, Plucker6.scale,
      Plucker6.kleinQ, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;>
    ring

theorem conjugatePolar_polar {R : Type*} [CommRing R] (C P : KleinQuadric.Plucker6 R) :
    C.polar (conjugatePolar C P) = C.kleinQ * C.polar P := by
  rw [conjugatePolar_eq]
  simp [Plucker6.polar, Plucker6.add, Plucker6.scale, Plucker6.kleinQ]
  ring

theorem conjugatePolar_involutive_up_to_scale {R : Type*} [CommRing R]
    (C P : KleinQuadric.Plucker6 R) :
    conjugatePolar C (conjugatePolar C P) = Plucker6.scale (C.kleinQ ^ 2) P := by
  rw [conjugatePolar_eq, conjugatePolar_polar, conjugatePolar_eq]
  ext <;> simp [Plucker6.add, Plucker6.scale] <;> ring

theorem conjugatePolar_kleinQ {R : Type*} [CommRing R] (C P : KleinQuadric.Plucker6 R) :
    (conjugatePolar C P).kleinQ = C.kleinQ ^ 2 * P.kleinQ := by
  rw [conjugatePolar_eq]
  simp [Plucker6.add, Plucker6.scale, Plucker6.polar, Plucker6.kleinQ]
  ring

/-- Involutive anti-diagonal sign matrix representing the Klein incidence bilinear form `C.polar P`
on `Fin 6 → R` (`polarDotMatrix *ᵥ coordinates P`). -/
def polarDotMatrix {R : Type*} [CommRing R] : Matrix (Fin 6) (Fin 6) R :=
  ![ ![0, 0, 0, 0, 0, 1],
     ![0, 0, 0, 0, -1, 0],
     ![0, 0, 0, 1, 0, 0],
     ![0, 0, 1, 0, 0, 0],
     ![0, -1, 0, 0, 0, 0],
     ![1, 0, 0, 0, 0, 0] ]

theorem polar_eq_vec_dot_mulVec {R : Type*} [CommRing R] (C P : KleinQuadric.Plucker6 R) :
    C.polar P = coordinates C ⬝ᵥ (polarDotMatrix *ᵥ coordinates P) := by
  simp [Plucker6.polar, Plucker6.add, Plucker6.kleinQ, polarDotMatrix,
    coordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  ring

theorem polarDotMatrix_mul_self {R : Type*} [CommRing R] :
    (polarDotMatrix : Matrix (Fin 6) (Fin 6) R) * polarDotMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Matrix.mul_apply, Fin.sum_univ_six]; simp [polarDotMatrix])

theorem polarDotMatrix_mulVec_injective {R : Type*} [CommRing R] :
    Function.Injective (Matrix.mulVecLin (polarDotMatrix : Matrix (Fin 6) (Fin 6) R)) := by
  intro x y hxy
  have h := congrArg (fun v => (polarDotMatrix : Matrix (Fin 6) (Fin 6) R) *ᵥ v) hxy
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, polarDotMatrix_mul_self] using h

/-- Evaluation map assigning to a linear complex `C` its incidence bilinear forms with 5 given
Plücker vectors `L : Fin 5 → Plucker6 K`. -/
noncomputable def fiveLineEvalMap {K : Type*} [Field K] (L : Fin 5 → KleinQuadric.Plucker6 K) :
    (Fin 6 → K) →ₗ[K] (Fin 5 → K) where
  toFun c i := c ⬝ᵥ (polarDotMatrix *ᵥ coordinates (L i))
  map_add' x y := by ext i; simp [add_dotProduct]
  map_smul' r x := by ext i; simp [smul_dotProduct]

/-- Five linearly independent lines determine a unique linear complex up to scale (`finrank = 1`)
(`Plücker No. 28`, `p. 47`). -/
theorem finrank_fiveLineComplexSubmodule {K : Type*} [Field K]
    (L : Fin 5 → KleinQuadric.Plucker6 K)
    (hL : LinearIndependent K (fun i => coordinates (L i))) :
    Module.finrank K (LinearMap.ker (fiveLineEvalMap L)) = 1 := by
  have hL_image : LinearIndependent K (fun i => polarDotMatrix *ᵥ coordinates (L i)) :=
    hL.map' (Matrix.mulVecLin polarDotMatrix)
      (LinearMap.ker_eq_bot.mpr polarDotMatrix_mulVec_injective)
  let M : Matrix (Fin 5) (Fin 6) K := Matrix.of (fun i => polarDotMatrix *ᵥ coordinates (L i))
  have hEvalEq : fiveLineEvalMap L = Matrix.mulVecLin M := by
    ext c i
    simp [fiveLineEvalMap, M, Matrix.mulVec, dotProduct_comm]
  have hKerMt : LinearMap.ker (Matrix.mulVecLin Mᵀ) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have hsub : Matrix.mulVecLin Mᵀ (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hsum : ∑ i : Fin 5, (x - y) i • (polarDotMatrix *ᵥ coordinates (L i)) = 0 := by
      ext j
      have hj : (Matrix.mulVec Mᵀ (x - y)) j = 0 := congrFun hsub j
      rw [Matrix.mulVec_transpose, Matrix.vecMul, dotProduct] at hj
      simpa [M, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj
    have hlin := (Fintype.linearIndependent_iff.mp hL_image) (x - y) hsum
    ext i
    exact sub_eq_zero.mp (hlin i)
  have hRankMt : Module.finrank K (LinearMap.range (Matrix.mulVecLin Mᵀ)) = 5 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin Mᵀ)
    rw [hKerMt, finrank_bot, add_zero, Module.finrank_fin_fun] at hrk
    exact hrk
  have hRankM : Module.finrank K (LinearMap.range (Matrix.mulVecLin M)) = 5 := by
    change M.rank = 5
    rw [← Matrix.rank_transpose]
    exact hRankMt
  have hRangeEq : LinearMap.range (fiveLineEvalMap L) = LinearMap.range (Matrix.mulVecLin M) := by
    rw [hEvalEq]
  have hRank := LinearMap.finrank_range_add_finrank_ker (fiveLineEvalMap L)
  rw [hRangeEq, hRankM, Module.finrank_fin_fun] at hRank
  omega

/-- Non-commutativity witness for the `6 × 6` Plücker transformation carrier `Matrix (Fin 6) (Fin 6) R`. -/
theorem matrix6_noncomm {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 6) (Fin 6) R, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

end LinearComplexConjugacyAndUniqueness

section CanonicalCentralAxis

/-- Canonical general linear complex whose central axis is the `z`-axis with parameter (pitch) `k`
(`Plücker Nos. 44–61`, `pp. 61–74`). -/
def canonicalCentralComplex (k : ℝ) : KleinQuadric.Plucker6 ℝ :=
  plucker6Equiv.symm (directionMomentEquiv.symm (![0, 0, 1], ![0, 0, k]))

theorem canonicalCentralComplex_kleinQ (k : ℝ) :
    (canonicalCentralComplex k).kleinQ = k := by
  simp [canonicalCentralComplex, plucker6Equiv, Plucker6.kleinQ,
    directionMomentEquiv]

/-- Plücker's central-axis slope formula: a finite line through `(r, 0, 0)` with direction `(0, dy, dz)`
belongs to `canonicalCentralComplex k` iff `r * dy + k * dz = 0`, i.e., the inclination angle satisfies
`dy / dz = -k / r` (`No. 46`, `p. 64`). -/
theorem canonicalCentralComplex_slope (k r dy dz : ℝ) :
    (canonicalCentralComplex k).Incident
        (rayPlucker ![1, r, 0, 0] ![1, r, dy, dz]) ↔
      r * dy + k * dz = 0 := by
  have hc : canonicalCentralComplex k = ⟨0, 0, 1, k, 0, 0⟩ := by
    ext <;> simp [canonicalCentralComplex, plucker6Equiv, directionMomentEquiv]
  have hr : rayPlucker ![1, r, 0, 0] ![1, r, dy, dz] = ⟨0, dy, dz, r * dy, r * dz, 0⟩ := by
    ext <;> simp [rayPlucker]
  rw [hc, hr]
  simp only [Plucker6.Incident, Plucker6.polar, Plucker6.add, Plucker6.kleinQ]
  constructor <;> intro h <;> linarith

end CanonicalCentralAxis

end InfoGeometry.Projective.PluckerRayAxisAndDyname
