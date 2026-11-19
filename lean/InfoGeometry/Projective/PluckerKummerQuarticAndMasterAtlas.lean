/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.PluckerQuadraticComplexAndSurfaces
import InfoGeometry.Projective.PluckerCongruenceCylindroidAndRegulus
import InfoGeometry.Projective.PluckerRayAxisAndDyname

/-!
# Singular Lines, Universal Kummer Quartic Surface, Equatorial Surfaces, and Master Atlas

This module formalizes Archetypes `PL₈` (`Abth. II §§4–6, Nos. 291–341`, plus
`Abth. III, Nos. 342–373`) and `PL₉` (Master Epistemic Causal Poset & Synthesis) of Julius
Plücker's *Neue Geometrie des Raumes* (`Liniengeometriev1.pdf`, pp. 275–378):

* Singular lines and double lines (`IsSingularLine`, `IsDoubleLine`, `isDoubleLine_implies_isSingularLine`).
* Universal chart-covariant Kummer `w²` factorization (`universal_kummer_w_sq_factorization`):
  for EVERY `4 × 3` affine point chart `k : Fin 4` and ANY `6 × 6` quadratic complex matrix `S`
  over any `CommRing R`, `det (coneChartMatrix S x k) = (x k) ^ 2 * kummerSingularQuartic S x`,
  proved via `binet_cauchy_3x6` applied twice, together with Klein-ambiguity invariance
  (`kummerSingularQuartic_add_klein`), degree-4 homogeneity, and point–plane self-duality
  (`kummer_plane_dual_duality`).
* Canonical 10-monomial Kummer quartic (`canonicalKummerQuartic`), invariance under the
  16-element `(ℤ₂³) ⋊ V₄` group (`canonicalKummerQuartic_group_invariant`), and a concrete
  rational 16-node Kummer surface with all 16 projectively distinct singular nodes verified
  (`kummer16Orbit_all_nodes`, `kummer16Orbit_pairwise_nonproportional`).
* Plücker sextic `Eq. (5.171)` → `w²` Kummer surface `Eq. (5.178)`, directional-derivative
  center coincidence, and `[countermodel_found]` `eq5183_printed_sign_erratum` (`p. 302`).
* Equatorial complex surfaces `ψ(x) y² + φ(x) z² - φ(x) ψ(x) = 0` (`Nos. 342–373`).
* `PL₉`: 9-node `PartialOrder PluckerNeueGeometrieArchetype` bitmask causal poset, explicit
  incomparability branching witnesses, and `plucker_neue_geometrie_master_synthesis`.
-/

namespace InfoGeometry.Projective.PluckerKummerQuarticAndMasterAtlas

open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Projective.PluckerAffineScrew
open InfoGeometry.Projective.PluckerRayAxisAndDyname
open InfoGeometry.Projective.PluckerCongruenceCylindroidAndRegulus
open InfoGeometry.Projective.PluckerQuadraticComplexAndSurfaces
open Matrix

section SingularAndDoubleLines

/-- Tangent complex 6-vector of quadratic form `S` at ray `P` (`Plücker Abth. II §4`). -/
def tangentComplexVec {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (P : KleinQuadric.Plucker6 R) : Fin 6 → R :=
  S *ᵥ coordinates P

/-- A line `P` of a quadratic complex `S` is singular (`No. 291`, `p. 275`) when `P.IsKlein`,
`Pᵀ S P = 0`, and the tangent linear complex `S *ᵥ P` lies on the dual Klein quadric
`(S P)ᵀ J (S P) = 0`. -/
def IsSingularLine {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (P : KleinQuadric.Plucker6 R) : Prop :=
  P.IsKlein ∧
    coordinates P ⬝ᵥ tangentComplexVec S P = 0 ∧
    tangentComplexVec S P ⬝ᵥ (polarDotMatrix *ᵥ tangentComplexVec S P) = 0

/-- A line `P` is a double line of `S` when `P.IsKlein` and `S *ᵥ coordinates P` is proportional
to the Klein polar `polarDotMatrix *ᵥ coordinates P` (`No. 299`). -/
def IsDoubleLine {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (P : KleinQuadric.Plucker6 R) : Prop :=
  P.IsKlein ∧ ∃ c : R, tangentComplexVec S P = c • (polarDotMatrix *ᵥ coordinates P)

theorem isDoubleLine_implies_isSingularLine {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (P : KleinQuadric.Plucker6 R)
    (hD : IsDoubleLine S P) : IsSingularLine S P := by
  rcases hD with ⟨hK, c, hc⟩
  have hpol : P.polar P = 2 * P.kleinQ := by
    simp [Plucker6.polar, Plucker6.add, Plucker6.kleinQ]; ring
  have hpdot : coordinates P ⬝ᵥ (polarDotMatrix *ᵥ coordinates P) = 2 * P.kleinQ := by
    rw [← polar_eq_vec_dot_mulVec, hpol]
  rw [Plucker6.IsKlein] at hK
  rw [hK, mul_zero] at hpdot
  refine ⟨hK, ?_, ?_⟩
  · rw [hc, dotProduct_smul, hpdot, smul_zero]
  · rw [hc, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      Matrix.mulVec_mulVec, polarDotMatrix_mul_self, Matrix.one_mulVec,
      dotProduct_comm, hpdot, smul_zero, smul_zero]

end SingularAndDoubleLines

section UniversalKummerFactorization

/-- Ascending `3`-element subsets of `Fin 6` (20 triples `(i, j, k)` with `i < j < k`). -/
def triple6 : Fin 20 → Fin 3 → Fin 6 :=
  ![ ![0, 1, 2], ![0, 1, 3], ![0, 1, 4], ![0, 1, 5],
     ![0, 2, 3], ![0, 2, 4], ![0, 2, 5], ![0, 3, 4], ![0, 3, 5], ![0, 4, 5],
     ![1, 2, 3], ![1, 2, 4], ![1, 2, 5], ![1, 3, 4], ![1, 3, 5], ![1, 4, 5],
     ![2, 3, 4], ![2, 3, 5], ![2, 4, 5], ![3, 4, 5] ]

/-- The 20 chart-covariant quadratic Plücker minor polynomials `ψ_t(x)` in the repository's
`(01, 02, 03, 12, 13, 23)` coordinate convention (of which `16` are nonzero). -/
def kummerPsi {R : Type*} [Ring R] (t : Fin 20) (x : Fin 4 → R) : R :=
  ![ x 0 ^ 2, 0, x 0 * x 1, x 0 * x 2, -(x 0 * x 1), 0, x 0 * x 3, x 1 ^ 2, x 1 * x 2, x 1 * x 3,
     -(x 0 * x 2), -(x 0 * x 3), 0, x 1 * x 2, x 2 ^ 2, x 2 * x 3, x 1 * x 3, x 2 * x 3,
     x 3 ^ 2, 0 ] t

/-- Basis vector `e_j : Fin 4 → R`. -/
private def stdBasis4 {R : Type*} [Ring R] (j : Fin 4) : Fin 4 → R :=
  fun i => if i = j then 1 else 0

/-- `6 × 3` ray chart matrix whose `c`-th column (`c : Fin 3`) is the Plücker vector joining
`x` to the reference vertex `e_{k.succAbove c}`. -/
def chartRayMatrix {R : Type*} [Ring R] (x : Fin 4 → R) (k : Fin 4) :
    Matrix (Fin 6) (Fin 3) R :=
  Matrix.of fun r c => coordinates (rayPlucker x (stdBasis4 (k.succAbove c))) r

/-- Quadratic complex cone `3 × 3` symmetric matrix on the `k`-th affine chart (`k : Fin 4`). -/
def coneChartMatrix {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (x : Fin 4 → R) (k : Fin 4) : Matrix (Fin 3) (Fin 3) R :=
  (chartRayMatrix x k)ᵀ * S * (chartRayMatrix x k)

/-- Universal Kummer singular surface quartic in homogeneous coordinates `x : Fin 4 → R`,
formed by Binet–Cauchy contraction of all `3 × 3` minors of `S` against `kummerPsi`. -/
def kummerSingularQuartic {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (x : Fin 4 → R) : R :=
  ∑ t : Fin 20, ∑ u : Fin 20,
    kummerPsi t x * (S.submatrix (triple6 t) (triple6 u)).det * kummerPsi u x

/-- Universal minor factorization lemma across all `4` affine charts (`80` total `3 × 3` minors):
`det (chartRayMatrix x k)[t, :] = (-1)^k * x k * kummerPsi t x`. -/
theorem chartRayMatrix_minor_eq {R : Type*} [CommRing R]
    (x : Fin 4 → R) (k : Fin 4) (t : Fin 20) :
    ((chartRayMatrix x k).submatrix (triple6 t) id).det =
      ((-1 : R) ^ (k : ℕ)) * x k * kummerPsi t x := by
  rw [Matrix.det_fin_three]
  fin_cases k <;> fin_cases t <;>
    simp [Matrix.submatrix_apply, chartRayMatrix, coordinates, rayPlucker, stdBasis4,
      triple6, kummerPsi, Fin.succAbove] <;>
    ring

/-- Auxiliary `2 × 6` Binet–Cauchy minor index list (`15` pairs `i < j`). -/
private def pair6 : Fin 15 → Fin 2 → Fin 6 :=
  ![ ![0, 1], ![0, 2], ![0, 3], ![0, 4], ![0, 5],
     ![1, 2], ![1, 3], ![1, 4], ![1, 5],
     ![2, 3], ![2, 4], ![2, 5],
     ![3, 4], ![3, 5],
     ![4, 5] ]

private lemma sum_univ_15 {R : Type*} [AddCommMonoid R] (f : Fin 15 → R) :
    ∑ p : Fin 15, f p =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 +
      f 10 + f 11 + f 12 + f 13 + f 14 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, ← add_assoc]
  rfl

private lemma sum_univ_20 {R : Type*} [AddCommMonoid R] (f : Fin 20 → R) :
    ∑ t : Fin 20, f t =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 +
      f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, ← add_assoc]
  rfl

private lemma binet_cauchy_2x6_scalar {R : Type*} [CommRing R]
    (a00 a01 a02 a03 a04 a05 a10 a11 a12 a13 a14 a15
     b00 b01 b02 b03 b04 b05 b10 b11 b12 b13 b14 b15 : R) :
    (a00 * b00 + a01 * b01 + a02 * b02 + a03 * b03 + a04 * b04 + a05 * b05) *
    (a10 * b10 + a11 * b11 + a12 * b12 + a13 * b13 + a14 * b14 + a15 * b15) -
    (a00 * b10 + a01 * b11 + a02 * b12 + a03 * b13 + a04 * b14 + a05 * b15) *
    (a10 * b00 + a11 * b01 + a12 * b02 + a13 * b03 + a14 * b04 + a15 * b05) =
      (a00 * a11 - a01 * a10) * (b00 * b11 - b01 * b10) +
      (a00 * a12 - a02 * a10) * (b00 * b12 - b02 * b10) +
      (a00 * a13 - a03 * a10) * (b00 * b13 - b03 * b10) +
      (a00 * a14 - a04 * a10) * (b00 * b14 - b04 * b10) +
      (a00 * a15 - a05 * a10) * (b00 * b15 - b05 * b10) +
      (a01 * a12 - a02 * a11) * (b01 * b12 - b02 * b11) +
      (a01 * a13 - a03 * a11) * (b01 * b13 - b03 * b11) +
      (a01 * a14 - a04 * a11) * (b01 * b14 - b04 * b11) +
      (a01 * a15 - a05 * a11) * (b01 * b15 - b05 * b11) +
      (a02 * a13 - a03 * a12) * (b02 * b13 - b03 * b12) +
      (a02 * a14 - a04 * a12) * (b02 * b14 - b04 * b12) +
      (a02 * a15 - a05 * a12) * (b02 * b15 - b05 * b12) +
      (a03 * a14 - a04 * a13) * (b03 * b14 - b04 * b13) +
      (a03 * a15 - a05 * a13) * (b03 * b15 - b05 * b13) +
      (a04 * a15 - a05 * a14) * (b04 * b15 - b05 * b14) := by
  ring

private lemma binet_cauchy_2x6 {R : Type*} [CommRing R]
    (A B : Matrix (Fin 2) (Fin 6) R) :
    (A * Bᵀ).det =
      ∑ p : Fin 15, (A.submatrix id (pair6 p)).det * (B.submatrix id (pair6 p)).det := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero, Matrix.submatrix_apply, id_eq, Matrix.det_fin_two, pair6]
  have hs := binet_cauchy_2x6_scalar
    (A 0 0) (A 0 1) (A 0 2) (A 0 3) (A 0 4) (A 0 5)
    (A 1 0) (A 1 1) (A 1 2) (A 1 3) (A 1 4) (A 1 5)
    (B 0 0) (B 0 1) (B 0 2) (B 0 3) (B 0 4) (B 0 5)
    (B 1 0) (B 1 1) (B 1 2) (B 1 3) (B 1 4) (B 1 5)
  convert hs using 1 <;> simp [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

private def bColDet {R : Type*} [CommRing R] (B : Matrix (Fin 3) (Fin 6) R)
    (k u v : Fin 6) : R :=
  B 0 k * (B 1 u * B 2 v - B 1 v * B 2 u) -
    B 1 k * (B 0 u * B 2 v - B 0 v * B 2 u) +
    B 2 k * (B 0 u * B 1 v - B 0 v * B 1 u)

private lemma bColDet_eq_triple {R : Type*} [CommRing R] (B : Matrix (Fin 3) (Fin 6) R)
    (i j l : Fin 6) :
    bColDet B i j l = (B.submatrix id ![i, j, l]).det := by
  rw [Matrix.det_fin_three]
  have c0 : (![i, j, l] : Fin 3 → Fin 6) 0 = i := rfl
  have c1 : (![i, j, l] : Fin 3 → Fin 6) 1 = j := rfl
  have c2 : (![i, j, l] : Fin 3 → Fin 6) 2 = l := rfl
  simp only [bColDet, Matrix.submatrix_apply, id_eq, c0, c1, c2]
  ring

private lemma binet_cofactor_scalar_group {R : Type*} [CommRing R]
    (a0 a1 a2 a3 a4 a5 : R)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 : R)
    (d012 d013 d014 d015 d023 d024 d025 d034 d035 d045
     d123 d124 d125 d134 d135 d145 d234 d235 d245 d345 : R) :
    m0 * (a2 * d012 + a3 * d013 + a4 * d014 + a5 * d015) +
    m1 * (-a1 * d012 + a3 * d023 + a4 * d024 + a5 * d025) +
    m2 * (-a1 * d013 - a2 * d023 + a4 * d034 + a5 * d035) +
    m3 * (-a1 * d014 - a2 * d024 - a3 * d034 + a5 * d045) +
    m4 * (-a1 * d015 - a2 * d025 - a3 * d035 - a4 * d045) +
    m5 * (a0 * d012 + a3 * d123 + a4 * d124 + a5 * d125) +
    m6 * (a0 * d013 - a2 * d123 + a4 * d134 + a5 * d135) +
    m7 * (a0 * d014 - a2 * d124 - a3 * d134 + a5 * d145) +
    m8 * (a0 * d015 - a2 * d125 - a3 * d135 - a4 * d145) +
    m9 * (a0 * d023 + a1 * d123 + a4 * d234 + a5 * d235) +
    m10 * (a0 * d024 + a1 * d124 - a3 * d234 + a5 * d245) +
    m11 * (a0 * d025 + a1 * d125 - a3 * d235 - a4 * d245) +
    m12 * (a0 * d034 + a1 * d134 + a2 * d234 + a5 * d345) +
    m13 * (a0 * d035 + a1 * d135 + a2 * d235 - a4 * d345) +
    m14 * (a0 * d045 + a1 * d145 + a2 * d245 + a3 * d345) =
      (a0 * m5 - a1 * m1 + a2 * m0) * d012 +
      (a0 * m6 - a1 * m2 + a3 * m0) * d013 +
      (a0 * m7 - a1 * m3 + a4 * m0) * d014 +
      (a0 * m8 - a1 * m4 + a5 * m0) * d015 +
      (a0 * m9 - a2 * m2 + a3 * m1) * d023 +
      (a0 * m10 - a2 * m3 + a4 * m1) * d024 +
      (a0 * m11 - a2 * m4 + a5 * m1) * d025 +
      (a0 * m12 - a3 * m3 + a4 * m2) * d034 +
      (a0 * m13 - a3 * m4 + a5 * m2) * d035 +
      (a0 * m14 - a4 * m4 + a5 * m3) * d045 +
      (a1 * m9 - a2 * m6 + a3 * m5) * d123 +
      (a1 * m10 - a2 * m7 + a4 * m5) * d124 +
      (a1 * m11 - a2 * m8 + a5 * m5) * d125 +
      (a1 * m12 - a3 * m7 + a4 * m6) * d134 +
      (a1 * m13 - a3 * m8 + a5 * m6) * d135 +
      (a1 * m14 - a4 * m8 + a5 * m7) * d145 +
      (a2 * m12 - a3 * m10 + a4 * m9) * d234 +
      (a2 * m13 - a3 * m11 + a5 * m9) * d235 +
      (a2 * m14 - a4 * m11 + a5 * m10) * d245 +
      (a3 * m14 - a4 * m13 + a5 * m12) * d345 := by
  ring

private lemma pairDet_eq_submatrix {R : Type*} [CommRing R]
    (A : Matrix (Fin 3) (Fin 6) R) (p : Fin 15) :
    ((Matrix.of fun (i : Fin 2) (j : Fin 6) => A i.succ j).submatrix id (pair6 p)).det =
      A 1 (pair6 p 0) * A 2 (pair6 p 1) - A 1 (pair6 p 1) * A 2 (pair6 p 0) := by
  rw [Matrix.det_fin_two]
  rfl

private lemma tripleDet_laplace_row0 {R : Type*} [CommRing R]
    (A : Matrix (Fin 3) (Fin 6) R) (i j l : Fin 6) :
    (A.submatrix id ![i, j, l]).det =
      A 0 i * (A 1 j * A 2 l - A 1 l * A 2 j) -
        A 0 j * (A 1 i * A 2 l - A 1 l * A 2 i) +
        A 0 l * (A 1 i * A 2 j - A 1 j * A 2 i) := by
  rw [Matrix.det_fin_three]
  have c0 : (![i, j, l] : Fin 3 → Fin 6) 0 = i := rfl
  have c1 : (![i, j, l] : Fin 3 → Fin 6) 1 = j := rfl
  have c2 : (![i, j, l] : Fin 3 → Fin 6) 2 = l := rfl
  simp only [Matrix.submatrix_apply, id_eq, c0, c1, c2]
  ring

private def pairCofactorSum {R : Type*} [Ring R] (a : Fin 6 → R) (d : Fin 20 → R) : Fin 15 → R :=
  ![ a 2 * d 0  + a 3 * d 1  + a 4 * d 2  + a 5 * d 3,
    -a 1 * d 0  + a 3 * d 4  + a 4 * d 5  + a 5 * d 6,
    -a 1 * d 1  - a 2 * d 4  + a 4 * d 7  + a 5 * d 8,
    -a 1 * d 2  - a 2 * d 5  - a 3 * d 7  + a 5 * d 9,
    -a 1 * d 3  - a 2 * d 6  - a 3 * d 8  - a 4 * d 9,
     a 0 * d 0  + a 3 * d 10 + a 4 * d 11 + a 5 * d 12,
     a 0 * d 1  - a 2 * d 10 + a 4 * d 13 + a 5 * d 14,
     a 0 * d 2  - a 2 * d 11 - a 3 * d 13 + a 5 * d 15,
     a 0 * d 3  - a 2 * d 12 - a 3 * d 14 - a 4 * d 15,
     a 0 * d 4  + a 1 * d 10 + a 4 * d 16 + a 5 * d 17,
     a 0 * d 5  + a 1 * d 11 - a 3 * d 16 + a 5 * d 18,
     a 0 * d 6  + a 1 * d 12 - a 3 * d 17 - a 4 * d 18,
     a 0 * d 7  + a 1 * d 13 + a 2 * d 16 + a 5 * d 19,
     a 0 * d 8  + a 1 * d 14 + a 2 * d 17 - a 4 * d 19,
     a 0 * d 9  + a 1 * d 15 + a 2 * d 18 + a 3 * d 19 ]

/-- `3 × 6` Binet–Cauchy formula proved cleanly by reducing to `binet_cauchy_2x6` via Laplace
cofactor expansion along row `0` and factoring the 15 minor coefficients. -/
theorem binet_cauchy_3x6 {R : Type*} [CommRing R]
    (A B : Matrix (Fin 3) (Fin 6) R) :
    (A * Bᵀ).det =
      ∑ t : Fin 20, (A.submatrix id (triple6 t)).det * (B.submatrix id (triple6 t)).det := by
  let A₂ : Matrix (Fin 2) (Fin 6) R := Matrix.of fun i j => A i.succ j
  let B0 : Matrix (Fin 2) (Fin 6) R := Matrix.of fun i j => B i.succ j
  let B1 : Matrix (Fin 2) (Fin 6) R := Matrix.of fun (i : Fin 2) j => B (if i = 0 then 0 else 2) j
  let B2 : Matrix (Fin 2) (Fin 6) R := Matrix.of fun (i : Fin 2) j => B (if i = 0 then 0 else 1) j
  have hA0 : ∀ j, A₂ 0 j = A 1 j := fun _ => rfl
  have hA1 : ∀ j, A₂ 1 j = A 2 j := fun _ => rfl
  have hB00 : ∀ j, B0 0 j = B 1 j := fun _ => rfl
  have hB01 : ∀ j, B0 1 j = B 2 j := fun _ => rfl
  have hB10 : ∀ j, B1 0 j = B 0 j := fun _ => rfl
  have hB11 : ∀ j, B1 1 j = B 2 j := fun _ => rfl
  have hB20 : ∀ j, B2 0 j = B 0 j := fun _ => rfl
  have hB21 : ∀ j, B2 1 j = B 1 j := fun _ => rfl
  have hDet :
      (A * Bᵀ).det =
        (∑ k : Fin 6, A 0 k * B 0 k) * (A₂ * B0ᵀ).det -
        (∑ k : Fin 6, A 0 k * B 1 k) * (A₂ * B1ᵀ).det +
        (∑ k : Fin 6, A 0 k * B 2 k) * (A₂ * B2ᵀ).det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_six,
      hA0, hA1, hB00, hB01, hB10, hB11, hB20, hB21]
    ring
  let M : Fin 15 → R := fun p => (A₂.submatrix id (pair6 p)).det
  have hB0 : ∀ p, (B0.submatrix id (pair6 p)).det =
      B 1 (pair6 p 0) * B 2 (pair6 p 1) - B 1 (pair6 p 1) * B 2 (pair6 p 0) := fun p => by
    rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, id_eq, hB00, hB01]
  have hB1 : ∀ p, (B1.submatrix id (pair6 p)).det =
      B 0 (pair6 p 0) * B 2 (pair6 p 1) - B 0 (pair6 p 1) * B 2 (pair6 p 0) := fun p => by
    rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, id_eq, hB10, hB11]
  have hB2 : ∀ p, (B2.submatrix id (pair6 p)).det =
      B 0 (pair6 p 0) * B 1 (pair6 p 1) - B 0 (pair6 p 1) * B 1 (pair6 p 0) := fun p => by
    rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, id_eq, hB20, hB21]
  have hLHS :
      (A * Bᵀ).det =
        ∑ p : Fin 15, M p * (∑ k : Fin 6, A 0 k * bColDet B k (pair6 p 0) (pair6 p 1)) := by
    rw [hDet, binet_cauchy_2x6 A₂ B0, binet_cauchy_2x6 A₂ B1, binet_cauchy_2x6 A₂ B2]
    simp only [hB0, hB1, hB2]
    change (∑ k : Fin 6, A 0 k * B 0 k) * (∑ p : Fin 15, M p *
            (B 1 (pair6 p 0) * B 2 (pair6 p 1) - B 1 (pair6 p 1) * B 2 (pair6 p 0))) -
        (∑ k : Fin 6, A 0 k * B 1 k) * (∑ p : Fin 15, M p *
            (B 0 (pair6 p 0) * B 2 (pair6 p 1) - B 0 (pair6 p 1) * B 2 (pair6 p 0))) +
        (∑ k : Fin 6, A 0 k * B 2 k) * (∑ p : Fin 15, M p *
            (B 0 (pair6 p 0) * B 1 (pair6 p 1) - B 0 (pair6 p 1) * B 1 (pair6 p 0))) =
          ∑ p : Fin 15, M p * (∑ k : Fin 6, A 0 k * bColDet B k (pair6 p 0) (pair6 p 1))
    have hswap0 : (∑ y : Fin 6, A 0 y * B 0 y) * (∑ p : Fin 15, M p *
        (B 1 (pair6 p 0) * B 2 (pair6 p 1) - B 1 (pair6 p 1) * B 2 (pair6 p 0))) =
        ∑ p : Fin 15, ∑ k : Fin 6, A 0 k * B 0 k *
          (M p * (B 1 (pair6 p 0) * B 2 (pair6 p 1) - B 1 (pair6 p 1) * B 2 (pair6 p 0))) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    have hswap1 : (∑ y : Fin 6, A 0 y * B 1 y) * (∑ p : Fin 15, M p *
        (B 0 (pair6 p 0) * B 2 (pair6 p 1) - B 0 (pair6 p 1) * B 2 (pair6 p 0))) =
        ∑ p : Fin 15, ∑ k : Fin 6, A 0 k * B 1 k *
          (M p * (B 0 (pair6 p 0) * B 2 (pair6 p 1) - B 0 (pair6 p 1) * B 2 (pair6 p 0))) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    have hswap2 : (∑ y : Fin 6, A 0 y * B 2 y) * (∑ p : Fin 15, M p *
        (B 0 (pair6 p 0) * B 1 (pair6 p 1) - B 0 (pair6 p 1) * B 1 (pair6 p 0))) =
        ∑ p : Fin 15, ∑ k : Fin 6, A 0 k * B 2 k *
          (M p * (B 0 (pair6 p 0) * B 1 (pair6 p 1) - B 0 (pair6 p 1) * B 1 (pair6 p 0))) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    rw [hswap0, hswap1, hswap2, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [bColDet]; ring
  rw [hLHS]
  let d : Fin 20 → R := fun t => (B.submatrix id (triple6 t)).det
  have hcol : ∀ t : Fin 20, d t = bColDet B (triple6 t 0) (triple6 t 1) (triple6 t 2) := fun t => by
    dsimp [d]
    have ht : ![triple6 t 0, triple6 t 1, triple6 t 2] = triple6 t := by
      ext c; fin_cases c <;> rfl
    rw [bColDet_eq_triple, ht]
  have hpair : ∀ p : Fin 15,
      ∑ k : Fin 6, A 0 k * bColDet B k (pair6 p 0) (pair6 p 1) =
        pairCofactorSum (A 0) d p := by
    have h0 : d 0 = bColDet B 0 1 2 := hcol 0
    have h1 : d 1 = bColDet B 0 1 3 := hcol 1
    have h2 : d 2 = bColDet B 0 1 4 := hcol 2
    have h3 : d 3 = bColDet B 0 1 5 := hcol 3
    have h4 : d 4 = bColDet B 0 2 3 := hcol 4
    have h5 : d 5 = bColDet B 0 2 4 := hcol 5
    have h6 : d 6 = bColDet B 0 2 5 := hcol 6
    have h7 : d 7 = bColDet B 0 3 4 := hcol 7
    have h8 : d 8 = bColDet B 0 3 5 := hcol 8
    have h9 : d 9 = bColDet B 0 4 5 := hcol 9
    have h10 : d 10 = bColDet B 1 2 3 := hcol 10
    have h11 : d 11 = bColDet B 1 2 4 := hcol 11
    have h12 : d 12 = bColDet B 1 2 5 := hcol 12
    have h13 : d 13 = bColDet B 1 3 4 := hcol 13
    have h14 : d 14 = bColDet B 1 3 5 := hcol 14
    have h15 : d 15 = bColDet B 1 4 5 := hcol 15
    have h16 : d 16 = bColDet B 2 3 4 := hcol 16
    have h17 : d 17 = bColDet B 2 3 5 := hcol 17
    have h18 : d 18 = bColDet B 2 4 5 := hcol 18
    have h19 : d 19 = bColDet B 3 4 5 := hcol 19
    intro p
    fin_cases p
    · change ∑ k : Fin 6, A 0 k * bColDet B k 0 1 = A 0 2 * d 0 + A 0 3 * d 1 + A 0 4 * d 2 + A 0 5 * d 3
      rw [Fin.sum_univ_six, h0, h1, h2, h3]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 0 2 = -A 0 1 * d 0 + A 0 3 * d 4 + A 0 4 * d 5 + A 0 5 * d 6
      rw [Fin.sum_univ_six, h0, h4, h5, h6]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 0 3 = -A 0 1 * d 1 - A 0 2 * d 4 + A 0 4 * d 7 + A 0 5 * d 8
      rw [Fin.sum_univ_six, h1, h4, h7, h8]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 0 4 = -A 0 1 * d 2 - A 0 2 * d 5 - A 0 3 * d 7 + A 0 5 * d 9
      rw [Fin.sum_univ_six, h2, h5, h7, h9]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 0 5 = -A 0 1 * d 3 - A 0 2 * d 6 - A 0 3 * d 8 - A 0 4 * d 9
      rw [Fin.sum_univ_six, h3, h6, h8, h9]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 1 2 = A 0 0 * d 0 + A 0 3 * d 10 + A 0 4 * d 11 + A 0 5 * d 12
      rw [Fin.sum_univ_six, h0, h10, h11, h12]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 1 3 = A 0 0 * d 1 - A 0 2 * d 10 + A 0 4 * d 13 + A 0 5 * d 14
      rw [Fin.sum_univ_six, h1, h10, h13, h14]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 1 4 = A 0 0 * d 2 - A 0 2 * d 11 - A 0 3 * d 13 + A 0 5 * d 15
      rw [Fin.sum_univ_six, h2, h11, h13, h15]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 1 5 = A 0 0 * d 3 - A 0 2 * d 12 - A 0 3 * d 14 - A 0 4 * d 15
      rw [Fin.sum_univ_six, h3, h12, h14, h15]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 2 3 = A 0 0 * d 4 + A 0 1 * d 10 + A 0 4 * d 16 + A 0 5 * d 17
      rw [Fin.sum_univ_six, h4, h10, h16, h17]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 2 4 = A 0 0 * d 5 + A 0 1 * d 11 - A 0 3 * d 16 + A 0 5 * d 18
      rw [Fin.sum_univ_six, h5, h11, h16, h18]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 2 5 = A 0 0 * d 6 + A 0 1 * d 12 - A 0 3 * d 17 - A 0 4 * d 18
      rw [Fin.sum_univ_six, h6, h12, h17, h18]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 3 4 = A 0 0 * d 7 + A 0 1 * d 13 + A 0 2 * d 16 + A 0 5 * d 19
      rw [Fin.sum_univ_six, h7, h13, h16, h19]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 3 5 = A 0 0 * d 8 + A 0 1 * d 14 + A 0 2 * d 17 - A 0 4 * d 19
      rw [Fin.sum_univ_six, h8, h14, h17, h19]; dsimp only [bColDet]; ring
    · change ∑ k : Fin 6, A 0 k * bColDet B k 4 5 = A 0 0 * d 9 + A 0 1 * d 15 + A 0 2 * d 18 + A 0 3 * d 19
      rw [Fin.sum_univ_six, h9, h15, h18, h19]; dsimp only [bColDet]; ring
  have hg := binet_cofactor_scalar_group
    (A 0 0) (A 0 1) (A 0 2) (A 0 3) (A 0 4) (A 0 5)
    (M 0) (M 1) (M 2) (M 3) (M 4) (M 5) (M 6) (M 7)
    (M 8) (M 9) (M 10) (M 11) (M 12) (M 13) (M 14)
    (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7) (d 8) (d 9)
    (d 10) (d 11) (d 12) (d 13) (d 14) (d 15) (d 16) (d 17) (d 18) (d 19)
  have hL_rew :
      ∑ p : Fin 15, M p * (∑ k : Fin 6, A 0 k * bColDet B k (pair6 p 0) (pair6 p 1)) =
      M 0 * (A 0 2 * d 0 + A 0 3 * d 1 + A 0 4 * d 2 + A 0 5 * d 3) +
      M 1 * (-A 0 1 * d 0 + A 0 3 * d 4 + A 0 4 * d 5 + A 0 5 * d 6) +
      M 2 * (-A 0 1 * d 1 - A 0 2 * d 4 + A 0 4 * d 7 + A 0 5 * d 8) +
      M 3 * (-A 0 1 * d 2 - A 0 2 * d 5 - A 0 3 * d 7 + A 0 5 * d 9) +
      M 4 * (-A 0 1 * d 3 - A 0 2 * d 6 - A 0 3 * d 8 - A 0 4 * d 9) +
      M 5 * (A 0 0 * d 0 + A 0 3 * d 10 + A 0 4 * d 11 + A 0 5 * d 12) +
      M 6 * (A 0 0 * d 1 - A 0 2 * d 10 + A 0 4 * d 13 + A 0 5 * d 14) +
      M 7 * (A 0 0 * d 2 - A 0 2 * d 11 - A 0 3 * d 13 + A 0 5 * d 15) +
      M 8 * (A 0 0 * d 3 - A 0 2 * d 12 - A 0 3 * d 14 - A 0 4 * d 15) +
      M 9 * (A 0 0 * d 4 + A 0 1 * d 10 + A 0 4 * d 16 + A 0 5 * d 17) +
      M 10 * (A 0 0 * d 5 + A 0 1 * d 11 - A 0 3 * d 16 + A 0 5 * d 18) +
      M 11 * (A 0 0 * d 6 + A 0 1 * d 12 - A 0 3 * d 17 - A 0 4 * d 18) +
      M 12 * (A 0 0 * d 7 + A 0 1 * d 13 + A 0 2 * d 16 + A 0 5 * d 19) +
      M 13 * (A 0 0 * d 8 + A 0 1 * d 14 + A 0 2 * d 17 - A 0 4 * d 19) +
      M 14 * (A 0 0 * d 9 + A 0 1 * d 15 + A 0 2 * d 18 + A 0 3 * d 19) := by
    simp only [hpair]
    rw [sum_univ_15]
    rfl
  have hM : ∀ p : Fin 15, M p =
      A 1 (pair6 p 0) * A 2 (pair6 p 1) - A 1 (pair6 p 1) * A 2 (pair6 p 0) :=
    pairDet_eq_submatrix A
  have hR_rew :
      (A 0 0 * M 5 - A 0 1 * M 1 + A 0 2 * M 0) * d 0 +
      (A 0 0 * M 6 - A 0 1 * M 2 + A 0 3 * M 0) * d 1 +
      (A 0 0 * M 7 - A 0 1 * M 3 + A 0 4 * M 0) * d 2 +
      (A 0 0 * M 8 - A 0 1 * M 4 + A 0 5 * M 0) * d 3 +
      (A 0 0 * M 9 - A 0 2 * M 2 + A 0 3 * M 1) * d 4 +
      (A 0 0 * M 10 - A 0 2 * M 3 + A 0 4 * M 1) * d 5 +
      (A 0 0 * M 11 - A 0 2 * M 4 + A 0 5 * M 1) * d 6 +
      (A 0 0 * M 12 - A 0 3 * M 3 + A 0 4 * M 2) * d 7 +
      (A 0 0 * M 13 - A 0 3 * M 4 + A 0 5 * M 2) * d 8 +
      (A 0 0 * M 14 - A 0 4 * M 4 + A 0 5 * M 3) * d 9 +
      (A 0 1 * M 9 - A 0 2 * M 6 + A 0 3 * M 5) * d 10 +
      (A 0 1 * M 10 - A 0 2 * M 7 + A 0 4 * M 5) * d 11 +
      (A 0 1 * M 11 - A 0 2 * M 8 + A 0 5 * M 5) * d 12 +
      (A 0 1 * M 12 - A 0 3 * M 7 + A 0 4 * M 6) * d 13 +
      (A 0 1 * M 13 - A 0 3 * M 8 + A 0 5 * M 6) * d 14 +
      (A 0 1 * M 14 - A 0 4 * M 8 + A 0 5 * M 7) * d 15 +
      (A 0 2 * M 12 - A 0 3 * M 10 + A 0 4 * M 9) * d 16 +
      (A 0 2 * M 13 - A 0 3 * M 11 + A 0 5 * M 9) * d 17 +
      (A 0 2 * M 14 - A 0 4 * M 11 + A 0 5 * M 10) * d 18 +
      (A 0 3 * M 14 - A 0 4 * M 13 + A 0 5 * M 12) * d 19 =
        ∑ t : Fin 20, (A.submatrix id (triple6 t)).det * (B.submatrix id (triple6 t)).det := by
    change _ = ∑ t : Fin 20, (A.submatrix id (triple6 t)).det * d t
    rw [sum_univ_20]
    have hm0  : M 0  = A 1 0 * A 2 1 - A 1 1 * A 2 0 := hM 0
    have hm1  : M 1  = A 1 0 * A 2 2 - A 1 2 * A 2 0 := hM 1
    have hm2  : M 2  = A 1 0 * A 2 3 - A 1 3 * A 2 0 := hM 2
    have hm3  : M 3  = A 1 0 * A 2 4 - A 1 4 * A 2 0 := hM 3
    have hm4  : M 4  = A 1 0 * A 2 5 - A 1 5 * A 2 0 := hM 4
    have hm5  : M 5  = A 1 1 * A 2 2 - A 1 2 * A 2 1 := hM 5
    have hm6  : M 6  = A 1 1 * A 2 3 - A 1 3 * A 2 1 := hM 6
    have hm7  : M 7  = A 1 1 * A 2 4 - A 1 4 * A 2 1 := hM 7
    have hm8  : M 8  = A 1 1 * A 2 5 - A 1 5 * A 2 1 := hM 8
    have hm9  : M 9  = A 1 2 * A 2 3 - A 1 3 * A 2 2 := hM 9
    have hm10 : M 10 = A 1 2 * A 2 4 - A 1 4 * A 2 2 := hM 10
    have hm11 : M 11 = A 1 2 * A 2 5 - A 1 5 * A 2 2 := hM 11
    have hm12 : M 12 = A 1 3 * A 2 4 - A 1 4 * A 2 3 := hM 12
    have hm13 : M 13 = A 1 3 * A 2 5 - A 1 5 * A 2 3 := hM 13
    have hm14 : M 14 = A 1 4 * A 2 5 - A 1 5 * A 2 4 := hM 14
    have ha0  := tripleDet_laplace_row0 A 0 1 2
    have ha1  := tripleDet_laplace_row0 A 0 1 3
    have ha2  := tripleDet_laplace_row0 A 0 1 4
    have ha3  := tripleDet_laplace_row0 A 0 1 5
    have ha4  := tripleDet_laplace_row0 A 0 2 3
    have ha5  := tripleDet_laplace_row0 A 0 2 4
    have ha6  := tripleDet_laplace_row0 A 0 2 5
    have ha7  := tripleDet_laplace_row0 A 0 3 4
    have ha8  := tripleDet_laplace_row0 A 0 3 5
    have ha9  := tripleDet_laplace_row0 A 0 4 5
    have ha10 := tripleDet_laplace_row0 A 1 2 3
    have ha11 := tripleDet_laplace_row0 A 1 2 4
    have ha12 := tripleDet_laplace_row0 A 1 2 5
    have ha13 := tripleDet_laplace_row0 A 1 3 4
    have ha14 := tripleDet_laplace_row0 A 1 3 5
    have ha15 := tripleDet_laplace_row0 A 1 4 5
    have ha16 := tripleDet_laplace_row0 A 2 3 4
    have ha17 := tripleDet_laplace_row0 A 2 3 5
    have ha18 := tripleDet_laplace_row0 A 2 4 5
    have ha19 := tripleDet_laplace_row0 A 3 4 5
    change _ =
      (A.submatrix id ![0, 1, 2]).det * d 0  + (A.submatrix id ![0, 1, 3]).det * d 1 +
      (A.submatrix id ![0, 1, 4]).det * d 2  + (A.submatrix id ![0, 1, 5]).det * d 3 +
      (A.submatrix id ![0, 2, 3]).det * d 4  + (A.submatrix id ![0, 2, 4]).det * d 5 +
      (A.submatrix id ![0, 2, 5]).det * d 6  + (A.submatrix id ![0, 3, 4]).det * d 7 +
      (A.submatrix id ![0, 3, 5]).det * d 8  + (A.submatrix id ![0, 4, 5]).det * d 9 +
      (A.submatrix id ![1, 2, 3]).det * d 10 + (A.submatrix id ![1, 2, 4]).det * d 11 +
      (A.submatrix id ![1, 2, 5]).det * d 12 + (A.submatrix id ![1, 3, 4]).det * d 13 +
      (A.submatrix id ![1, 3, 5]).det * d 14 + (A.submatrix id ![1, 4, 5]).det * d 15 +
      (A.submatrix id ![2, 3, 4]).det * d 16 + (A.submatrix id ![2, 3, 5]).det * d 17 +
      (A.submatrix id ![2, 4, 5]).det * d 18 + (A.submatrix id ![3, 4, 5]).det * d 19
    rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14,
        ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14,
        ha15, ha16, ha17, ha18, ha19]
  rw [hL_rew, hg, hR_rew]

/-- **Universal Kummer Quartic `w²` Factorization (`Plücker Abth. II §5`)**:
For EVERY `4 × 3` chart `k : Fin 4` and EVERY `6 × 6` matrix `S` over any `CommRing R`,
`det ((chartRayMatrix x k)ᵀ * S * (chartRayMatrix x k)) = (x k)^2 * kummerSingularQuartic S x`. -/
theorem universal_kummer_w_sq_factorization {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (x : Fin 4 → R) (k : Fin 4) :
    (coneChartMatrix S x k).det = (x k) ^ 2 * kummerSingularQuartic S x := by
  let L := chartRayMatrix x k
  have h1 : coneChartMatrix S x k = Lᵀ * (Lᵀ * Sᵀ)ᵀ := by
    simp [coneChartMatrix, L, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h1, binet_cauchy_3x6]
  have h2 : ∀ t : Fin 20,
      ((Lᵀ * Sᵀ).submatrix id (triple6 t)).det =
        ∑ u : Fin 20, ((S.submatrix (triple6 t) (triple6 u)).det) *
          (L.submatrix (triple6 u) id).det := by
    intro t
    have hsub : (Lᵀ * Sᵀ).submatrix id (triple6 t) =
        Lᵀ * (S.submatrix (triple6 t) id)ᵀ := by
      ext i c
      simp [Matrix.mul_apply, Matrix.submatrix_apply]
    have hswap : ((Lᵀ * (S.submatrix (triple6 t) id)ᵀ).det) =
        ((S.submatrix (triple6 t) id * L).det) := by
      rw [← Matrix.det_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_transpose]
    have hSL : S.submatrix (triple6 t) id * L = S.submatrix (triple6 t) id * (Lᵀ)ᵀ := by
      rw [Matrix.transpose_transpose]
    rw [hsub, hswap, hSL, binet_cauchy_3x6]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hLu : (Lᵀ.submatrix id (triple6 u)).det = (L.submatrix (triple6 u) id).det := by
      rw [← Matrix.det_transpose]; rfl
    rw [hLu]; rfl
  simp only [h2]
  have hLt : ∀ t : Fin 20, (Lᵀ.submatrix id (triple6 t)).det = (L.submatrix (triple6 t) id).det := by
    intro t; rw [← Matrix.det_transpose]; rfl
  dsimp only [L] at hLt ⊢
  simp only [hLt, chartRayMatrix_minor_eq, kummerSingularQuartic]
  have hneg2 : (((-1 : R) ^ (k : ℕ)) * ((-1 : R) ^ (k : ℕ))) = 1 := by
    rw [← mul_pow]; norm_num
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  calc
    ((-1 : R) ^ (k : ℕ) * x k * kummerPsi t x) *
        ((S.submatrix (triple6 t) (triple6 u)).det *
          ((-1 : R) ^ (k : ℕ) * x k * kummerPsi u x))
      = ((-1 : R) ^ (k : ℕ) * (-1 : R) ^ (k : ℕ)) * (x k * x k) *
          (kummerPsi t x * (S.submatrix (triple6 t) (triple6 u)).det * kummerPsi u x) := by ring
    _ = (x k) ^ 2 * (kummerPsi t x * (S.submatrix (triple6 t) (triple6 u)).det * kummerPsi u x) := by
      rw [hneg2, one_mul, sq]

private lemma polarDotMatrix_mulVec_coordinates {R : Type*} [CommRing R]
    (P : KleinQuadric.Plucker6 R) :
    (polarDotMatrix : Matrix (Fin 6) (Fin 6) R) *ᵥ coordinates P =
      coordinates (axisDualEquiv P) := by
  ext r
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  fin_cases r <;> simp [polarDotMatrix, coordinates, axisDualEquiv]

private lemma rayPlucker_polar_same_base {R : Type*} [CommRing R] (x y z : Fin 4 → R) :
    (rayPlucker x y).polar (rayPlucker x z) = 0 := by
  dsimp [Plucker6.polar, Plucker6.add, Plucker6.kleinQ, rayPlucker]
  ring

theorem chartRayMatrix_polarDotMatrix_zero {R : Type*} [CommRing R] (x : Fin 4 → R) (k : Fin 4) :
    (chartRayMatrix x k)ᵀ * ((polarDotMatrix : Matrix (Fin 6) (Fin 6) R) * chartRayMatrix x k) =
      (0 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  rw [Matrix.mul_apply]
  change (fun r => chartRayMatrix x k r i) ⬝ᵥ
      ((polarDotMatrix : Matrix (Fin 6) (Fin 6) R) *ᵥ fun s => chartRayMatrix x k s j) = 0
  have hi : (fun r => chartRayMatrix x k r i) =
      coordinates (rayPlucker x (stdBasis4 (k.succAbove i))) := rfl
  have hj : (fun s => chartRayMatrix x k s j) =
      coordinates (rayPlucker x (stdBasis4 (k.succAbove j))) := rfl
  rw [hi, hj, ← polar_eq_vec_dot_mulVec, rayPlucker_polar_same_base]

/-- **Klein-ambiguity invariance of the Kummer singular surface (`Abth. II §5`)**:
Adding any scalar multiple `c • polarDotMatrix` leaves the Kummer quartic polynomial identically
unchanged across every point `x : Fin 4 → R` over any integral domain `R`. -/
theorem kummerSingularQuartic_add_klein {R : Type*} [CommRing R] [IsDomain R]
    (S : Matrix (Fin 6) (Fin 6) R) (c : R) (x : Fin 4 → R) :
    kummerSingularQuartic (S + c • (polarDotMatrix : Matrix (Fin 6) (Fin 6) R)) x =
      kummerSingularQuartic S x := by
  by_cases hx : ∃ k : Fin 4, x k ≠ 0
  · rcases hx with ⟨k, hxk⟩
    have hcone : coneChartMatrix (S + c • (polarDotMatrix : Matrix (Fin 6) (Fin 6) R)) x k =
        coneChartMatrix S x k := by
      simp only [coneChartMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc, chartRayMatrix_polarDotMatrix_zero x k, smul_zero, add_zero]
    have hdet :
        (x k) ^ 2 * kummerSingularQuartic (S + c • (polarDotMatrix : Matrix (Fin 6) (Fin 6) R)) x =
          (x k) ^ 2 * kummerSingularQuartic S x := by
      rw [← universal_kummer_w_sq_factorization
            (S + c • (polarDotMatrix : Matrix (Fin 6) (Fin 6) R)) x k,
          ← universal_kummer_w_sq_factorization S x k, hcone]
    exact mul_left_cancel₀ (pow_ne_zero 2 hxk) hdet
  · push Not at hx
    have hpsi0 : ∀ t : Fin 20, kummerPsi t x = 0 := by
      intro t; fin_cases t <;> simp [kummerPsi, hx]
    simp [kummerSingularQuartic, hpsi0]

/-- Plane-chart matrix joining plane `u` to coordinate reference planes, equal to
`(polarDotMatrix : Matrix (Fin 6) (Fin 6) R) * chartRayMatrix u k`. -/
def planeChartMatrix {R : Type*} [CommRing R] (u : Fin 4 → R) (k : Fin 4) :
    Matrix (Fin 6) (Fin 3) R :=
  Matrix.of fun r c => coordinates (axisAsRayPlucker u (stdBasis4 (k.succAbove c))) r

private lemma planeChartMatrix_eq_polar_mul {R : Type*} [CommRing R] (u : Fin 4 → R) (k : Fin 4) :
    planeChartMatrix u k = (polarDotMatrix : Matrix (Fin 6) (Fin 6) R) * chartRayMatrix u k := by
  ext r c
  change coordinates (axisDualEquiv (rayPlucker u (stdBasis4 (k.succAbove c)))) r =
    ((polarDotMatrix : Matrix (Fin 6) (Fin 6) R) *ᵥ fun s => chartRayMatrix u k s c) r
  have hc : (fun s => chartRayMatrix u k s c) =
      coordinates (rayPlucker u (stdBasis4 (k.succAbove c))) := rfl
  rw [hc, polarDotMatrix_mulVec_coordinates]

/-- **Kummer Point–Plane Self-Duality (`Plücker Abth. II §§5–6`)**:
Replacing ray coordinates by dual plane-axis coordinates conjugates `S` by `polarDotMatrix` and
yields the exact same `w² * kummerSingularQuartic (polarDotMatrix * S * polarDotMatrix) u` structure. -/
theorem kummer_plane_dual_duality {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (u : Fin 4 → R) (k : Fin 4) :
    ((planeChartMatrix u k)ᵀ * S * planeChartMatrix u k).det =
      (u k) ^ 2 * kummerSingularQuartic
        ((polarDotMatrix : Matrix (Fin 6) (Fin 6) R) * S *
          (polarDotMatrix : Matrix (Fin 6) (Fin 6) R)) u := by
  let J : Matrix (Fin 6) (Fin 6) R := polarDotMatrix
  have hpolT : Jᵀ = J := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [planeChartMatrix_eq_polar_mul, Matrix.transpose_mul, hpolT]
  have hmat :
      (chartRayMatrix u k)ᵀ * J * S * (J * chartRayMatrix u k) =
        coneChartMatrix (J * S * J) u k := by
    simp [coneChartMatrix, Matrix.mul_assoc]
  rw [hmat]
  exact universal_kummer_w_sq_factorization (J * S * J) u k

private lemma homogeneous4_term {R : Type*} [CommRing R] (a p d q : R) :
    (a ^ 2 * p) * d * (a ^ 2 * q) = a ^ 4 * (p * d * q) := by
  ring

theorem kummerSingularQuartic_homogeneous4 {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (a : R) (x : Fin 4 → R) :
    kummerSingularQuartic S (a • x) = a ^ 4 * kummerSingularQuartic S x := by
  have hpsi : ∀ t : Fin 20, kummerPsi t (a • x) = a ^ 2 * kummerPsi t x := by
    intro t; fin_cases t <;> simp [kummerPsi] <;> ring
  simp only [kummerSingularQuartic, hpsi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
  exact homogeneous4_term a (kummerPsi t x) ((S.submatrix (triple6 t) (triple6 u)).det)
    (kummerPsi u x)

/-- Non-commutativity witness for the `3 × 3` matrix carrier (`coneChartMatrix` on `Fin 3`). -/
theorem matrix3_noncomm {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 3) (Fin 3) R, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

end UniversalKummerFactorization

section CanonicalKummerSixteenNodesAndErratum

/-- Canonical 10-monomial Kummer quartic surface equation (`Plücker §5–6`, Klein 1870):
`x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴ + A(x₀²x₁² + x₂²x₃²) + B(x₀²x₂² + x₁²x₃²) + C(x₀²x₃² + x₁²x₂²) + 2 D x₀x₁x₂x₃`. -/
def canonicalKummerQuartic {R : Type*} [CommRing R] (A B C D : R) (x : Fin 4 → R) : R :=
  x 0 ^ 4 + x 1 ^ 4 + x 2 ^ 4 + x 3 ^ 4 +
    A * (x 0 ^ 2 * x 1 ^ 2 + x 2 ^ 2 * x 3 ^ 2) +
    B * (x 0 ^ 2 * x 2 ^ 2 + x 1 ^ 2 * x 3 ^ 2) +
    C * (x 0 ^ 2 * x 3 ^ 2 + x 1 ^ 2 * x 2 ^ 2) +
    2 * D * x 0 * x 1 * x 2 * x 3

/-- Formal algebraic gradient `(∂Φ/∂x₀, ∂Φ/∂x₁, ∂Φ/∂x₂, ∂Φ/∂x₃)` of the canonical Kummer quartic. -/
def canonicalKummerGrad {R : Type*} [CommRing R] (A B C D : R) (x : Fin 4 → R) : Fin 4 → R
  | 0 => 4 * x 0 ^ 3 + 2 * A * x 0 * x 1 ^ 2 + 2 * B * x 0 * x 2 ^ 2 + 2 * C * x 0 * x 3 ^ 2 +
      2 * D * x 1 * x 2 * x 3
  | 1 => 4 * x 1 ^ 3 + 2 * A * x 1 * x 0 ^ 2 + 2 * B * x 1 * x 3 ^ 2 + 2 * C * x 1 * x 2 ^ 2 +
      2 * D * x 0 * x 2 * x 3
  | 2 => 4 * x 2 ^ 3 + 2 * A * x 2 * x 3 ^ 2 + 2 * B * x 2 * x 0 ^ 2 + 2 * C * x 2 * x 1 ^ 2 +
      2 * D * x 0 * x 1 * x 3
  | 3 => 4 * x 3 ^ 3 + 2 * A * x 3 * x 2 ^ 2 + 2 * B * x 3 * x 1 ^ 2 + 2 * C * x 3 * x 0 ^ 2 +
      2 * D * x 0 * x 1 * x 2

/-- Four even sign-flip involutions preserving `x₀ x₁ x₂ x₃`. -/
def kummerSignFlip {R : Type*} [Ring R] (s : Fin 4) (x : Fin 4 → R) : Fin 4 → R
  | i =>
    match s, i with
    | 0, 0 => x 0 | 0, 1 => x 1 | 0, 2 => x 2 | 0, 3 => x 3
    | 1, 0 => x 0 | 1, 1 => x 1 | 1, 2 => -x 2 | 1, 3 => -x 3
    | 2, 0 => x 0 | 2, 1 => -x 1 | 2, 2 => x 2 | 2, 3 => -x 3
    | 3, 0 => x 0 | 3, 1 => -x 1 | 3, 2 => -x 2 | 3, 3 => x 3

/-- Four Klein four-group `V₄` coordinate permutations `{id, (01)(23), (02)(13), (03)(12)}`. -/
def kummerV4Perm {R : Type*} (p : Fin 4) (x : Fin 4 → R) : Fin 4 → R
  | i =>
    match p, i with
    | 0, 0 => x 0 | 0, 1 => x 1 | 0, 2 => x 2 | 0, 3 => x 3
    | 1, 0 => x 1 | 1, 1 => x 0 | 1, 2 => x 3 | 1, 3 => x 2
    | 2, 0 => x 2 | 2, 1 => x 3 | 2, 2 => x 0 | 2, 3 => x 1
    | 3, 0 => x 3 | 3, 1 => x 2 | 3, 2 => x 1 | 3, 3 => x 0

/-- Action of the 16-element Kummer symmetry group `(ℤ₂³) ⋊ V₄` (realized via `Fin 4 × Fin 4`). -/
def kummerGroupAct {R : Type*} [Ring R] (g : Fin 4 × Fin 4) (x : Fin 4 → R) : Fin 4 → R :=
  kummerSignFlip g.1 (kummerV4Perm g.2 x)

theorem canonicalKummerQuartic_group_invariant {R : Type*} [CommRing R]
    (A B C D : R) (g : Fin 4 × Fin 4) (x : Fin 4 → R) :
    canonicalKummerQuartic A B C D (kummerGroupAct g x) = canonicalKummerQuartic A B C D x := by
  rcases g with ⟨s, p⟩
  fin_cases s <;> fin_cases p <;>
    simp [kummerGroupAct, kummerSignFlip, kummerV4Perm, canonicalKummerQuartic] <;> ring

private lemma canonicalKummerGrad_v4Perm_zero {R : Type*} [CommRing R]
    (A B C D : R) (p : Fin 4) (x : Fin 4 → R) (hx : canonicalKummerGrad A B C D x = 0) :
    canonicalKummerGrad A B C D (kummerV4Perm p x) = 0 := by
  have h0 : canonicalKummerGrad A B C D x 0 = 0 := congrFun hx 0
  have h1 : canonicalKummerGrad A B C D x 1 = 0 := congrFun hx 1
  have h2 : canonicalKummerGrad A B C D x 2 = 0 := congrFun hx 2
  have h3 : canonicalKummerGrad A B C D x 3 = 0 := congrFun hx 3
  dsimp only [canonicalKummerGrad] at h0 h1 h2 h3
  ext i
  fin_cases p <;> fin_cases i <;>
    dsimp only [kummerV4Perm, canonicalKummerGrad, Pi.zero_apply]
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · linear_combination h1
  · linear_combination h0
  · linear_combination h3
  · linear_combination h2
  · linear_combination h2
  · linear_combination h3
  · linear_combination h0
  · linear_combination h1
  · linear_combination h3
  · linear_combination h2
  · linear_combination h1
  · linear_combination h0

private lemma canonicalKummerGrad_signFlip_zero {R : Type*} [CommRing R]
    (A B C D : R) (s : Fin 4) (x : Fin 4 → R) (hx : canonicalKummerGrad A B C D x = 0) :
    canonicalKummerGrad A B C D (kummerSignFlip s x) = 0 := by
  have h0 : canonicalKummerGrad A B C D x 0 = 0 := congrFun hx 0
  have h1 : canonicalKummerGrad A B C D x 1 = 0 := congrFun hx 1
  have h2 : canonicalKummerGrad A B C D x 2 = 0 := congrFun hx 2
  have h3 : canonicalKummerGrad A B C D x 3 = 0 := congrFun hx 3
  dsimp only [canonicalKummerGrad] at h0 h1 h2 h3
  ext i
  fin_cases s <;> fin_cases i <;>
    dsimp only [kummerSignFlip, canonicalKummerGrad, Pi.zero_apply]
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · linear_combination h0
  · linear_combination h1
  · linear_combination -h2
  · linear_combination -h3
  · linear_combination h0
  · linear_combination -h1
  · linear_combination h2
  · linear_combination -h3
  · linear_combination h0
  · linear_combination -h1
  · linear_combination -h2
  · linear_combination h3

theorem canonicalKummerGrad_group_zero {R : Type*} [CommRing R]
    (A B C D : R) (g : Fin 4 × Fin 4) (x : Fin 4 → R)
    (hx : canonicalKummerGrad A B C D x = 0) :
    canonicalKummerGrad A B C D (kummerGroupAct g x) = 0 :=
  canonicalKummerGrad_signFlip_zero A B C D g.1 (kummerV4Perm g.2 x)
    (canonicalKummerGrad_v4Perm_zero A B C D g.2 x hx)

/-- Concrete nondegenerate Kummer parameters generating `16` distinct singular nodes from `(1,2,3,5)`. -/
def kummer16NodeBase : Fin 4 → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 5

theorem kummer16Orbit_all_nodes (g : Fin 4 × Fin 4) :
    let y := kummerGroupAct g kummer16NodeBase
    canonicalKummerQuartic (-53 / 17 : ℝ) (-43 / 7) (529 / 11) (-49590 / 1309) y = 0 ∧
      canonicalKummerGrad (-53 / 17 : ℝ) (-43 / 7) (529 / 11) (-49590 / 1309) y = 0 := by
  have hval :
      canonicalKummerQuartic (-53 / 17 : ℝ) (-43 / 7) (529 / 11) (-49590 / 1309)
        kummer16NodeBase = 0 := by
    dsimp [canonicalKummerQuartic, kummer16NodeBase]
    norm_num
  have hgrad :
      canonicalKummerGrad (-53 / 17 : ℝ) (-43 / 7) (529 / 11) (-49590 / 1309)
        kummer16NodeBase = 0 := by
    ext i
    fin_cases i <;>
      (dsimp [canonicalKummerGrad, kummer16NodeBase]; norm_num)
  exact ⟨(canonicalKummerQuartic_group_invariant _ _ _ _ g kummer16NodeBase).trans hval,
    canonicalKummerGrad_group_zero _ _ _ _ g kummer16NodeBase hgrad⟩

theorem kummer16Orbit_pairwise_nonproportional (g₁ g₂ : Fin 4 × Fin 4) (hne : g₁ ≠ g₂) :
    ¬ ∃ c : ℝ, kummerGroupAct g₁ kummer16NodeBase = c • kummerGroupAct g₂ kummer16NodeBase := by
  rintro ⟨c, hc⟩
  rcases g₁ with ⟨s₁, p₁⟩; rcases g₂ with ⟨s₂, p₂⟩
  by_cases hp : p₁ = p₂
  · subst hp
    have hs : s₁ ≠ s₂ := fun h => hne (by subst h; rfl)
    have hc0 : kummerGroupAct (s₁, p₁) kummer16NodeBase 0 =
        c * kummerGroupAct (s₂, p₁) kummer16NodeBase 0 := congrFun hc 0
    have h0eq : kummerGroupAct (s₁, p₁) kummer16NodeBase 0 =
        kummerGroupAct (s₂, p₁) kummer16NodeBase 0 := by
      fin_cases s₁ <;> fin_cases s₂ <;> fin_cases p₁ <;> rfl
    have h0ne : kummerGroupAct (s₂, p₁) kummer16NodeBase 0 ≠ 0 := by
      fin_cases s₂ <;> fin_cases p₁ <;> simp [kummerGroupAct, kummerSignFlip, kummerV4Perm,
        kummer16NodeBase]
    have hc1 : c = 1 := by
      have : (c - 1) * kummerGroupAct (s₂, p₁) kummer16NodeBase 0 = 0 := by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0ne)
    rw [hc1, one_smul] at hc
    fin_cases s₁ <;> fin_cases s₂ <;> fin_cases p₁ <;>
      first | exact hs rfl |
        (have hfun : ∀ i, kummerGroupAct _ kummer16NodeBase i =
            kummerGroupAct _ kummer16NodeBase i := congrFun hc
         have hd := hfun 1
         have he := hfun 2
         have hf := hfun 3
         dsimp [kummerGroupAct, kummerSignFlip, kummerV4Perm, kummer16NodeBase] at hd he hf
         linarith)
  · have hminor :
        kummerGroupAct (s₁, p₁) kummer16NodeBase 0 ^ 2 *
          kummerGroupAct (s₂, p₂) kummer16NodeBase 1 ^ 2 =
        kummerGroupAct (s₁, p₁) kummer16NodeBase 1 ^ 2 *
          kummerGroupAct (s₂, p₂) kummer16NodeBase 0 ^ 2 := by
      have hc0 := congrFun hc 0
      have hc1 := congrFun hc 1
      dsimp only [Pi.smul_apply, smul_eq_mul] at hc0 hc1
      rw [hc0, hc1]
      ring
    have hflip : ∀ (s : Fin 4) (v : Fin 4 → ℝ) (i : Fin 4),
        kummerSignFlip s v i ^ 2 = v i ^ 2 := by
      intro s v i; fin_cases s <;> fin_cases i <;> simp [kummerSignFlip]
    simp only [kummerGroupAct, hflip] at hminor
    fin_cases p₁ <;> fin_cases p₂ <;>
      first | exact hp rfl |
        (dsimp [kummerV4Perm, kummer16NodeBase] at hminor; norm_num at hminor)

/-- **Plücker Sextic `Eq. (5.171)` → `w²` Kummer Quartic `Eq. (5.178)` (`p. 301`)**:
Evaluating `coneChartMatrix S ![x, y, z, w] 3` directly yields Plücker's sextic cone determinant
with an explicit `w²` factor extracting the Kummer quartic at infinity `w = 0`. -/
theorem plucker_sextic_eq5171_factors_w_sq {R : Type*} [CommRing R]
    (S : Matrix (Fin 6) (Fin 6) R) (x y z w : R) :
    (coneChartMatrix S ![x, y, z, w] 3).det =
      w ^ 2 * kummerSingularQuartic S ![x, y, z, w] := by
  simpa using universal_kummer_w_sq_factorization S ![x, y, z, w] 3

/-- Plücker's printed `Eq. (5.183)` `y`-coordinate `(D Q - F T) / (2 D F)` (`p. 302`). -/
noncomputable def printedEq5183_y (D F Q T : ℝ) : ℝ :=
  (D * Q - F * T) / (2 * D * F)

/-- `[countermodel_found]` **Historical sign erratum in Plücker `Eq. (5.183)` (`p. 302`)**:
The true directional-derivative center of the Kummer quartic coincides with the `y`-coordinate of
`centralParallelepipedCenter` (`(F T - D Q) / (2 D F)`), whereas printed `Eq. (5.183)` has the
exact opposite sign `(D Q - F T) / (2 D F)` (`≠` whenever `F T ≠ D Q`, witnessed at
`D = F = Q = 1, T = 0`: true `-1/2` vs printed `+1/2`). -/
theorem eq5183_printed_sign_erratum (D E F Q R S T U P : ℝ)
    (hD : D ≠ 0) (hE : E ≠ 0) (hF : F ≠ 0) :
    printedEq5183_y D F Q T = -(centralParallelepipedCenter D E F Q R S T U P 1) := by
  rw [centralParallelepipedCenter_eq D E F Q R S T U P hD hE hF]
  simp only [printedEq5183_y, Matrix.cons_val_one, Matrix.cons_val_zero]
  field_simp [hD, hF]; ring

theorem eq5183_countermodel_witness :
    printedEq5183_y 1 1 1 0 ≠ centralParallelepipedCenter 1 1 1 1 0 0 0 0 0 1 := by
  intro h
  have h1 : printedEq5183_y 1 1 1 0 = 1 / 2 := by
    dsimp [printedEq5183_y]; norm_num
  have h2 : centralParallelepipedCenter 1 1 1 1 0 0 0 0 0 1 = -(1 / 2) := by
    dsimp [centralParallelepipedCenter, parallelepipedVertexG, parallelepipedVertexH]; norm_num
  rw [h1, h2] at h
  norm_num at h

end CanonicalKummerSixteenNodesAndErratum

section EquatorialComplexSurfaces

/-- Plücker's normalized equatorial complex surface (`Abth. III, Nos. 342–373`, `pp. 319–350`):
`ψ(x) * y² + φ(x) * z² - φ(x) * ψ(x) = 0`. -/
def equatorialComplexSurface (φ ψ : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  ψ x * y ^ 2 + φ x * z ^ 2 - φ x * ψ x

inductive EquatorialSliceClass
  | elliptic
  | hyperbolic
  | imaginary
  | degenerate
  deriving DecidableEq

/-- Classification of real cross-sections `x = const` of `equatorialComplexSurface`:
elliptic (`φ > 0, ψ > 0`), hyperbolic (`φ * ψ < 0`), empty real locus (`φ < 0, ψ < 0`), or
degenerate tangent-line pairs (`φ = 0 ∨ ψ = 0`). -/
theorem equatorialSliceZero_classify (φ ψ : ℝ → ℝ) (x : ℝ) :
    (0 < φ x ∧ 0 < ψ x ∧
        ∀ y z : ℝ, equatorialComplexSurface φ ψ x y z = 0 ↔ y ^ 2 / φ x + z ^ 2 / ψ x = 1) ∨
    (φ x * ψ x < 0 ∧
        ∀ y z : ℝ, equatorialComplexSurface φ ψ x y z = 0 ↔ y ^ 2 / φ x + z ^ 2 / ψ x = 1) ∨
    (φ x < 0 ∧ ψ x < 0 ∧ ∀ y z : ℝ, equatorialComplexSurface φ ψ x y z ≠ 0) ∨
    (φ x = 0 ∨ ψ x = 0) := by
  by_cases hz : φ x = 0 ∨ ψ x = 0
  · exact Or.inr (Or.inr (Or.inr hz))
  · push Not at hz
    rcases hz with ⟨hφ, hψ⟩
    have heqv : ∀ y z : ℝ,
        equatorialComplexSurface φ ψ x y z = 0 ↔ y ^ 2 / φ x + z ^ 2 / ψ x = 1 := by
      intro y z
      simp only [equatorialComplexSurface]
      have hmul : ψ x * y ^ 2 + φ x * z ^ 2 - φ x * ψ x = 0 ↔
          (y ^ 2 / φ x + z ^ 2 / ψ x - 1) * (φ x * ψ x) = 0 := by
        have hid : (y ^ 2 / φ x + z ^ 2 / ψ x - 1) * (φ x * ψ x) =
            ψ x * y ^ 2 + φ x * z ^ 2 - φ x * ψ x := by
          field_simp [hφ, hψ]
        rw [hid]
      rw [hmul, mul_eq_zero]
      constructor
      · intro h
        exact sub_eq_zero.mp (h.resolve_right (mul_ne_zero hφ hψ))
      · intro h
        left; exact sub_eq_zero.mpr h
    rcases lt_or_gt_of_ne hφ with hφneg | hφpos <;>
        rcases lt_or_gt_of_ne hψ with hψneg | hψpos
    · right; right; left
      refine ⟨hφneg, hψneg, fun y z heq => ?_⟩
      simp only [equatorialComplexSurface] at heq
      have hpos : 0 < φ x * ψ x := mul_pos_of_neg_of_neg hφneg hψneg
      have hy : ψ x * y ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hψneg) (sq_nonneg y)
      have hz2 : φ x * z ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hφneg) (sq_nonneg z)
      linarith
    · right; left
      exact ⟨mul_neg_of_neg_of_pos hφneg hψpos, heqv⟩
    · right; left
      exact ⟨mul_neg_of_pos_of_neg hφpos hψneg, heqv⟩
    · left
      exact ⟨hφpos, hψpos, heqv⟩

end EquatorialComplexSurfaces

section EpistemicCausalPosetAndSynthesis

/-- The 9 mathematical archetypes extracted from Julius Plücker's *Neue Geometrie des Raumes*
(`Liniengeometriev1.pdf`, Parts I–II, `Nos. 1–373`, pp. 1–378). -/
inductive PluckerNeueGeometrieArchetype : Type
  | PL1 : PluckerNeueGeometrieArchetype -- Ray–Axis coordinates, duality & covariance (`Nos. 1–16`)
  | PL2 : PluckerNeueGeometrieArchetype -- Dynames, forces & linear complex conjugacy (`Nos. 17–25`)
  | PL3 : PluckerNeueGeometrieArchetype -- Linear complexes & canonical central axis (`Nos. 26–61`)
  | PL4 : PluckerNeueGeometrieArchetype -- Congruences & Plücker's cubic cylindroid (`Nos. 62–107`)
  | PL5 : PluckerNeueGeometrieArchetype -- Three-complex web, regulus & No. 143 (`Nos. 108–148`)
  | PL6 : PluckerNeueGeometrieArchetype -- Quadratic complexes, splitting & degree (`Nos. 149–233`)
  | PL7 : PluckerNeueGeometrieArchetype -- Characteristic quadric & parallelepiped (`Nos. 234–290`)
  | PL8 : PluckerNeueGeometrieArchetype -- Singular/double lines, Kummer & equatorial (`Nos. 291–373`)
  | PL9 : PluckerNeueGeometrieArchetype -- Master synthesis (`Liniengeometriev1.pdf` complete)
  deriving DecidableEq, Repr

/-- Transitive closure dependency bitmask encoding the exact chapter/theorem DAG on `Fin 9`. -/
def pluckerMask : PluckerNeueGeometrieArchetype → UInt16
  | .PL1 => 0b000000001
  | .PL2 => 0b000000011 -- ≥ PL1
  | .PL3 => 0b000000101 -- ≥ PL1
  | .PL4 => 0b000001111 -- ≥ PL1, PL2, PL3
  | .PL5 => 0b000011111 -- ≥ PL1..PL4
  | .PL6 => 0b000100001 -- ≥ PL1
  | .PL7 => 0b001100001 -- ≥ PL1, PL6
  | .PL8 => 0b011111111 -- ≥ PL1..PL7
  | .PL9 => 0b111111111 -- ≥ PL1..PL8

instance : LE PluckerNeueGeometrieArchetype where
  le a b := (pluckerMask a &&& pluckerMask b) = pluckerMask a

instance (a b : PluckerNeueGeometrieArchetype) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable ((pluckerMask a &&& pluckerMask b) = pluckerMask a))

instance : PartialOrder PluckerNeueGeometrieArchetype where
  le := (· ≤ ·)
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide

theorem plucker_causal_poset_branching_witnesses :
    (¬ (PluckerNeueGeometrieArchetype.PL2 ≤ .PL3) ∧
      ¬ (PluckerNeueGeometrieArchetype.PL3 ≤ .PL2)) ∧
    (¬ (PluckerNeueGeometrieArchetype.PL4 ≤ .PL6) ∧
      ¬ (PluckerNeueGeometrieArchetype.PL6 ≤ .PL4)) ∧
    (¬ (PluckerNeueGeometrieArchetype.PL5 ≤ .PL7) ∧
      ¬ (PluckerNeueGeometrieArchetype.PL7 ≤ .PL5)) := by
  decide

theorem plucker_all_reach_master (a : PluckerNeueGeometrieArchetype) :
    a ≤ PluckerNeueGeometrieArchetype.PL9 := by
  cases a <;> decide

/-- **Master Epistemic Synthesis (`PL₉`)** connecting all eight Plücker 1868/1869 archetypes:
ray–axis duality, two-force dyname splitting, 5-line linear complex uniqueness, cylindroid
surface & `No. 143` countermodel, `21/20`-dimensional quadratic complex quotient & `Eq. (1.21)`
countermodel, universal `w²` Kummer quartic factorization, concrete 16-node Kummer orbit, and
`Eq. (5.183)` sign erratum. -/
theorem plucker_neue_geometrie_master_synthesis :
    (∀ (x y u v : Fin 4 → ℝ),
      (∑ k, u k * x k = 0) → (∑ k, u k * y k = 0) →
      (∑ k, v k * x k = 0) → (∑ k, v k * y k = 0) →
      ∀ i j, coordinates (rayPlucker x y) i * coordinates (axisAsRayPlucker u v) j =
        coordinates (rayPlucker x y) j * coordinates (axisAsRayPlucker u v) i) ∧
    (∀ d m : Vec3, d ≠ 0 ∨ m ≠ 0 → ∃ d₁ m₁ d₂ m₂ : Vec3,
      d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ d₁ ⬝ᵥ m₁ = 0 ∧ d₂ ⬝ᵥ m₂ = 0 ∧ d₁ + d₂ = d ∧ m₁ + m₂ = m) ∧
    (∀ (k₁ k₂ c s t : ℝ), c ^ 2 + s ^ 2 = 1 →
      let p := cylindroidPoint k₁ k₂ c s t
      p 2 * (p 0 ^ 2 + p 1 ^ 2) = (k₂ - k₁) * p 0 * p 1) ∧
    (¬ ∃ (ι : Type) (C : ι → KleinQuadric.Plucker6 ℝ),
      ∀ y₁ y₂ y₃ : ℝ, (y₁ ^ 2 + y₂ ^ 2 - y₃ ^ 2 = 0) ↔
        ∀ i : ι, (C i).Incident (rayPlucker ![1, 0, 0, 0] ![0, y₁, y₂, y₃])) ∧
    (Module.finrank ℝ (symmMat6Submodule ℝ ⧸ Submodule.span ℝ {kleinSymmMatrix}) = 20) ∧
    (printedEq121 1 1 1 0 2 0 0 0 0 ≠ centralParallelepipedCenter 1 1 1 0 2 0 0 0 0) ∧
    (∀ (S : Matrix (Fin 6) (Fin 6) ℝ) (x : Fin 4 → ℝ) (k : Fin 4),
      (coneChartMatrix S x k).det = (x k) ^ 2 * kummerSingularQuartic S x) ∧
    (∀ g₁ g₂ : Fin 4 × Fin 4, g₁ ≠ g₂ →
      ¬ ∃ c : ℝ, kummerGroupAct g₁ kummer16NodeBase = c • kummerGroupAct g₂ kummer16NodeBase) ∧
    (printedEq5183_y 1 1 1 0 ≠ centralParallelepipedCenter 1 1 1 1 0 0 0 0 0 1) :=
  ⟨fun x y u v h1 h2 h3 h4 i j => ray_axis_minors_eq_of_four_incidences x y u v h1 h2 h3 h4 i j,
   exists_two_finite_forces_for_dyname,
   cylindroid_cubic_surface_eq,
   no143_quadratic_cone_not_cut_by_linear_complexes,
   finrank_quadraticComplexQuotient,
   by dsimp [printedEq121, centralParallelepipedCenter, parallelepipedVertexG, parallelepipedVertexH]; norm_num,
   universal_kummer_w_sq_factorization,
   kummer16Orbit_pairwise_nonproportional,
   by dsimp [printedEq5183_y, centralParallelepipedCenter, parallelepipedVertexG, parallelepipedVertexH]; norm_num⟩

end EpistemicCausalPosetAndSynthesis

end InfoGeometry.Projective.PluckerKummerQuarticAndMasterAtlas
