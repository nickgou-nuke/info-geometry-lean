/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.PluckerRayAxisAndDyname
import InfoGeometry.Projective.PluckerComplexPencil

/-!
# Linear Complex Congruences, Plücker's Cubic Cylindroid, Reguli, and No. 143 Impossibility

This module formalizes Archetypes `PL₄` (`Abth. I §2, Nos. 62–107`) and
`PL₅` (`Abth. I §3, Nos. 108–148`) of Julius Plücker's *Neue Geometrie des Raumes*
(`Liniengeometriev1.pdf`, pp. 74–152):

* Congruence `(C, D)` ray-uniqueness at non-singular points (`congruence_unique_ray_through_point`)
  and four-case directrix classification via `pencilDiscriminant` (`pencil_classification_hyperbolic`,
  `pencil_classification_parabolic`, `pencil_classification_elliptic`,
  `pencil_classification_intersecting`).
* Plücker's cubic cylindroid (`cylindroidDir`, `cylindroidMom`, `cylindroid_axisFoot`,
  `cylindroid_cubic_surface_eq`, `cylindroid_not_planar_of_ne`, `Nos. 96–104`).
* Three-complex web orthogonality and involution (`finrank_kleinPolarOrth_eq_three`,
  `kleinPolarOrth_involutive`) and explicit opposite reguli `rulingPlus` / `rulingMinus` on
  `x₀² + x₃² - x₁² - x₂² = 0` (`opposite_reguli_common_point`, `opposite_reguli_incident`).
* `[countermodel_found]` `No. 143` impossibility (`no143_quadratic_cone_not_cut_by_linear_complexes`,
  `no143_plane_conic_not_enveloped_by_linear_complexes`): no family of linear complexes can cut
  out a non-degenerate quadratic cone or conic envelope.
-/

namespace InfoGeometry.Projective.PluckerCongruenceCylindroidAndRegulus

open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction
open InfoGeometry.Projective.PluckerLinearComplex
open InfoGeometry.Projective.PluckerAffineScrew
open InfoGeometry.Projective.PluckerComplexPencil
open InfoGeometry.Projective.PluckerRayAxisAndDyname
open Matrix

section CongruenceAndPencilClassification

/-- Null-system intersection map at a point `x : Fin 4 → K` for two linear complexes `C, D`:
sends `y` to `(C(x, y), D(x, y))` (`Plücker Nos. 62–72`, `pp. 74–85`). -/
noncomputable def congruenceNullMap {K : Type*} [Field K]
    (C D : KleinQuadric.Plucker6 K) (x : Fin 4 → K) :
    (Fin 4 → K) →ₗ[K] (Fin 2 → K) where
  toFun y := ![(complexMatrix C *ᵥ x) ⬝ᵥ y, (complexMatrix D *ᵥ x) ⬝ᵥ y]
  map_add' y₁ y₂ := by
    ext i; fin_cases i <;> simp [dotProduct_add]
  map_smul' r y := by
    ext i; fin_cases i <;> simp [dotProduct_smul]

private lemma complexMatrix_mulVec_dot_self {R : Type*} [CommRing R]
    (C : KleinQuadric.Plucker6 R) (x : Fin 4 → R) :
    (complexMatrix C *ᵥ x) ⬝ᵥ x = 0 := by
  have h : (complexForm C) x x = 0 := complexForm_isAlt C x
  simpa [complexForm, Matrix.toBilin'_apply', dotProduct_comm] using h

/-- Through any point `x` where the null planes `complexMatrix C *ᵥ x` and `complexMatrix D *ᵥ x`
are linearly independent, the congruence ray space has projective `finrank = 2` (a unique projective
line) and every member `y` yields ray Plücker coordinates proportional to `axisAsRayPlucker u v`
(`Plücker Nos. 62–72`). -/
theorem congruence_unique_ray_through_point {K : Type*} [Field K]
    (C D : KleinQuadric.Plucker6 K) (x : Fin 4 → K)
    (hInd : LinearIndependent K ![complexMatrix C *ᵥ x, complexMatrix D *ᵥ x]) :
    Module.finrank K (LinearMap.ker (congruenceNullMap C D x)) = 2 ∧
      ∀ y ∈ LinearMap.ker (congruenceNullMap C D x),
        ∀ (j₀ : Fin 6),
          coordinates (axisAsRayPlucker (complexMatrix C *ᵥ x) (complexMatrix D *ᵥ x)) j₀ ≠ 0 →
          ∃ c : K, ∀ i : Fin 6,
            coordinates (rayPlucker x y) i =
              c * coordinates (axisAsRayPlucker (complexMatrix C *ᵥ x) (complexMatrix D *ᵥ x)) i := by
  let u := complexMatrix C *ᵥ x
  let v := complexMatrix D *ᵥ x
  let M : Matrix (Fin 2) (Fin 4) K := Matrix.of ![u, v]
  have hEq : congruenceNullMap C D x = Matrix.mulVecLin M := by
    ext y i
    fin_cases i <;> simp [congruenceNullMap, M, Matrix.mulVec, u, v]
  have hKerMt : LinearMap.ker (Matrix.mulVecLin Mᵀ) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    have hsub : Matrix.mulVecLin Mᵀ (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have hsum : ∑ i : Fin 2, (a - b) i • (![u, v] i) = 0 := by
      ext j
      have hj : (Matrix.mulVec Mᵀ (a - b)) j = 0 := congrFun hsub j
      rw [Matrix.mulVec_transpose, Matrix.vecMul, dotProduct] at hj
      simpa [M, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj
    have hlin := (Fintype.linearIndependent_iff.mp hInd) (a - b) hsum
    ext i
    exact sub_eq_zero.mp (hlin i)
  have hRankMt : Module.finrank K (LinearMap.range (Matrix.mulVecLin Mᵀ)) = 2 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin Mᵀ)
    rw [hKerMt, finrank_bot, add_zero, Module.finrank_fin_fun] at hrk
    exact hrk
  have hRankM : Module.finrank K (LinearMap.range (Matrix.mulVecLin M)) = 2 := by
    change M.rank = 2
    rw [← Matrix.rank_transpose]
    exact hRankMt
  have hRangeEq : LinearMap.range (congruenceNullMap C D x) = LinearMap.range (Matrix.mulVecLin M) := by
    rw [hEq]
  have hRank := LinearMap.finrank_range_add_finrank_ker (congruenceNullMap C D x)
  rw [hRangeEq, hRankM, Module.finrank_fin_fun] at hRank
  refine ⟨by omega, ?_⟩
  intro y hy j₀ hj₀
  have hux : ∑ k, u k * x k = 0 := by
    simpa [u, dotProduct] using complexMatrix_mulVec_dot_self C x
  have hvx : ∑ k, v k * x k = 0 := by
    simpa [v, dotProduct] using complexMatrix_mulVec_dot_self D x
  have hy0 : congruenceNullMap C D x y = 0 := LinearMap.mem_ker.mp hy
  have huy : ∑ k, u k * y k = 0 := by
    simpa [congruenceNullMap, u, dotProduct] using congrFun hy0 0
  have hvy : ∑ k, v k * y k = 0 := by
    simpa [congruenceNullMap, v, dotProduct] using congrFun hy0 1
  exact ray_axis_proportional_of_four_incidences x y u v hux huy hvx hvy j₀ hj₀

/-- Discriminant of the congruence pencil `s C + t D` (`Plücker Nos. 73–95`). -/
def pencilDiscriminant {R : Type*} [Ring R] (C D : KleinQuadric.Plucker6 R) : R :=
  (C.polar D) ^ 2 - 4 * C.kleinQ * D.kleinQ

theorem pencil_quadratic_completion {R : Type*} [CommRing R]
    (C D : KleinQuadric.Plucker6 R) (s t : R) :
    4 * C.kleinQ * ((Plucker6.scale s C).add (Plucker6.scale t D)).kleinQ =
      (2 * C.kleinQ * s + (C.polar D) * t) ^ 2 - pencilDiscriminant C D * t ^ 2 := by
  rw [kleinQ_homogeneous_pencil]
  simp only [pencilDiscriminant]
  ring

/-- Hyperbolic congruence (`Δ > 0`, `C.kleinQ ≠ 0`): the pencil contains two distinct skew real
directrices `D₁, D₂` with `D₁.IsKlein`, `D₂.IsKlein`, and `D₁.polar D₂ ≠ 0` (`No. 76`). -/
theorem pencil_classification_hyperbolic (C D : KleinQuadric.Plucker6 ℝ)
    (hC : C.kleinQ ≠ 0) (hpos : 0 < pencilDiscriminant C D) :
    let r := Real.sqrt (pencilDiscriminant C D)
    let D₁ := (Plucker6.scale (-(C.polar D) + r) C).add (Plucker6.scale (2 * C.kleinQ) D)
    let D₂ := (Plucker6.scale (-(C.polar D) - r) C).add (Plucker6.scale (2 * C.kleinQ) D)
    D₁.IsKlein ∧ D₂.IsKlein ∧ D₁.polar D₂ ≠ 0 := by
  intro r D₁ D₂
  have hr2 : r ^ 2 = pencilDiscriminant C D := Real.sq_sqrt (le_of_lt hpos)
  have hD1 : D₁.IsKlein := by
    rw [Plucker6.IsKlein, kleinQ_homogeneous_pencil]
    have h4 : 4 * C.kleinQ * ((-(C.polar D) + r) ^ 2 * C.kleinQ +
        (-(C.polar D) + r) * (2 * C.kleinQ) * C.polar D + (2 * C.kleinQ) ^ 2 * D.kleinQ) = 0 := by
      have hid : (-(C.polar D) + r) ^ 2 * C.kleinQ +
          (-(C.polar D) + r) * (2 * C.kleinQ) * C.polar D + (2 * C.kleinQ) ^ 2 * D.kleinQ =
          C.kleinQ * (r ^ 2 - pencilDiscriminant C D) := by
        simp only [pencilDiscriminant]; ring
      rw [hid, hr2, sub_self, mul_zero, mul_zero]
    exact (mul_eq_zero.mp h4).resolve_left (mul_ne_zero (by norm_num) hC)
  have hD2 : D₂.IsKlein := by
    rw [Plucker6.IsKlein, kleinQ_homogeneous_pencil]
    have h4 : 4 * C.kleinQ * ((-(C.polar D) - r) ^ 2 * C.kleinQ +
        (-(C.polar D) - r) * (2 * C.kleinQ) * C.polar D + (2 * C.kleinQ) ^ 2 * D.kleinQ) = 0 := by
      have hid : (-(C.polar D) - r) ^ 2 * C.kleinQ +
          (-(C.polar D) - r) * (2 * C.kleinQ) * C.polar D + (2 * C.kleinQ) ^ 2 * D.kleinQ =
          C.kleinQ * (r ^ 2 - pencilDiscriminant C D) := by
        simp only [pencilDiscriminant]; ring
      rw [hid, hr2, sub_self, mul_zero, mul_zero]
    exact (mul_eq_zero.mp h4).resolve_left (mul_ne_zero (by norm_num) hC)
  have hpol : D₁.polar D₂ = -4 * C.kleinQ * pencilDiscriminant C D := by
    have hadd : (D₁.add D₂).kleinQ =
        ((Plucker6.scale (-2 * C.polar D) C).add (Plucker6.scale (4 * C.kleinQ) D)).kleinQ := by
      congr 1
      ext <;> simp [D₁, D₂, Plucker6.add, Plucker6.scale] <;> ring
    have hsum : D₁.polar D₂ = (D₁.add D₂).kleinQ - D₁.kleinQ - D₂.kleinQ := by
      simp [Plucker6.polar]
    rw [hsum, hD1, hD2, hadd, kleinQ_homogeneous_pencil]
    simp only [pencilDiscriminant]
    ring
  refine ⟨hD1, hD2, ?_⟩
  rw [hpol]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hC) (ne_of_gt hpos)

/-- Parabolic congruence (`Δ = 0`, `C.kleinQ ≠ 0`): there is a unique coalesced directrix line
in the pencil (`No. 78`). -/
theorem pencil_classification_parabolic (C D : KleinQuadric.Plucker6 ℝ)
    (hC : C.kleinQ ≠ 0) (hzero : pencilDiscriminant C D = 0) :
    let D₀ := (Plucker6.scale (-(C.polar D)) C).add (Plucker6.scale (2 * C.kleinQ) D)
    D₀.IsKlein ∧
      ∀ s t : ℝ, ((Plucker6.scale s C).add (Plucker6.scale t D)).IsKlein ↔
        2 * C.kleinQ * s + (C.polar D) * t = 0 := by
  intro D₀
  have hD0 : D₀.IsKlein := by
    rw [Plucker6.IsKlein, kleinQ_homogeneous_pencil]
    have h4 : (-(C.polar D)) ^ 2 * C.kleinQ +
        (-(C.polar D)) * (2 * C.kleinQ) * C.polar D + (2 * C.kleinQ) ^ 2 * D.kleinQ =
        -C.kleinQ * pencilDiscriminant C D := by
      simp only [pencilDiscriminant]; ring
    rw [h4, hzero, mul_zero]
  refine ⟨hD0, fun s t => ?_⟩
  have hcomp := pencil_quadratic_completion C D s t
  rw [hzero, zero_mul, sub_zero] at hcomp
  constructor
  · intro hk
    rw [Plucker6.IsKlein] at hk
    rw [hk, mul_zero] at hcomp
    exact sq_eq_zero_iff.mp hcomp.symm
  · intro hlin
    rw [Plucker6.IsKlein]
    have h4k : 4 * C.kleinQ * ((Plucker6.scale s C).add (Plucker6.scale t D)).kleinQ = 0 := by
      rw [hcomp, hlin, zero_pow (by norm_num)]
    exact (mul_eq_zero.mp h4k).resolve_left (mul_ne_zero (by norm_num) hC)

/-- Elliptic congruence (`Δ < 0`, `C.kleinQ ≠ 0`): no real nonzero pencil member lies on the Klein
quadric (conjugate-imaginary directrices over `ℂ`) (`No. 77`). -/
theorem pencil_classification_elliptic (C D : KleinQuadric.Plucker6 ℝ)
    (hC : C.kleinQ ≠ 0) (hneg : pencilDiscriminant C D < 0) (s t : ℝ) (hst : s ≠ 0 ∨ t ≠ 0) :
    ¬ ((Plucker6.scale s C).add (Plucker6.scale t D)).IsKlein := by
  intro hk
  rw [Plucker6.IsKlein] at hk
  have hcomp := pencil_quadratic_completion C D s t
  rw [hk, mul_zero] at hcomp
  have hsum : (2 * C.kleinQ * s + (C.polar D) * t) ^ 2 + (-pencilDiscriminant C D) * t ^ 2 = 0 := by
    linarith [hcomp]
  have ht0 : (-pencilDiscriminant C D) * t ^ 2 = 0 := by
    nlinarith [sq_nonneg (2 * C.kleinQ * s + (C.polar D) * t), sq_nonneg t]
  have ht : t = 0 := by
    rcases mul_eq_zero.mp ht0 with hdisc | ht2
    · linarith [hneg]
    · exact sq_eq_zero_iff.mp ht2
  rw [ht, mul_zero, zero_pow (by norm_num), mul_zero, add_zero, add_zero] at hsum
  have hs0 : 2 * C.kleinQ * s = 0 := sq_eq_zero_iff.mp hsum
  have hs : s = 0 := (mul_eq_zero.mp hs0).resolve_left (mul_ne_zero (by norm_num) hC)
  exact hst.elim (fun h => h hs) (fun h => h ht)

/-- Intersecting-directrices degenerate pencil: when both generators are special and incident,
every linear combination in the pencil is special (`No. 80`). -/
theorem pencil_classification_intersecting {R : Type*} [CommRing R]
    (C D : KleinQuadric.Plucker6 R)
    (hC : C.IsKlein) (hD : D.IsKlein) (hCD : C.Incident D) (s t : R) :
    ((Plucker6.scale s C).add (Plucker6.scale t D)).IsKlein := by
  rw [Plucker6.IsKlein, kleinQ_homogeneous_pencil]
  rw [Plucker6.IsKlein] at hC hD
  rw [Plucker6.Incident] at hCD
  rw [hC, hD, hCD]
  ring

end CongruenceAndPencilClassification

section CubicCylindroid

/-- Direction vector `(c, s, 0)` of a generator of Plücker's cylindroid (`Nos. 96–104`, `pp. 97–106`). -/
def cylindroidDir (c s : ℝ) : Vec3 := ![c, s, 0]

/-- Moment vector `(c * k₁, s * k₂, 0)` along the cylindroid generator parametrized by principal
pitches `k₁, k₂` and angle `(c, s)` with `c² + s² = 1`. -/
def cylindroidMom (k₁ k₂ c s : ℝ) : Vec3 := ![c * k₁, s * k₂, 0]

theorem cylindroid_axisFoot (k₁ k₂ c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (axisFoot (cylindroidDir c s) (cylindroidMom k₁ k₂ c s)).1 =
      ![0, 0, c * s * (k₂ - k₁)] := by
  have hdd : cylindroidDir c s ⬝ᵥ cylindroidDir c s = 1 := by
    rw [dotProduct, Fin.sum_univ_three]
    change c * c + s * s + 0 * 0 = 1
    linarith [hcs]
  ext i
  change ((cylindroidDir c s ⬝ᵥ cylindroidDir c s)⁻¹ •
      crossProduct (cylindroidDir c s) (cylindroidMom k₁ k₂ c s)) i =
    ![0, 0, c * s * (k₂ - k₁)] i
  rw [hdd, inv_one, one_smul]
  dsimp only [crossProduct, LinearMap.mk₂_apply, cylindroidDir, cylindroidMom]
  fin_cases i
  · change s * 0 - 0 * (s * k₂) = 0; ring
  · change 0 * (c * k₁) - c * 0 = 0; ring
  · change c * (s * k₂) - s * (c * k₁) = c * s * (k₂ - k₁); ring

/-- Point on the `(c, s)`-generator of the cylindroid at parameter `t` along the central foot. -/
def cylindroidPoint (k₁ k₂ c s t : ℝ) : Vec3 :=
  ![0, 0, c * s * (k₂ - k₁)] + t • cylindroidDir c s

/-- Plücker's cubic cylindroid surface equation `z (x² + y²) = (k₂ - k₁) x y` (`Eq. (98)`, `p. 99`). -/
theorem cylindroid_cubic_surface_eq (k₁ k₂ c s t : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    let p := cylindroidPoint k₁ k₂ c s t
    p 2 * (p 0 ^ 2 + p 1 ^ 2) = (k₂ - k₁) * p 0 * p 1 := by
  intro p
  have hp0 : p 0 = t * c := by
    change 0 + t * c = t * c; ring
  have hp1 : p 1 = t * s := by
    change 0 + t * s = t * s; ring
  have hp2 : p 2 = c * s * (k₂ - k₁) := by
    change c * s * (k₂ - k₁) + t * 0 = c * s * (k₂ - k₁); ring
  rw [hp0, hp1, hp2]
  have hid :
      c * s * (k₂ - k₁) * ((t * c) ^ 2 + (t * s) ^ 2) - (k₂ - k₁) * (t * c) * (t * s) =
        c * s * (k₂ - k₁) * t ^ 2 * ((c ^ 2 + s ^ 2) - 1) := by ring
  rw [hcs, sub_self, mul_zero] at hid
  exact sub_eq_zero.mp hid

/-- A nondegenerate cylindroid (`k₁ ≠ k₂`) is genuinely three-dimensional (not contained in any
single plane) (`No. 99`). -/
theorem cylindroid_not_planar_of_ne (k₁ k₂ : ℝ) (hk : k₁ ≠ k₂)
    (a b c d : ℝ) (hnon : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∃ (c' s' t : ℝ),
      c' ^ 2 + s' ^ 2 = 1 ∧
        let p := cylindroidPoint k₁ k₂ c' s' t
        a * p 0 + b * p 1 + c * p 2 + d ≠ 0 := by
  by_contra hAll
  push Not at hAll
  have h000 : a * 0 + b * 0 + c * 0 + d = 0 := by
    simpa [cylindroidPoint, cylindroidDir] using hAll 1 0 0 (by norm_num)
  have hd : d = 0 := by linarith
  have h101 : a * 1 + b * 0 + c * 0 + d = 0 := by
    simpa [cylindroidPoint, cylindroidDir] using hAll 1 0 1 (by norm_num)
  have ha : a = 0 := by linarith
  have h011 : a * 0 + b * 1 + c * 0 + d = 0 := by
    simpa [cylindroidPoint, cylindroidDir] using hAll 0 1 1 (by norm_num)
  have hb : b = 0 := by linarith
  have h345 :
      a * 0 + b * 0 + c * ((3 / 5 : ℝ) * (4 / 5) * (k₂ - k₁)) + d = 0 := by
    simpa [cylindroidPoint, cylindroidDir] using
      hAll (3 / 5) (4 / 5) 0 (by norm_num)
  rw [ha, hb, hd] at h345
  have hc0 : c * ((12 / 25 : ℝ) * (k₂ - k₁)) = 0 := by linarith
  have hc : c = 0 :=
    (mul_eq_zero.mp hc0).resolve_right (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hk.symm))
  exact hnon.elim (fun h => h ha) (fun h => h.elim (fun h' => h' hb) (fun h' => h' hc))

end CubicCylindroid

section ThreeComplexWebAndRegulus

/-- Orthogonal complement (conjugate linear complex web) with respect to the Klein bilinear pairing
`u ⬝ᵥ (polarDotMatrix *ᵥ v)` (`Plücker Abth. I §3, Nos. 108–124`, `pp. 120–135`). -/
def kleinPolarOrth {K : Type*} [Field K] (W : Submodule K (Fin 6 → K)) :
    Submodule K (Fin 6 → K) where
  carrier := {y | ∀ w ∈ W, w ⬝ᵥ (polarDotMatrix *ᵥ y) = 0}
  zero_mem' w _ := by simp
  add_mem' hx hy w hw := by
    rw [Matrix.mulVec_add, dotProduct_add, hx w hw, hy w hw, add_zero]
  smul_mem' r x hx w hw := by
    rw [Matrix.mulVec_smul, dotProduct_smul, hx w hw, smul_zero]

private lemma polarDotMatrix_transpose {R : Type*} [CommRing R] :
    (polarDotMatrix : Matrix (Fin 6) (Fin 6) R)ᵀ = polarDotMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma polar_bilin_symm {R : Type*} [CommRing R] (u v : Fin 6 → R) :
    u ⬝ᵥ (polarDotMatrix *ᵥ v) = v ⬝ᵥ (polarDotMatrix *ᵥ u) := by
  calc
    u ⬝ᵥ (polarDotMatrix *ᵥ v) = (u ᵥ* polarDotMatrix) ⬝ᵥ v :=
      Matrix.dotProduct_mulVec u polarDotMatrix v
    _ = (u ᵥ* (polarDotMatrix : Matrix (Fin 6) (Fin 6) R)ᵀ) ⬝ᵥ v := by
      rw [polarDotMatrix_transpose]
    _ = (polarDotMatrix *ᵥ u) ⬝ᵥ v := by rw [Matrix.vecMul_transpose]
    _ = v ⬝ᵥ (polarDotMatrix *ᵥ u) := dotProduct_comm _ _

theorem kleinPolarOrth_symm_mem {K : Type*} [Field K] (W : Submodule K (Fin 6 → K)) :
    W ≤ kleinPolarOrth (kleinPolarOrth W) := by
  intro w hw y hy
  rw [polar_bilin_symm]
  exact hy w hw

private lemma finrank_kleinPolarOrth_add {K : Type*} [Field K] (W : Submodule K (Fin 6 → K)) :
    Module.finrank K W + Module.finrank K (kleinPolarOrth W) = 6 := by
  let b := Module.finBasis K W
  let v : Fin (Module.finrank K W) → (Fin 6 → K) := fun i => (b i : Fin 6 → K)
  have hv_ind : LinearIndependent K v :=
    b.linearIndependent.map' (Submodule.subtype W) (Submodule.ker_subtype W)
  have hv_img : LinearIndependent K (fun i => polarDotMatrix *ᵥ v i) :=
    hv_ind.map' (Matrix.mulVecLin polarDotMatrix)
      (LinearMap.ker_eq_bot.mpr polarDotMatrix_mulVec_injective)
  let M : Matrix (Fin (Module.finrank K W)) (Fin 6) K :=
    Matrix.of (fun i => polarDotMatrix *ᵥ v i)
  have hKerEq : kleinPolarOrth W = LinearMap.ker (Matrix.mulVecLin M) := by
    ext y
    change (∀ w ∈ W, w ⬝ᵥ (polarDotMatrix *ᵥ y) = 0) ↔ Matrix.mulVec M y = 0
    constructor
    · intro hy
      ext i
      change (polarDotMatrix *ᵥ v i) ⬝ᵥ y = 0
      rw [dotProduct_comm, ← polar_bilin_symm]
      exact hy (v i) (b i).2
    · intro hy w hw
      have hw_rep : w = ∑ i, b.repr ⟨w, hw⟩ i • v i := by
        have h0 : (⟨w, hw⟩ : W) = ∑ i, b.repr ⟨w, hw⟩ i • b i := (b.sum_repr ⟨w, hw⟩).symm
        have h1 := congrArg Subtype.val h0
        simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h1
        exact h1
      rw [hw_rep, sum_dotProduct]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_dotProduct, polar_bilin_symm, dotProduct_comm]
      have hmi : (polarDotMatrix *ᵥ v i) ⬝ᵥ y = 0 := congrFun hy i
      rw [hmi, smul_zero]
  have hKerMt : LinearMap.ker (Matrix.mulVecLin Mᵀ) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have hsub : Matrix.mulVecLin Mᵀ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hsum : ∑ i : Fin (Module.finrank K W), (x - y) i • (polarDotMatrix *ᵥ v i) = 0 := by
      ext j
      have hj : (Matrix.mulVec Mᵀ (x - y)) j = 0 := congrFun hsub j
      rw [Matrix.mulVec_transpose, Matrix.vecMul, dotProduct] at hj
      simpa [M, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj
    have hlin := (Fintype.linearIndependent_iff.mp hv_img) (x - y) hsum
    ext i
    exact sub_eq_zero.mp (hlin i)
  have hRankMt : Module.finrank K (LinearMap.range (Matrix.mulVecLin Mᵀ)) =
      Module.finrank K W := by
    have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin Mᵀ)
    rw [hKerMt, finrank_bot, add_zero, Module.finrank_fin_fun] at hrk
    exact hrk
  have hRankM : Module.finrank K (LinearMap.range (Matrix.mulVecLin M)) = Module.finrank K W := by
    change M.rank = Module.finrank K W
    rw [← Matrix.rank_transpose]
    exact hRankMt
  have hRank := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
  rw [hRankM, ← hKerEq, Module.finrank_fin_fun] at hRank
  exact hRank

/-- A 3-dimensional linear complex web has a 3-dimensional conjugate orthogonal web (`No. 110`). -/
theorem finrank_kleinPolarOrth_eq_three {K : Type*} [Field K]
    (W : Submodule K (Fin 6 → K)) (hW : Module.finrank K W = 3) :
    Module.finrank K (kleinPolarOrth W) = 3 := by
  have h := finrank_kleinPolarOrth_add W
  rw [hW] at h
  omega

/-- Double Klein orthogonality is an exact involution on subspaces of `K⁶` (`No. 111`). -/
theorem kleinPolarOrth_involutive {K : Type*} [Field K] (W : Submodule K (Fin 6 → K)) :
    kleinPolarOrth (kleinPolarOrth W) = W := by
  have h1 := finrank_kleinPolarOrth_add W
  have h2 := finrank_kleinPolarOrth_add (kleinPolarOrth W)
  have hfe : Module.finrank K W = Module.finrank K (kleinPolarOrth (kleinPolarOrth W)) := by omega
  exact (Submodule.eq_of_le_of_finrank_eq (kleinPolarOrth_symm_mem W) hfe).symm

/-- Canonical ruled hyperboloid quadric `x₀² + x₃² - x₁² - x₂² = 0` (`Nos. 125–142`). -/
def hyperboloidQuadric {R : Type*} [Ring R] (x : Fin 4 → R) : R :=
  x 0 ^ 2 + x 3 ^ 2 - x 1 ^ 2 - x 2 ^ 2

/-- Positive-system ruling point on the hyperboloid (`(s₀, s₁)` line, `(t₀, t₁)` point parameter). -/
def rulingPlusPoint {R : Type*} [Ring R] (s₀ s₁ t₀ t₁ : R) : Fin 4 → R :=
  ![s₀ * t₀ + s₁ * t₁, s₁ * t₁ - s₀ * t₀, s₀ * t₁ + s₁ * t₀, s₀ * t₁ - s₁ * t₀]

/-- Opposite-system ruling point on the hyperboloid (`(u₀, u₁)` line, `(v₀, v₁)` point parameter). -/
def rulingMinusPoint {R : Type*} [Ring R] (u₀ u₁ v₀ v₁ : R) : Fin 4 → R :=
  ![u₀ * v₀ + u₁ * v₁, u₁ * v₁ - u₀ * v₀, u₁ * v₀ + u₀ * v₁, u₁ * v₀ - u₀ * v₁]

theorem rulingPlus_on_quadric {R : Type*} [CommRing R] (s₀ s₁ t₀ t₁ : R) :
    hyperboloidQuadric (rulingPlusPoint s₀ s₁ t₀ t₁) = 0 := by
  change (s₀ * t₀ + s₁ * t₁) ^ 2 + (s₀ * t₁ - s₁ * t₀) ^ 2 -
    (s₁ * t₁ - s₀ * t₀) ^ 2 - (s₀ * t₁ + s₁ * t₀) ^ 2 = 0
  ring

theorem rulingMinus_on_quadric {R : Type*} [CommRing R] (u₀ u₁ v₀ v₁ : R) :
    hyperboloidQuadric (rulingMinusPoint u₀ u₁ v₀ v₁) = 0 := by
  change (u₀ * v₀ + u₁ * v₁) ^ 2 + (u₁ * v₀ - u₀ * v₁) ^ 2 -
    (u₁ * v₁ - u₀ * v₀) ^ 2 - (u₁ * v₀ + u₀ * v₁) ^ 2 = 0
  ring

/-- Any line of the positive regulus meets any line of the negative regulus at
`rulingPlusPoint s₀ s₁ u₀ u₁ = rulingMinusPoint u₀ u₁ s₀ s₁` (`Nos. 125–135`). -/
theorem opposite_reguli_common_point {R : Type*} [CommRing R] (s₀ s₁ u₀ u₁ : R) :
    rulingPlusPoint s₀ s₁ u₀ u₁ = rulingMinusPoint u₀ u₁ s₀ s₁ := by
  ext i
  fin_cases i <;> simp [rulingPlusPoint, rulingMinusPoint] <;> ring

def rulingPlusLine {R : Type*} [Ring R] (s₀ s₁ : R) : KleinQuadric.Plucker6 R :=
  rayPlucker (rulingPlusPoint s₀ s₁ 1 0) (rulingPlusPoint s₀ s₁ 0 1)

def rulingMinusLine {R : Type*} [Ring R] (u₀ u₁ : R) : KleinQuadric.Plucker6 R :=
  rayPlucker (rulingMinusPoint u₀ u₁ 1 0) (rulingMinusPoint u₀ u₁ 0 1)

theorem opposite_reguli_incident {R : Type*} [CommRing R] (s₀ s₁ u₀ u₁ : R) :
    (rulingPlusLine s₀ s₁).Incident (rulingMinusLine u₀ u₁) := by
  have hp : rulingPlusLine s₀ s₁ =
      ⟨2 * s₀ * s₁, s₀ ^ 2 - s₁ ^ 2, s₀ ^ 2 + s₁ ^ 2,
       -(s₀ ^ 2 + s₁ ^ 2), s₁ ^ 2 - s₀ ^ 2, 2 * s₀ * s₁⟩ := by
    ext <;> simp [rulingPlusLine, rayPlucker, rulingPlusPoint] <;> ring
  have hm : rulingMinusLine u₀ u₁ =
      ⟨2 * u₀ * u₁, u₀ ^ 2 - u₁ ^ 2, -(u₀ ^ 2 + u₁ ^ 2),
       -(u₀ ^ 2 + u₁ ^ 2), -(u₁ ^ 2 - u₀ ^ 2), -(2 * u₀ * u₁)⟩ := by
    ext <;> simp [rulingMinusLine, rayPlucker, rulingMinusPoint] <;> ring
  rw [hp, hm]
  simp only [Plucker6.Incident, Plucker6.polar, Plucker6.add, Plucker6.kleinQ]
  ring

end ThreeComplexWebAndRegulus

section No143Countermodel

/-- `[countermodel_found]` **Plücker No. 143 cone impossibility (`pp. 145–147`)**:
Any family of linear complexes `C : ι → Plucker6 ℝ` intersecting a fixed vertex `v₀ = ![1, 0, 0, 0]`
carves out a linear cone `(C i).p23 * y₁ - (C i).p13 * y₂ + (C i).p12 * y₃ = 0` on directions
`(y₁, y₂, y₃)`, which is closed under vector addition and therefore cannot coincide with the
irreducible quadratic cone `y₁² + y₂² - y₃² = 0` (witnessed by `(1, 0, 1)` and `(-1, 0, 1)`, whose
sum `(0, 0, 2)` fails `0 + 0 - 4 = 0`). -/
theorem no143_quadratic_cone_not_cut_by_linear_complexes :
    ¬ ∃ (ι : Type) (C : ι → KleinQuadric.Plucker6 ℝ),
      ∀ y₁ y₂ y₃ : ℝ,
        (y₁ ^ 2 + y₂ ^ 2 - y₃ ^ 2 = 0) ↔
          ∀ i : ι, (C i).Incident (rayPlucker ![1, 0, 0, 0] ![0, y₁, y₂, y₃]) := by
  rintro ⟨ι, C, hC⟩
  have hpos : ∀ i : ι, (C i).Incident (rayPlucker ![1, 0, 0, 0] ![0, 1, 0, 1]) :=
    (hC 1 0 1).mp (by norm_num)
  have hneg : ∀ i : ι, (C i).Incident (rayPlucker ![1, 0, 0, 0] ![0, -1, 0, 1]) :=
    (hC (-1) 0 1).mp (by norm_num)
  have hlin : ∀ (i : ι) (y₁ y₂ y₃ : ℝ),
      (C i).Incident (rayPlucker ![1, 0, 0, 0] ![0, y₁, y₂, y₃]) ↔
        y₁ * (C i).p23 - y₂ * (C i).p13 + y₃ * (C i).p12 = 0 := by
    intro i y₁ y₂ y₃
    have hr : rayPlucker ![1, 0, 0, 0] ![0, y₁, y₂, y₃] = ⟨y₁, y₂, y₃, 0, 0, 0⟩ := by
      ext <;> simp [rayPlucker]
    rw [hr]
    simp only [Plucker6.Incident, Plucker6.polar, Plucker6.add, Plucker6.kleinQ]
    constructor <;> intro h <;> linarith
  have hsum : ∀ i : ι, (C i).Incident (rayPlucker ![1, 0, 0, 0] ![0, 0, 0, 2]) := by
    intro i
    have h1 := (hlin i 1 0 1).mp (hpos i)
    have h2 := (hlin i (-1) 0 1).mp (hneg i)
    rw [hlin]
    linarith
  have hquad := (hC 0 0 2).mpr hsum
  norm_num at hquad

/-- `[countermodel_found]` **Dual Plücker No. 143 conic impossibility**:
Dually in the plane `x₀ = 0`, no family of linear complexes can cut out the irreducible conic
envelope `u₁² + u₂² - u₃² = 0` via `axisAsRayPlucker ![1, 0, 0, 0] ![0, u₁, u₂, u₃]`. -/
theorem no143_plane_conic_not_enveloped_by_linear_complexes :
    ¬ ∃ (ι : Type) (C : ι → KleinQuadric.Plucker6 ℝ),
      ∀ u₁ u₂ u₃ : ℝ,
        (u₁ ^ 2 + u₂ ^ 2 - u₃ ^ 2 = 0) ↔
          ∀ i : ι, (C i).Incident (axisAsRayPlucker ![1, 0, 0, 0] ![0, u₁, u₂, u₃]) := by
  rintro ⟨ι, C, hC⟩
  have hpos : ∀ i : ι, (C i).Incident (axisAsRayPlucker ![1, 0, 0, 0] ![0, 1, 0, 1]) :=
    (hC 1 0 1).mp (by norm_num)
  have hneg : ∀ i : ι, (C i).Incident (axisAsRayPlucker ![1, 0, 0, 0] ![0, -1, 0, 1]) :=
    (hC (-1) 0 1).mp (by norm_num)
  have hlin : ∀ (i : ι) (u₁ u₂ u₃ : ℝ),
      (C i).Incident (axisAsRayPlucker ![1, 0, 0, 0] ![0, u₁, u₂, u₃]) ↔
        (C i).p01 * u₁ + (C i).p02 * u₂ + (C i).p03 * u₃ = 0 := by
    intro i u₁ u₂ u₃
    have ha : axisAsRayPlucker ![1, 0, 0, 0] ![0, u₁, u₂, u₃] = ⟨0, 0, 0, u₃, -u₂, u₁⟩ := by
      ext <;> simp [axisAsRayPlucker, axisDualEquiv, rayPlucker]
    rw [ha]
    simp only [Plucker6.Incident, Plucker6.polar, Plucker6.add, Plucker6.kleinQ]
    constructor <;> intro h <;> linarith
  have hsum : ∀ i : ι, (C i).Incident (axisAsRayPlucker ![1, 0, 0, 0] ![0, 0, 0, 2]) := by
    intro i
    have h1 := (hlin i 1 0 1).mp (hpos i)
    have h2 := (hlin i (-1) 0 1).mp (hneg i)
    rw [hlin]
    linarith
  have hquad := (hC 0 0 2).mpr hsum
  norm_num at hquad

end No143Countermodel

end InfoGeometry.Projective.PluckerCongruenceCylindroidAndRegulus
