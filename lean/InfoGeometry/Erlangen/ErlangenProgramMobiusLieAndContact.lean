/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
import InfoGeometry.Canonical.GrassmannPfaffianDarbouxAlgebra
import InfoGeometry.Projective.CrossRatioMobiusInvariant
import InfoGeometry.Projective.CrossRatioPGL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# Erlangen Program (§§6–9): Inversion, Lie Sphere Geometry, Contact 5-Space & Bridges III–IV

This module formalizes Archetypes `EK₅`, `EK₆`, and `EK₇` of Felix Klein's 1872 *Erlangen Program*
(`0807.3161v1 (1).pdf`, pp. 9–18), together with **Grassmann–Plücker–Klein Bridges III & IV**:

1. **Geometry of Reciprocal Radii & `[countermodel_found]` Footnote 26 (`§6`, pp. 9–11)**:
   * Euclidean inversion `euclidInvert x = (x ⬝ᵥ x)⁻¹ • x` (`euclidInvert_involutive`,
     `euclidInvert_distSq`, `euclidInvert_crossRatioSq_invariant`, sphere–hyperplane duality).
   * Pentaspherical `5D` lightcone lift `moebiusLightconeLift` on signature `(4, 1)`, linearizing
     Euclidean inversion to reflection `u₀ ↦ -u₀`.
   * **Footnote 26 countermodel**: antiholomorphic inversion `z ↦ (star z)⁻¹` cannot be written as
     any complex fractional-linear Möbius transformation `(a z + b) / (c z + d)`
     (`klein_footnote26_inversion_not_holomorphic_mobius`), while anti-homographies `antiMobius`
     conjugate cross-ratios and compose into holomorphic Möbius maps.
2. **Lie's Sphere Geometry & Grassmann–Plücker–Klein Bridge III (`§7`, pp. 11–14, Footnote 31)**:
   * Signature `(3, 2)` Lie sphere inner product `lieBilin`, oriented circle embedding `lieCircleVec`,
     oriented tangency characterization, and explicit `O(3,2)` radius-dilation group
     `lieRadiusDilMatrix t` (`lieRadiusDilMatrix_preserves_lieBilin`, `lieRadiusDilMatrix_det`,
     `lieRadiusDilMatrix_add`, mapping points `r = 0` to circles `r = t`).
   * **Bridge III**: Linear projection `lieToGrassmannCircleProj : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)`
     to Grassmann's 1862 Lorentzian circle space (`circleVec`, `circleBilin`), linking Lie tangency
     to `GrassmannPluckerMeetAndCircleSpace.IsCircleTangent` and contrasting `O(3,2)` tangency
     invariance with `note97_syncyclic_vs_moebius_tangency`.
3. **Cremona, Contact 5-Space, Legendre Pullback & Bridge IV (`§§8–9`, pp. 14–18)**:
   * Quadratic Cremona involution `cremona2`, differential `1`-form `contactOneForm`
     (`dz - p dx - q dy`) vanishing on surface graphs, point pencils, and space curves, exact
     Legendre contact pullback (`contactOneForm_legendre_pullback`), and Clebsch connex incidence.
   * **Bridge IV**: Embeds Klein's 5D contact structure `ω ∧ Ω²` into `ExteriorAlgebra ℝ (Fin 5 → ℝ)`,
     proving strict nondegeneracy `ω * Ω^2 ≠ 0` (`volCoord = -2 ≠ 0`) together with
     `GrassmannPfaffianDarbouxAlgebra.grassmann_no511_pfaff_vanishing` (`n = 2`, degree `5 ≠ 0` vs `7 = 0`).
-/

noncomputable section

namespace InfoGeometry.Erlangen.ErlangenProgramMobiusLieAndContact

open InfoGeometry.Projective.ExteriorRegressive
open InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
open InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
open InfoGeometry.Canonical.GrassmannPfaffianDarbouxAlgebra
open Matrix

/-! ## 1. Reciprocal Radii, Pentaspherical Lightcone, & Footnote 26 Countermodel (§6) -/

section ReciprocalRadiiAndMobius

/-- Matrix non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem matrix2C_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

/-- Matrix non-commutativity witness for `Matrix (Fin 4) (Fin 4) R`. -/
theorem matrix4_noncomm {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 4) (Fin 4) R, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

/-- Matrix non-commutativity witness for `Matrix (Fin 5) (Fin 5) ℝ`. -/
theorem matrix5R_noncomm :
    ∃ A B : Matrix (Fin 5) (Fin 5) ℝ, A * B ≠ B * A := by
  refine ⟨Matrix.of (fun i j => if i = 0 ∧ j = 1 then 1 else 0),
          Matrix.of (fun i j => if i = 1 ∧ j = 0 then 1 else 0), ?_⟩
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp [Matrix.mul_apply] at h00

/-- Euclidean inversion with respect to the unit sphere `x ↦ (x ⬝ᵥ x)⁻¹ • x` (`§6`, p. 9). -/
def euclidInvert {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  ((x ⬝ᵥ x)⁻¹) • x

theorem euclidInvert_involutive {n : ℕ} {x : Fin n → ℝ} (hx : x ⬝ᵥ x ≠ 0) :
    euclidInvert (euclidInvert x) = x := by
  dsimp [euclidInvert]
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_smul]
  have hsc : (((x ⬝ᵥ x)⁻¹ * ((x ⬝ᵥ x)⁻¹ * (x ⬝ᵥ x)))⁻¹) * (x ⬝ᵥ x)⁻¹ = 1 := by
    field_simp [hx]
  rw [hsc, one_smul]

/-- Conformal squared-distance scaling under Euclidean inversion (`§6`, p. 9). -/
theorem euclidInvert_distSq {n : ℕ} {x y : Fin n → ℝ}
    (hx : x ⬝ᵥ x ≠ 0) (hy : y ⬝ᵥ y ≠ 0) :
    (euclidInvert x - euclidInvert y) ⬝ᵥ (euclidInvert x - euclidInvert y) =
      ((x - y) ⬝ᵥ (x - y)) / ((x ⬝ᵥ x) * (y ⬝ᵥ y)) := by
  dsimp [euclidInvert]
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, smul_dotProduct,
    dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul,
    dotProduct_smul]
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
  simp only [smul_eq_mul]
  have hxy : y ⬝ᵥ x = x ⬝ᵥ y := dotProduct_comm y x
  rw [hxy]
  field_simp [hx, hy]
  ring

/-- Four-point squared Euclidean distance cross-ratio is strictly invariant under inversion (`§6`). -/
theorem euclidInvert_crossRatioSq_invariant {n : ℕ} {x₁ x₂ x₃ x₄ : Fin n → ℝ}
    (h₁ : x₁ ⬝ᵥ x₁ ≠ 0) (h₂ : x₂ ⬝ᵥ x₂ ≠ 0) (h₃ : x₃ ⬝ᵥ x₃ ≠ 0) (h₄ : x₄ ⬝ᵥ x₄ ≠ 0)
    (h13 : (x₁ - x₃) ⬝ᵥ (x₁ - x₃) ≠ 0) (h24 : (x₂ - x₄) ⬝ᵥ (x₂ - x₄) ≠ 0) :
    (((euclidInvert x₁ - euclidInvert x₂) ⬝ᵥ (euclidInvert x₁ - euclidInvert x₂)) *
        ((euclidInvert x₃ - euclidInvert x₄) ⬝ᵥ (euclidInvert x₃ - euclidInvert x₄))) /
      (((euclidInvert x₁ - euclidInvert x₃) ⬝ᵥ (euclidInvert x₁ - euclidInvert x₃)) *
        ((euclidInvert x₂ - euclidInvert x₄) ⬝ᵥ (euclidInvert x₂ - euclidInvert x₄))) =
      (((x₁ - x₂) ⬝ᵥ (x₁ - x₂)) * ((x₃ - x₄) ⬝ᵥ (x₃ - x₄))) /
        (((x₁ - x₃) ⬝ᵥ (x₁ - x₃)) * ((x₂ - x₄) ⬝ᵥ (x₂ - x₄))) := by
  rw [euclidInvert_distSq h₁ h₂, euclidInvert_distSq h₃ h₄,
      euclidInvert_distSq h₁ h₃, euclidInvert_distSq h₂ h₄]
  field_simp [h₁, h₂, h₃, h₄, h13, h24]

/-- Spheres `a (x⬝x) + 2 (b⬝x) + c = 0` invert to spheres/hyperplanes with swapped `(a, c)` (`§6`). -/
theorem euclidInvert_sphere_duality {n : ℕ} (a c : ℝ) (b x : Fin n → ℝ) (hx : x ⬝ᵥ x ≠ 0) :
    a * (x ⬝ᵥ x) + 2 * (b ⬝ᵥ x) + c = 0 ↔
      c * (euclidInvert x ⬝ᵥ euclidInvert x) + 2 * (b ⬝ᵥ euclidInvert x) + a = 0 := by
  dsimp [euclidInvert]
  rw [smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have hid : c * ((x ⬝ᵥ x)⁻¹ * ((x ⬝ᵥ x)⁻¹ * (x ⬝ᵥ x))) + 2 * ((x ⬝ᵥ x)⁻¹ * (b ⬝ᵥ x)) + a =
      (a * (x ⬝ᵥ x) + 2 * (b ⬝ᵥ x) + c) / (x ⬝ᵥ x) := by
    field_simp [hx]
    ring
  rw [hid]
  exact (div_eq_zero_iff.trans (or_iff_left hx)).symm

/-- Signature `(4, 1)` pentaspherical bilinear form on `Fin 5 → ℝ` (`§6`, p. 10; `Footnote 31`). -/
def moebiusBilin5 (u v : Fin 5 → ℝ) : ℝ :=
  -u 4 * v 4 + u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

/-- Stereographic paraboloid/lightcone lift `ℝ³ → Fin 5 → ℝ` linearizing the Möbius group (`§6`). -/
def moebiusLightconeLift (x : Fin 3 → ℝ) : Fin 5 → ℝ :=
  ![(1 - x ⬝ᵥ x) / 2, x 0, x 1, x 2, (1 + x ⬝ᵥ x) / 2]

theorem moebiusLightconeLift_isNull (x : Fin 3 → ℝ) :
    moebiusBilin5 (moebiusLightconeLift x) (moebiusLightconeLift x) = 0 := by
  have h0 : moebiusLightconeLift x 0 = (1 - x ⬝ᵥ x) / 2 := rfl
  have h1 : moebiusLightconeLift x 1 = x 0 := rfl
  have h2 : moebiusLightconeLift x 2 = x 1 := rfl
  have h3 : moebiusLightconeLift x 3 = x 2 := rfl
  have h4 : moebiusLightconeLift x 4 = (1 + x ⬝ᵥ x) / 2 := rfl
  rw [moebiusBilin5, h0, h1, h2, h3, h4]
  have hn : x 0 * x 0 + x 1 * x 1 + x 2 * x 2 = x ⬝ᵥ x := by
    simp [dotProduct, Fin.sum_univ_three]
  linarith [hn]

theorem moebiusBilin5_chord (x y : Fin 3 → ℝ) :
    moebiusBilin5 (moebiusLightconeLift x) (moebiusLightconeLift y) =
      -((x - y) ⬝ᵥ (x - y)) / 2 := by
  have hx0 : moebiusLightconeLift x 0 = (1 - x ⬝ᵥ x) / 2 := rfl
  have hx1 : moebiusLightconeLift x 1 = x 0 := rfl
  have hx2 : moebiusLightconeLift x 2 = x 1 := rfl
  have hx3 : moebiusLightconeLift x 3 = x 2 := rfl
  have hx4 : moebiusLightconeLift x 4 = (1 + x ⬝ᵥ x) / 2 := rfl
  have hy0 : moebiusLightconeLift y 0 = (1 - y ⬝ᵥ y) / 2 := rfl
  have hy1 : moebiusLightconeLift y 1 = y 0 := rfl
  have hy2 : moebiusLightconeLift y 2 = y 1 := rfl
  have hy3 : moebiusLightconeLift y 3 = y 2 := rfl
  have hy4 : moebiusLightconeLift y 4 = (1 + y ⬝ᵥ y) / 2 := rfl
  rw [moebiusBilin5, hx0, hx1, hx2, hx3, hx4, hy0, hy1, hy2, hy3, hy4]
  simp [dotProduct, Fin.sum_univ_three]
  ring

/-- Unit-sphere inversion lifts linearly to the coordinate reflection `u₀ ↦ -u₀` in `ℝ⁵` (`§6`). -/
theorem moebius_inversion_as_reflection (x : Fin 3 → ℝ) (hx : x ⬝ᵥ x ≠ 0) :
    let u := moebiusLightconeLift x
    moebiusLightconeLift (euclidInvert x) =
      (x ⬝ᵥ x)⁻¹ • ![-u 0, u 1, u 2, u 3, u 4] := by
  have hinv_dot : euclidInvert x ⬝ᵥ euclidInvert x = (x ⬝ᵥ x)⁻¹ := by
    dsimp [euclidInvert]
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp [hx]
  ext i
  fin_cases i
  · change (1 - euclidInvert x ⬝ᵥ euclidInvert x) / 2 =
        (x ⬝ᵥ x)⁻¹ * -((1 - x ⬝ᵥ x) / 2)
    rw [hinv_dot]
    field_simp [hx]
    ring
  · dsimp [moebiusLightconeLift, euclidInvert]
  · dsimp [moebiusLightconeLift, euclidInvert]
  · dsimp [moebiusLightconeLift, euclidInvert]
  · change (1 + euclidInvert x ⬝ᵥ euclidInvert x) / 2 =
        (x ⬝ᵥ x)⁻¹ * ((1 + x ⬝ᵥ x) / 2)
    rw [hinv_dot]
    field_simp [hx]
    ring

/-- **`[countermodel_found]` Klein's Footnote 26 (`§6`, p. 10)**:
Complex reciprocal-radius inversion `z ↦ (star z)⁻¹` is NOT representable by any holomorphic
Möbius map `(a z + b) / (c z + d)`. -/
theorem klein_footnote26_inversion_not_holomorphic_mobius :
    ¬ ∃ a b c d : ℂ, ∀ z : ℂ, z ≠ 0 → (starRingEnd ℂ z)⁻¹ = (a * z + b) / (c * z + d) := by
  rintro ⟨a, b, c, d, h⟩
  have h1 := h 1 one_ne_zero
  have hm1 := h (-1) (neg_ne_zero.mpr one_ne_zero)
  have hI := h Complex.I Complex.I_ne_zero
  simp only [map_one, inv_one, mul_one] at h1
  simp only [map_neg, map_one, inv_neg, inv_one, mul_neg, mul_one] at hm1
  have hI_lhs : (starRingEnd ℂ Complex.I)⁻¹ = Complex.I := by
    simp [Complex.conj_I]
  rw [hI_lhs] at hI
  have hcd_pos : c + d ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h1
    exact one_ne_zero h1
  have hcd_neg : -c + d ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hm1
    norm_num at hm1
  have hci_pos : c * Complex.I + d ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hI
    exact Complex.I_ne_zero hI
  have e1 : c + d = a + b := by
    have hmul := congrArg (· * (c + d)) h1
    rwa [one_mul, div_mul_cancel₀ _ hcd_pos] at hmul
  have em1 : -(-c + d) = -a + b := by
    have hmul := congrArg (· * (-c + d)) hm1
    rwa [neg_one_mul, div_mul_cancel₀ _ hcd_neg] at hmul
  have hb : b = c := by linear_combination -(e1 + em1) / 2
  have ha : a = d := by linear_combination -(e1 - em1) / 2
  have eI : Complex.I * (c * Complex.I + d) = a * Complex.I + b := by
    have hmul := congrArg (· * (c * Complex.I + d)) hI
    rwa [div_mul_cancel₀ _ hci_pos] at hmul
  have hc0 : c = 0 := by
    rw [ha, hb] at eI
    have hI2 : Complex.I * (c * Complex.I + d) = -c + d * Complex.I := by
      calc
        Complex.I * (c * Complex.I + d) = c * (Complex.I * Complex.I) + d * Complex.I := by ring
        _ = c * (-1) + d * Complex.I := by rw [Complex.I_mul_I]
        _ = -c + d * Complex.I := by ring
    rw [hI2] at eI
    have h2c : (2 : ℂ) * c = 0 := by linear_combination -eI
    exact (mul_eq_zero.mp h2c).resolve_left (by norm_num)
  have h2 := h 2 (by norm_num)
  have h2_lhs : (starRingEnd ℂ (2 : ℂ))⁻¹ = (2 : ℂ)⁻¹ := by simp only [map_ofNat]
  rw [h2_lhs, hb, hc0, ha] at h2
  rw [hc0, zero_add] at hcd_pos
  have h2_rhs : (d * 2 + 0) / (0 * 2 + d) = (2 : ℂ) := by
    field_simp [hcd_pos]
    ring
  rw [h2_rhs] at h2
  norm_num at h2

/-- Pure scalar cross-ratio covariance identity for antiholomorphic fractional-linear maps. -/
private theorem antiMobius_conj_crossRatio_scalar (m00 m01 m10 m11 u₁ u₂ u₃ u₄ : ℂ)
    (hdet : m00 * m11 - m01 * m10 ≠ 0)
    (d₁ : m10 * u₁ + m11 ≠ 0) (d₂ : m10 * u₂ + m11 ≠ 0)
    (d₃ : m10 * u₃ + m11 ≠ 0) (d₄ : m10 * u₄ + m11 ≠ 0)
    (hs13 : u₁ - u₃ ≠ 0) (hs24 : u₂ - u₄ ≠ 0) :
    (((m00 * u₁ + m01) / (m10 * u₁ + m11) - (m00 * u₂ + m01) / (m10 * u₂ + m11)) *
        ((m00 * u₃ + m01) / (m10 * u₃ + m11) - (m00 * u₄ + m01) / (m10 * u₄ + m11))) /
      (((m00 * u₁ + m01) / (m10 * u₁ + m11) - (m00 * u₃ + m01) / (m10 * u₃ + m11)) *
        ((m00 * u₂ + m01) / (m10 * u₂ + m11) - (m00 * u₄ + m01) / (m10 * u₄ + m11))) =
      ((u₁ - u₂) * (u₃ - u₄)) / ((u₁ - u₃) * (u₂ - u₄)) := by
  have h12 : (m00 * u₁ + m01) / (m10 * u₁ + m11) - (m00 * u₂ + m01) / (m10 * u₂ + m11) =
      ((m00 * m11 - m01 * m10) * (u₁ - u₂)) / ((m10 * u₁ + m11) * (m10 * u₂ + m11)) := by
    rw [div_sub_div _ _ d₁ d₂]; congr 1; ring
  have h34 : (m00 * u₃ + m01) / (m10 * u₃ + m11) - (m00 * u₄ + m01) / (m10 * u₄ + m11) =
      ((m00 * m11 - m01 * m10) * (u₃ - u₄)) / ((m10 * u₃ + m11) * (m10 * u₄ + m11)) := by
    rw [div_sub_div _ _ d₃ d₄]; congr 1; ring
  have h13 : (m00 * u₁ + m01) / (m10 * u₁ + m11) - (m00 * u₃ + m01) / (m10 * u₃ + m11) =
      ((m00 * m11 - m01 * m10) * (u₁ - u₃)) / ((m10 * u₁ + m11) * (m10 * u₃ + m11)) := by
    rw [div_sub_div _ _ d₁ d₃]; congr 1; ring
  have h24 : (m00 * u₂ + m01) / (m10 * u₂ + m11) - (m00 * u₄ + m01) / (m10 * u₄ + m11) =
      ((m00 * m11 - m01 * m10) * (u₂ - u₄)) / ((m10 * u₂ + m11) * (m10 * u₄ + m11)) := by
    rw [div_sub_div _ _ d₂ d₄]; congr 1; ring
  rw [h12, h34, h13, h24, div_mul_div_comm, div_mul_div_comm]
  have hden12 : (m10 * u₁ + m11) * (m10 * u₂ + m11) ≠ 0 := mul_ne_zero d₁ d₂
  have hden34 : (m10 * u₃ + m11) * (m10 * u₄ + m11) ≠ 0 := mul_ne_zero d₃ d₄
  have hden13 : (m10 * u₁ + m11) * (m10 * u₃ + m11) ≠ 0 := mul_ne_zero d₁ d₃
  have hden24 : (m10 * u₂ + m11) * (m10 * u₄ + m11) ≠ 0 := mul_ne_zero d₂ d₄
  have hbot : (((m00 * m11 - m01 * m10) * (u₁ - u₃)) * ((m00 * m11 - m01 * m10) * (u₂ - u₄))) /
      (((m10 * u₁ + m11) * (m10 * u₃ + m11)) * ((m10 * u₂ + m11) * (m10 * u₄ + m11))) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero hdet hs13) (mul_ne_zero hdet hs24))
      (mul_ne_zero hden13 hden24)
  rw [div_eq_div_iff hbot (mul_ne_zero hs13 hs24)]
  field_simp [mul_ne_zero hden12 hden34, mul_ne_zero hden13 hden24]

/-- Pure scalar composition identity for two antiholomorphic fractional-linear maps. -/
private theorem antiMobius_comp_scalar (m00 m01 m10 m11 n00s n01s n10s n11s z : ℂ)
    (hden' : n10s * z + n11s ≠ 0) :
    (m00 * ((n00s * z + n01s) / (n10s * z + n11s)) + m01) /
        (m10 * ((n00s * z + n01s) / (n10s * z + n11s)) + m11) =
      ((m00 * n00s + m01 * n10s) * z + (m00 * n01s + m01 * n11s)) /
        ((m10 * n00s + m11 * n10s) * z + (m10 * n01s + m11 * n11s)) := by
  have htop : m00 * ((n00s * z + n01s) / (n10s * z + n11s)) + m01 =
      ((m00 * n00s + m01 * n10s) * z + (m00 * n01s + m01 * n11s)) / (n10s * z + n11s) := by
    rw [mul_div_assoc', div_add' _ _ _ hden']; congr 1; ring
  have hbot : m10 * ((n00s * z + n01s) / (n10s * z + n11s)) + m11 =
      ((m10 * n00s + m11 * n10s) * z + (m10 * n01s + m11 * n11s)) / (n10s * z + n11s) := by
    rw [mul_div_assoc', div_add' _ _ _ hden']; congr 1; ring
  rw [htop, hbot]
  exact div_div_div_cancel_right₀ hden' _ _

/-- Antiholomorphic Möbius transformation `(M₀₀ z̄ + M₀₁) / (M₁₀ z̄ + M₁₁)` (`Footnote 26`, p. 10). -/
noncomputable def antiMobius (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) : ℂ :=
  (M 0 0 * star z + M 0 1) / (M 1 0 * star z + M 1 1)

/-- Antiholomorphic Möbius maps send the complex cross-ratio to its complex conjugate (`Footnote 26`). -/
theorem antiMobius_conj_crossRatio (M : Matrix (Fin 2) (Fin 2) ℂ) (z₁ z₂ z₃ z₄ : ℂ)
    (hd : M.det ≠ 0)
    (d₁ : M 1 0 * star z₁ + M 1 1 ≠ 0) (d₂ : M 1 0 * star z₂ + M 1 1 ≠ 0)
    (d₃ : M 1 0 * star z₃ + M 1 1 ≠ 0) (d₄ : M 1 0 * star z₄ + M 1 1 ≠ 0)
    (h13 : z₁ - z₃ ≠ 0) (h24 : z₂ - z₄ ≠ 0) :
    ((antiMobius M z₁ - antiMobius M z₂) * (antiMobius M z₃ - antiMobius M z₄)) /
      ((antiMobius M z₁ - antiMobius M z₃) * (antiMobius M z₂ - antiMobius M z₄)) =
      star (((z₁ - z₂) * (z₃ - z₄)) / ((z₁ - z₃) * (z₂ - z₄))) := by
  dsimp [antiMobius]
  have hs13 : star z₁ - star z₃ ≠ 0 := by
    intro h0
    apply h13
    have := congrArg star h0
    simpa [star_sub, star_star] using this
  have hs24 : star z₂ - star z₄ ≠ 0 := by
    intro h0
    apply h24
    have := congrArg star h0
    simpa [star_sub, star_star] using this
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
    rwa [Matrix.det_fin_two] at hd
  rw [map_div₀, map_mul, map_mul, map_sub, map_sub, map_sub, map_sub]
  exact antiMobius_conj_crossRatio_scalar (M 0 0) (M 0 1) (M 1 0) (M 1 1)
    (star z₁) (star z₂) (star z₃) (star z₄) hdet d₁ d₂ d₃ d₄ hs13 hs24

/-- Composing two antiholomorphic Möbius maps recovers a holomorphic Möbius map (`§1` & `Footnote 26`). -/
theorem antiMobius_comp_eq_holomorphic (M N : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ)
    (hden : N 1 0 * star z + N 1 1 ≠ 0) :
    let P := M * N.map star
    antiMobius M (antiMobius N z) = (P 0 0 * z + P 0 1) / (P 1 0 * z + P 1 1) := by
  dsimp only [antiMobius]
  have hsc : star (N 1 0 * star z + N 1 1) = star (N 1 0) * z + star (N 1 1) := by
    simp [star_add, star_mul, mul_comm]
  have hnum : star (N 0 0 * star z + N 0 1) = star (N 0 0) * z + star (N 0 1) := by
    simp [star_add, star_mul, mul_comm]
  have hden' : star (N 1 0) * z + star (N 1 1) ≠ 0 := by
    have hsnz := star_ne_zero.mpr hden
    rwa [hsc] at hsnz
  simp only [star_div₀, hnum, hsc, Matrix.mul_apply, Matrix.map_apply, Fin.sum_univ_two]
  exact antiMobius_comp_scalar (M 0 0) (M 0 1) (M 1 0) (M 1 1)
    (star (N 0 0)) (star (N 0 1)) (star (N 1 0)) (star (N 1 1)) z hden'

end ReciprocalRadiiAndMobius

/-! ## 2. Lie's Sphere Geometry & Grassmann–Plücker–Klein Bridge III (§7, Footnote 31) -/

section LieSphereAndGrassmannBridge

/-- Signature `(3, 2)` Lie sphere/circle bilinear form (`§7`, `Footnote 31`, p. 14). -/
def lieBilin (u v : Fin 5 → ℝ) : ℝ :=
  -u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 - u 4 * v 4

/-- Oriented circle `(a, b; signed radius r)` embedded as a null vector in `ℝ⁵` (`§7`, p. 14). -/
def lieCircleVec (a b r : ℝ) : Fin 5 → ℝ :=
  ![(1 + a ^ 2 + b ^ 2 - r ^ 2) / 2, (1 - (a ^ 2 + b ^ 2 - r ^ 2)) / 2, a, b, r]

theorem lieCircleVec_isNull (a b r : ℝ) :
    lieBilin (lieCircleVec a b r) (lieCircleVec a b r) = 0 := by
  have h0 : lieCircleVec a b r 0 = (1 + a ^ 2 + b ^ 2 - r ^ 2) / 2 := rfl
  have h1 : lieCircleVec a b r 1 = (1 - (a ^ 2 + b ^ 2 - r ^ 2)) / 2 := rfl
  have h2 : lieCircleVec a b r 2 = a := rfl
  have h3 : lieCircleVec a b r 3 = b := rfl
  have h4 : lieCircleVec a b r 4 = r := rfl
  rw [lieBilin, h0, h1, h2, h3, h4]
  ring

theorem lieBilin_oriented_distance (a₁ b₁ r₁ a₂ b₂ r₂ : ℝ) :
    -2 * lieBilin (lieCircleVec a₁ b₁ r₁) (lieCircleVec a₂ b₂ r₂) =
      (a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - (r₁ - r₂) ^ 2 := by
  have h10 : lieCircleVec a₁ b₁ r₁ 0 = (1 + a₁ ^ 2 + b₁ ^ 2 - r₁ ^ 2) / 2 := rfl
  have h11 : lieCircleVec a₁ b₁ r₁ 1 = (1 - (a₁ ^ 2 + b₁ ^ 2 - r₁ ^ 2)) / 2 := rfl
  have h12 : lieCircleVec a₁ b₁ r₁ 2 = a₁ := rfl
  have h13 : lieCircleVec a₁ b₁ r₁ 3 = b₁ := rfl
  have h14 : lieCircleVec a₁ b₁ r₁ 4 = r₁ := rfl
  have h20 : lieCircleVec a₂ b₂ r₂ 0 = (1 + a₂ ^ 2 + b₂ ^ 2 - r₂ ^ 2) / 2 := rfl
  have h21 : lieCircleVec a₂ b₂ r₂ 1 = (1 - (a₂ ^ 2 + b₂ ^ 2 - r₂ ^ 2)) / 2 := rfl
  have h22 : lieCircleVec a₂ b₂ r₂ 2 = a₂ := rfl
  have h23 : lieCircleVec a₂ b₂ r₂ 3 = b₂ := rfl
  have h24 : lieCircleVec a₂ b₂ r₂ 4 = r₂ := rfl
  rw [lieBilin, h10, h11, h12, h13, h14, h20, h21, h22, h23, h24]
  ring

theorem lieBilin_eq_zero_iff_oriented_tangent (a₁ b₁ r₁ a₂ b₂ r₂ : ℝ) :
    lieBilin (lieCircleVec a₁ b₁ r₁) (lieCircleVec a₂ b₂ r₂) = 0 ↔
      (a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 = (r₁ - r₂) ^ 2 := by
  constructor
  · intro h
    have h2 : (a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - (r₁ - r₂) ^ 2 = 0 := by
      rw [← lieBilin_oriented_distance, h, mul_zero]
    linarith
  · intro h
    have h2 : -2 * lieBilin (lieCircleVec a₁ b₁ r₁) (lieCircleVec a₂ b₂ r₂) = 0 := by
      rw [lieBilin_oriented_distance, h, sub_self]
    linarith

/-- SymPy-certified `5 × 5` Lie radius-dilation matrix `L(t) ∈ SO(3,2)` sending `(a, b, r)`
to `(a, b, r + t)`, transforming zero-radius points to genuine circles (`§7`, pp. 13–14). -/
def lieRadiusDilMatrix (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  ![ ![1 - t ^ 2 / 2, -(t ^ 2 / 2), 0, 0, -t],
     ![t ^ 2 / 2,     1 + t ^ 2 / 2, 0, 0, t],
     ![0, 0, 1, 0, 0],
     ![0, 0, 0, 1, 0],
     ![t, t, 0, 0, 1] ]

theorem lieRadiusDilMatrix_preserves_lieBilin (t : ℝ) (u v : Fin 5 → ℝ) :
    lieBilin (lieRadiusDilMatrix t *ᵥ u) (lieRadiusDilMatrix t *ᵥ v) = lieBilin u v := by
  have hmul : ∀ w : Fin 5 → ℝ,
      ((lieRadiusDilMatrix t *ᵥ w) 0 = (1 - t ^ 2 / 2) * w 0 - (t ^ 2 / 2) * w 1 - t * w 4) ∧
      ((lieRadiusDilMatrix t *ᵥ w) 1 = (t ^ 2 / 2) * w 0 + (1 + t ^ 2 / 2) * w 1 + t * w 4) ∧
      ((lieRadiusDilMatrix t *ᵥ w) 2 = w 2) ∧
      ((lieRadiusDilMatrix t *ᵥ w) 3 = w 3) ∧
      ((lieRadiusDilMatrix t *ᵥ w) 4 = t * w 0 + t * w 1 + w 4) := by
    intro w
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp [lieRadiusDilMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_five]; try ring)
  rcases hmul u with ⟨hu0, hu1, hu2, hu3, hu4⟩
  rcases hmul v with ⟨hv0, hv1, hv2, hv3, hv4⟩
  rw [lieBilin, lieBilin, hu0, hu1, hu2, hu3, hu4, hv0, hv1, hv2, hv3, hv4]
  ring

theorem lieRadiusDilMatrix_add (s t : ℝ) :
    lieRadiusDilMatrix (s + t) = lieRadiusDilMatrix s * lieRadiusDilMatrix t := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_five]
  fin_cases i <;> fin_cases j <;>
    (simp [lieRadiusDilMatrix]; try ring)

theorem lieRadiusDilMatrix_mulVec_circleVec (t a b r : ℝ) :
    lieRadiusDilMatrix t *ᵥ lieCircleVec a b r = lieCircleVec a b (r + t) := by
  ext i
  fin_cases i <;>
    (simp [lieRadiusDilMatrix, lieCircleVec, Matrix.mulVec, dotProduct, Fin.sum_univ_five]; try ring)

/-- Points (`r = 0`) do NOT form a body for Lie's sphere group (`§7`, p. 13): `lieRadiusDilMatrix t`
converts every point `lieCircleVec a b 0` into a circle of radius `t`. -/
theorem lieRadiusDilMatrix_maps_point_to_circle (a b t : ℝ) (ht : t ≠ 0) :
    lieRadiusDilMatrix t *ᵥ lieCircleVec a b 0 = lieCircleVec a b t ∧
      (lieRadiusDilMatrix t *ᵥ lieCircleVec a b 0) 4 ≠ (lieCircleVec a b 0) 4 := by
  refine ⟨by simpa using lieRadiusDilMatrix_mulVec_circleVec t a b 0, ?_⟩
  rw [lieRadiusDilMatrix_mulVec_circleVec]
  change 0 + t ≠ 0
  simpa using ht

/-- **Grassmann–Plücker–Klein Bridge III (`§7`, Footnotes 29 & 31)**:
Canonical linear projection `π : ℝ⁵ →ₗ[ℝ] ℝ⁴` from Lie's `5D` oriented sphere space to
Grassmann's 1862 Lorentzian `4D` circle space (`GrassmannPluckerMeetAndCircleSpace.circleVec`). -/
def lieToGrassmannCircleProj : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun u := ![u 0 + u 1, u 2, u 3, u 0 - u 1]
  map_add' u v := by ext i; fin_cases i <;> (simp; try ring)
  map_smul' c u := by ext i; fin_cases i <;> (simp; try ring)

theorem lieToGrassmannCircleProj_circleVec (a b r : ℝ) :
    lieToGrassmannCircleProj (lieCircleVec a b r) = circleVec a b r := by
  ext i
  fin_cases i <;>
    (simp [lieToGrassmannCircleProj, lieCircleVec, circleVec]; try ring)

theorem circleBilin_lieToGrassmannProj (u v : Fin 5 → ℝ) :
    circleBilin (lieToGrassmannCircleProj u) (lieToGrassmannCircleProj v) =
      -2 * (lieBilin u v + u 4 * v 4) := by
  have hp : ∀ w : Fin 5 → ℝ,
      (lieToGrassmannCircleProj w 0 = w 0 + w 1) ∧
      (lieToGrassmannCircleProj w 1 = w 2) ∧
      (lieToGrassmannCircleProj w 2 = w 3) ∧
      (lieToGrassmannCircleProj w 3 = w 0 - w 1) := by
    intro w
    refine ⟨rfl, rfl, rfl, rfl⟩
  rcases hp u with ⟨hu0, hu1, hu2, hu3⟩
  rcases hp v with ⟨hv0, hv1, hv2, hv3⟩
  rw [circleBilin_apply, hu0, hu1, hu2, hu3, hv0, hv1, hv2, hv3, lieBilin]
  ring

/-- Grassmann's unoriented tangency predicate (`IsCircleTangent`) holds iff one of the two signed-
radius Lie orthogonality branches vanishes, unifying Grassmann `Note 97` (`GL(4,ℝ)`) with Lie's `O(3,2)` (`§7`). -/
theorem grassmann_tangency_iff_signed_lie_orthogonality (a₁ b₁ r₁ a₂ b₂ r₂ : ℝ) :
    IsCircleTangent (circleVec a₁ b₁ r₁) (circleVec a₂ b₂ r₂) ↔
      lieBilin (lieCircleVec a₁ b₁ r₁) (lieCircleVec a₂ b₂ r₂) = 0 ∨
        lieBilin (lieCircleVec a₁ b₁ r₁) (lieCircleVec a₂ b₂ (-r₂)) = 0 := by
  dsimp [IsCircleTangent]
  rw [(grassmann_no396_double_distance 0 0 a₁ b₁ r₁ a₁ b₁ r₁ a₂ b₂ r₂).2.1,
      (grassmann_no396_double_distance 0 0 a₂ b₂ r₂ a₁ b₁ r₁ a₂ b₂ r₂).2.1,
      (grassmann_no396_double_distance 0 0 a₁ b₁ r₁ a₁ b₁ r₁ a₂ b₂ r₂).2.2,
      lieBilin_eq_zero_iff_oriented_tangent, lieBilin_eq_zero_iff_oriented_tangent]
  have hdiff : ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - r₁ ^ 2 - r₂ ^ 2) ^ 2 -
      (-2 * r₁ ^ 2) * (-2 * r₂ ^ 2) =
      ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - (r₁ - r₂) ^ 2) *
        ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - (r₁ - (-r₂)) ^ 2) := by ring
  constructor
  · intro h
    have hprod : ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - (r₁ - r₂) ^ 2) *
        ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - (r₁ - (-r₂)) ^ 2) = 0 := by
      rw [← hdiff, h, sub_self]
    rcases mul_eq_zero.mp hprod with hl | hr
    · left; exact sub_eq_zero.mp hl
    · right; exact sub_eq_zero.mp hr
  · rintro (hl | hr)
    · have hp : ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - (r₁ - r₂) ^ 2) *
          ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - (r₁ - (-r₂)) ^ 2) = 0 := by
        rw [hl, sub_self, zero_mul]
      rw [← hdiff] at hp
      exact sub_eq_zero.mp hp
    · have hp : ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - (r₁ - r₂) ^ 2) *
          ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - (r₁ - (-r₂)) ^ 2) = 0 := by
        rw [hr, sub_self, mul_zero]
      rw [← hdiff] at hp
      exact sub_eq_zero.mp hp

end LieSphereAndGrassmannBridge

/-! ## 3. Cremona Involution, Contact 5-Space, Legendre Transform & Bridge IV (§§8–9) -/

section CremonaContactAndPfaffBridge

/-- Classical quadratic Cremona involution `(x₀, x₁, x₂) ↦ (x₁ x₂, x₀ x₂, x₀ x₁)` (`§8.1`, p. 15). -/
def cremona2 {R : Type*} [CommRing R] (x : Fin 3 → R) : Fin 3 → R :=
  ![x 1 * x 2, x 0 * x 2, x 0 * x 1]

theorem cremona2_involutive {R : Type*} [CommRing R] (x : Fin 3 → R) :
    cremona2 (cremona2 x) = (x 0 * x 1 * x 2) • x := by
  ext i
  fin_cases i <;> (simp [cremona2]; ring)

theorem cremona2_basePoints {R : Type*} [CommRing R] :
    cremona2 (![1, 0, 0] : Fin 3 → R) = 0 ∧
      cremona2 (![0, 1, 0] : Fin 3 → R) = 0 ∧
      cremona2 (![0, 0, 1] : Fin 3 → R) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [cremona2]

/-- Klein–Lie's fundamental united-position contact `1`-form `dz - p dx - q dy` on a `5D`
surface-element `(x, y, z, p, q)` (`§9`, p. 17). -/
def contactOneForm {R : Type*} [Ring R] (e δ : Fin 5 → R) : R :=
  δ 2 - e 3 * δ 0 - e 4 * δ 1

/-- Every surface, point pencil, and space-curve strip satisfies Klein's unified Legendrian relation
`dz - p dx - q dy = 0` (`§9`, p. 17). -/
theorem contactOneForm_three_classes {R : Type*} [CommRing R] (p q δx δy δp δq : R) :
    contactOneForm ![0, 0, 0, p, q] ![δx, δy, p * δx + q * δy, δp, δq] = 0 ∧
      contactOneForm ![0, 0, 0, p, q] ![0, 0, 0, δp, δq] = 0 ∧
      (∀ γx γy γp γq : R,
        contactOneForm ![0, 0, 0, γp, γq] ![γx, γy, γp * γx + γq * γy, δp, δq] = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [contactOneForm]; ring
  · dsimp [contactOneForm]; ring
  · intro γx γy γp γq
    dsimp [contactOneForm]; ring

/-- Legendre contact transformation `(x, y, z, p, q) ↦ (p, q, p x + q y - z, x, y)` (`§9`, p. 16). -/
def legendreContact {R : Type*} [Ring R] (e : Fin 5 → R) : Fin 5 → R :=
  ![e 3, e 4, e 3 * e 0 + e 4 * e 1 - e 2, e 0, e 1]

/-- Infinitesimal differential pushforward `(δx, δy, δz, δp, δq)` under `legendreContact`. -/
def legendreContactDiff {R : Type*} [Ring R] (e δ : Fin 5 → R) : Fin 5 → R :=
  ![δ 3, δ 4, δ 3 * e 0 + e 3 * δ 0 + δ 4 * e 1 + e 4 * δ 1 - δ 2, δ 0, δ 1]

theorem legendreContact_involutive {R : Type*} [CommRing R] (e : Fin 5 → R) :
    legendreContact (legendreContact e) = e := by
  ext i
  fin_cases i <;> (simp [legendreContact]; try ring)

/-- Exact invariance of the contact distribution: `L^*(dz - p dx - q dy) = -(dz - p dx - q dy)` (`§9`). -/
theorem contactOneForm_legendre_pullback {R : Type*} [CommRing R] (e δ : Fin 5 → R) :
    contactOneForm (legendreContact e) (legendreContactDiff e δ) = -contactOneForm e δ := by
  have hl0 : legendreContact e 3 = e 0 := rfl
  have hl1 : legendreContact e 4 = e 1 := rfl
  have hd0 : legendreContactDiff e δ 0 = δ 3 := rfl
  have hd1 : legendreContactDiff e δ 1 = δ 4 := rfl
  have hd2 : legendreContactDiff e δ 2 =
      δ 3 * e 0 + e 3 * δ 0 + δ 4 * e 1 + e 4 * δ 1 - δ 2 := rfl
  rw [contactOneForm, contactOneForm, hl0, hl1, hd0, hd1, hd2]
  ring

/-- Concrete point-to-plane interchange (`§9`): Legendre maps the `∞²` point pencil at `(0, 0, z₀)`
into the `∞²` elements of the plane `x' = 0` (`p' = 0, q' = 0` with tangent plane `z' = u x' + v y' - z₀`). -/
theorem legendreContact_point_to_plane {R : Type*} [CommRing R] (z₀ u v : R) :
    legendreContact ![0, 0, z₀, u, v] = ![u, v, -z₀, 0, 0] := by
  ext i
  fin_cases i <;> simp [legendreContact]

/-- Clebsch's connex point–plane incidence `u ⬝ᵥ x = 0` is invariant under `(A *ᵥ x, u ᵥ* B)`
when `B * A = 1` (`§9`, p. 18). -/
theorem clebsch_connex_incidence_invariant {R : Type*} [CommRing R]
    (A B : Matrix (Fin 4) (Fin 4) R) (hBA : B * A = 1) (u x : Fin 4 → R) :
    (u ᵥ* B) ⬝ᵥ (A *ᵥ x) = u ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hBA, Matrix.vecMul_one]

/-- **Grassmann–Plücker–Klein Bridge IV (Grassmann Pfaffian `No. 511` ↔ Klein `5D` Contact Form, `§9`)**:
Embed Klein's `5D` contact `1`-form `ω = dz - p dx - q dy` and symplectic `2`-form
`Ω = dp ∧ dx + dq ∧ dy` natively in `ExteriorAlgebra ℝ (Fin 5 → ℝ)`:
1. `ω ∧ Ω² ≠ 0` (explicitly `volCoord b (ω * Ω²) = -2 ≠ 0`), proving strict `5D`
   contact nondegeneracy across arbitrary `(p, q)`.
2. For `2`-parameter Pfaffian jets `pfaffJetOneForm u α` and `pfaffJetTwoForm β α` (`n = 2`),
   Grassmann `No. 511` forces `ω_jet * Ω_jet ^ 2 = 0` in `4D`, separating Darboux `4D` jets
   from `5D` nondegenerate contact forms! -/
theorem grassmann_pfaff_contact5 (p q : ℝ) :
    let b := Pi.basisFun ℝ (Fin 5)
    let ι := ExteriorAlgebra.ι ℝ
    let ω := ι (b 2) - p • ι (b 0) - q • ι (b 1)
    let Ω := ι (b 3) * ι (b 0) + ι (b 4) * ι (b 1)
    (volCoord b (ω * Ω ^ 2) = -2 ∧ ω * Ω ^ 2 ≠ 0) ∧
      (∀ (M : Type) [AddCommGroup M] [Module ℝ M] (u : Fin 2 → ℝ) (α β : Fin 2 → M),
        pfaffJetOneForm u α * pfaffJetTwoForm β α ^ 2 = 0) := by
  intro b ι ω Ω
  have he : ExteriorAlgebra.ι ℝ (b 0) * ExteriorAlgebra.ι ℝ (b 0) = 0 :=
    ExteriorAlgebra.ι_sq_zero _
  have he1 : ExteriorAlgebra.ι ℝ (b 1) * ExteriorAlgebra.ι ℝ (b 1) = 0 :=
    ExteriorAlgebra.ι_sq_zero _
  have he3 : ExteriorAlgebra.ι ℝ (b 3) * ExteriorAlgebra.ι ℝ (b 3) = 0 :=
    ExteriorAlgebra.ι_sq_zero _
  have he4 : ExteriorAlgebra.ι ℝ (b 4) * ExteriorAlgebra.ι ℝ (b 4) = 0 :=
    ExteriorAlgebra.ι_sq_zero _
  have h30_mem : (ι (b 3) * ι (b 0) : ExteriorAlgebra ℝ (Fin 5 → ℝ)) ∈ ⋀[ℝ]^2 (Fin 5 → ℝ) := by
    rw [ExteriorAlgebra.exteriorPower, pow_two]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self (ExteriorAlgebra.ι ℝ) (b 3))
      (LinearMap.mem_range_self (ExteriorAlgebra.ι ℝ) (b 0))
  have hcomm : (ι (b 3) * ι (b 0)) * (ι (b 4) * ι (b 1)) =
      (ι (b 4) * ι (b 1)) * (ι (b 3) * ι (b 0)) :=
    exteriorPower_two_mul_comm h30_mem _
  have hΩ2 : Ω ^ 2 = (2 : ℝ) • ((ι (b 3) * ι (b 0)) * (ι (b 4) * ι (b 1))) := by
    dsimp [Ω]
    rw [pow_two, add_mul, mul_add, mul_add]
    have ht1 : (ι (b 3) * ι (b 0)) * (ι (b 3) * ι (b 0)) = 0 := by
      have h03 := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℝ) (b 0) (b 3))
      calc
        (ι (b 3) * ι (b 0)) * (ι (b 3) * ι (b 0))
            = ι (b 3) * (ι (b 0) * ι (b 3)) * ι (b 0) := by simp only [mul_assoc]
        _ = ι (b 3) * (-(ι (b 3) * ι (b 0))) * ι (b 0) := by rw [h03]
        _ = -((ι (b 3) * ι (b 3)) * (ι (b 0) * ι (b 0))) := by
          simp only [mul_neg, neg_mul, mul_assoc]
        _ = 0 := by rw [he3, zero_mul, neg_zero]
    have ht2 : (ι (b 4) * ι (b 1)) * (ι (b 4) * ι (b 1)) = 0 := by
      have h14 := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℝ) (b 1) (b 4))
      calc
        (ι (b 4) * ι (b 1)) * (ι (b 4) * ι (b 1))
            = ι (b 4) * (ι (b 1) * ι (b 4)) * ι (b 1) := by simp only [mul_assoc]
        _ = ι (b 4) * (-(ι (b 4) * ι (b 1))) * ι (b 1) := by rw [h14]
        _ = -((ι (b 4) * ι (b 4)) * (ι (b 1) * ι (b 1))) := by
          simp only [mul_neg, neg_mul, mul_assoc]
        _ = 0 := by rw [he4, zero_mul, neg_zero]
    rw [ht1, ht2, zero_add, add_zero, ← hcomm, two_smul]
  have hp0 : ι (b 0) * ((ι (b 3) * ι (b 0)) * (ι (b 4) * ι (b 1))) = 0 := by
    have h03 := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℝ) (b 0) (b 3))
    calc
      ι (b 0) * ((ι (b 3) * ι (b 0)) * (ι (b 4) * ι (b 1)))
          = ((ι (b 0) * ι (b 3)) * ι (b 0)) * (ι (b 4) * ι (b 1)) := by simp only [mul_assoc]
      _ = ((-(ι (b 3) * ι (b 0))) * ι (b 0)) * (ι (b 4) * ι (b 1)) := by rw [h03]
      _ = -(ι (b 3) * (ι (b 0) * ι (b 0))) * (ι (b 4) * ι (b 1)) := by
        simp only [neg_mul, mul_assoc]
      _ = 0 := by rw [he, mul_zero, neg_zero, zero_mul]
  have hp1 : ι (b 1) * ((ι (b 3) * ι (b 0)) * (ι (b 4) * ι (b 1))) = 0 := by
    have h14 := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℝ) (b 1) (b 4))
    calc
      ι (b 1) * ((ι (b 3) * ι (b 0)) * (ι (b 4) * ι (b 1)))
          = ι (b 1) * ((ι (b 4) * ι (b 1)) * (ι (b 3) * ι (b 0))) := by rw [hcomm]
      _ = ((ι (b 1) * ι (b 4)) * ι (b 1)) * (ι (b 3) * ι (b 0)) := by simp only [mul_assoc]
      _ = ((-(ι (b 4) * ι (b 1))) * ι (b 1)) * (ι (b 3) * ι (b 0)) := by rw [h14]
      _ = -(ι (b 4) * (ι (b 1) * ι (b 1))) * (ι (b 3) * ι (b 0)) := by
        simp only [neg_mul, mul_assoc]
      _ = 0 := by rw [he1, mul_zero, neg_zero, zero_mul]
  have h30 : ι (b 3) * ι (b 0) = -(ι (b 0) * ι (b 3)) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (b 3) (b 0))
  have h20 : ι (b 2) * ι (b 0) = -(ι (b 0) * ι (b 2)) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (b 2) (b 0))
  have h41 : ι (b 4) * ι (b 1) = -(ι (b 1) * ι (b 4)) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (b 4) (b 1))
  have h31 : ι (b 3) * ι (b 1) = -(ι (b 1) * ι (b 3)) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (b 3) (b 1))
  have h21 : ι (b 2) * ι (b 1) = -(ι (b 1) * ι (b 2)) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (b 2) (b 1))
  have hvol5 : ι (b 0) * (ι (b 1) * (ι (b 2) * (ι (b 3) * ι (b 4)))) = volume b := by
    dsimp [volume, ι]
    have hcard5 : (Finset.univ : Finset (Fin 5)).card = 5 := Finset.card_fin 5
    rw [ExteriorAlgebra.basis_apply_ofCard b hcard5]
    let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hcard5)
    have h01 : (g 0).val < (g 1).val := g.strictMono (by decide : (0 : Fin 5) < 1)
    have h12 : (g 1).val < (g 2).val := g.strictMono (by decide : (1 : Fin 5) < 2)
    have h23 : (g 2).val < (g 3).val := g.strictMono (by decide : (2 : Fin 5) < 3)
    have h34 : (g 3).val < (g 4).val := g.strictMono (by decide : (3 : Fin 5) < 4)
    have h4lt : (g 4).val < 5 := (g 4).isLt
    have hg0 : g 0 = 0 := Fin.ext (by omega)
    have hg1 : g 1 = 1 := Fin.ext (by omega)
    have hg2 : g 2 = 2 := Fin.ext (by omega)
    have hg3 : g 3 = 3 := Fin.ext (by omega)
    have hg4 : g 4 = 4 := Fin.ext (by omega)
    change _ = ExteriorAlgebra.ιMulti ℝ 5 (fun r => b (g r))
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    simp [Matrix.vecTail, hg0, hg1, hg2, hg3, hg4]
  have h23041 : ι (b 2) * ((ι (b 3) * ι (b 0)) * (ι (b 4) * ι (b 1))) = -(volume b) := by
    calc
      ι (b 2) * ((ι (b 3) * ι (b 0)) * (ι (b 4) * ι (b 1)))
          = ι (b 2) * ((-(ι (b 0) * ι (b 3))) * (-(ι (b 1) * ι (b 4)))) := by
            rw [h30, h41]
      _ = (ι (b 2) * ι (b 0)) * ((ι (b 3) * ι (b 1)) * ι (b 4)) := by
            simp only [neg_mul_neg, mul_assoc]
      _ = (-(ι (b 0) * ι (b 2))) * ((-(ι (b 1) * ι (b 3))) * ι (b 4)) := by
            rw [h20, h31]
      _ = ι (b 0) * ((ι (b 2) * ι (b 1)) * (ι (b 3) * ι (b 4))) := by
            simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
      _ = ι (b 0) * ((-(ι (b 1) * ι (b 2))) * (ι (b 3) * ι (b 4))) := by
            rw [h21]
      _ = -(ι (b 0) * (ι (b 1) * (ι (b 2) * (ι (b 3) * ι (b 4))))) := by
            simp only [neg_mul, mul_neg, mul_assoc]
      _ = -(volume b) := by rw [hvol5]
  have hprod : ω * Ω ^ 2 = (-2 : ℝ) • volume b := by
    dsimp [ω]
    rw [hΩ2, sub_mul, sub_mul, smul_mul_assoc, smul_mul_assoc]
    simp only [mul_smul_comm, hp0, hp1, smul_zero, sub_zero]
    rw [h23041, smul_neg, ← neg_smul]
  have hvolCoord : volCoord b (ω * Ω ^ 2) = -2 := by
    rw [hprod, LinearMap.map_smul, volCoord_volume b, smul_eq_mul, mul_one]
  refine ⟨⟨hvolCoord, ?_⟩, fun M _ _ u α β => grassmann_no511_pfaff_exterior_vanishing u β α⟩
  intro hz
  have hc := congrArg (volCoord b) hz
  rw [hvolCoord, map_zero] at hc
  norm_num at hc

end CremonaContactAndPfaffBridge

end InfoGeometry.Erlangen.ErlangenProgramMobiusLieAndContact
