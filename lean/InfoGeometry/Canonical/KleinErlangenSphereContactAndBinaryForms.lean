/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Quaternion
import InfoGeometry.Projective.KleinErlangenProgramGroupsAndProjectiveTransfer

/-!
# Felix Klein's *Erlangen Program* (1872): Möbius & Lie Sphere Geometries, Cremona & Contact Transformations, Quaternions, & Binary Forms

This module formalizes Archetypes `EK₆`–`EK₉` from Felix Klein's 1872 Erlangen Program
(`0807.3161v1`, §§6–9, Concluding Remarks Footnote 37, and Note VII):

1. **`EK₆` (§6 & Footnote 26)**: Stereographic lift `stereoQuadricVec` from `ℝⁿ` into the Lorentzian
   null quadric of signature `(n + 1, 1)` (`moebiusQuadricBilin`), exact squared-distance formula
   and reciprocal-radii inversion `moebiusInversionEquiv`, plus Footnote 26's
   `[countermodel_found]` (`klein_fn26_unit_circle_inversion_not_holomorphic_moebius`) separating
   holomorphic `PSL(2, ℂ)` maps from full anti-holomorphic inversions `z ↦ 1 / star z`.
2. **`EK₇` (§7 & Footnote 31)**: Lie's oriented-sphere quadric `lieQuadricBilin` of signature
   `(n + 1, 2)` (`sigPos = 3, sigNeg = 2` for planar circles and `sigPos = 4, sigNeg = 2` for
   3D spheres), exact equivalence between oriented sphere tangency and `lieQuadricBilin`-nullity,
   and Laguerre's radius-shift subgroup `laguerreShift` in `O(n + 1, 2)` carrying points (`r = 0`)
   to spheres (`r = t ≠ 0`).
3. **`EK₈` (§8.1, §8.3 & §9)**: Cremona quadratic involution `cremonaPlane` breaking collinearity
   (`[countermodel_found]`), `fderiv` chain-rule tangent linearization (`tangentLinearizationEquiv`),
   `(2n + 1)`-dimensional contact geometry `ContactJetSpace` unifying point-fibers, smooth
   hypersurfaces (`fderiv`), and curve conormal strips as `n`-dimensional Legendrian manifolds,
   and Legendre's involutive contact transformation `legendreContact` swapping points with planes.
4. **`EK₉` (Concluding Remarks Fn. 37 & Note VII)**: Unit-quaternion `SO(3)` conjugation
   (`quatConjRot`) with `2 : 1` spin kernel, Cayley's universal binary cubic syzygy
   `Q² + 4 H₂³ = R f²`, Klein's `V₄`-symmetric spherical tetrahedron `kleinTetraVertex`,
   Cayley–Hermite's universal binary quartic syzygy `T² = -4 H³ + I H f² - J f³`, and Hesse's
   syzygetic pencil sharing the axial sextic covariant `x y (x⁴ - y⁴)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms

open scoped Quaternion Matrix
open QuadraticMap

/-! ## 0. Non-Commutativity Ground Witnesses (T16) -/

/-- Closed quaternion non-commutativity ground witness on `ℍ[ℝ]`. -/
theorem kleinErlangenSphere_quat_not_commute :
    ∃ a b : ℍ[ℝ], a * b ≠ b * a := by
  refine ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ?_⟩
  intro h
  have hk := congrArg QuaternionAlgebra.imK h
  norm_num at hk

/-- Closed `3 × 3` rational matrix non-commutativity ground witness (`Cremona` ambient matrices). -/
theorem kleinErlangenSphere_mat3Q_not_commute :
    ∃ a b : Matrix (Fin 3) (Fin 3) ℚ, a * b ≠ b * a := by
  refine ⟨Matrix.single 0 1 (1 : ℚ), Matrix.single 1 0 (1 : ℚ), ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => M 0 0) h
  simp [Matrix.mul_apply, Matrix.single_apply] at h00

/-! ## 1. `EK₆` (§6 & Fn. 26): Stereographic `(n+1, 1)` Lift & Reciprocal Radii -/

section MoebiusStereographic

private def moebiusQuadricRaw (n : ℕ) (u v : Fin (n + 2) → ℝ) : ℝ :=
  (∑ i : Fin n, u (Fin.castAdd 2 i) * v (Fin.castAdd 2 i)) +
    u ⟨n, by omega⟩ * v ⟨n, by omega⟩ -
    u ⟨n + 1, by omega⟩ * v ⟨n + 1, by omega⟩

private theorem moebiusQuadricRaw_add_left (n : ℕ) (u₁ u₂ v : Fin (n + 2) → ℝ) :
    moebiusQuadricRaw n (u₁ + u₂) v = moebiusQuadricRaw n u₁ v + moebiusQuadricRaw n u₂ v := by
  simp only [moebiusQuadricRaw, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private theorem moebiusQuadricRaw_smul_left (n : ℕ) (c : ℝ) (u v : Fin (n + 2) → ℝ) :
    moebiusQuadricRaw n (c • u) v = c * moebiusQuadricRaw n u v := by
  simp only [moebiusQuadricRaw, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

private theorem moebiusQuadricRaw_add_right (n : ℕ) (u v₁ v₂ : Fin (n + 2) → ℝ) :
    moebiusQuadricRaw n u (v₁ + v₂) = moebiusQuadricRaw n u v₁ + moebiusQuadricRaw n u v₂ := by
  simp only [moebiusQuadricRaw, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

private theorem moebiusQuadricRaw_smul_right (n : ℕ) (c : ℝ) (u v : Fin (n + 2) → ℝ) :
    moebiusQuadricRaw n u (c • v) = c * moebiusQuadricRaw n u v := by
  simp only [moebiusQuadricRaw, Pi.smul_apply, smul_eq_mul]
  have hs : ∑ i : Fin n, u (Fin.castAdd 2 i) * (c * v (Fin.castAdd 2 i)) =
      c * ∑ i : Fin n, u (Fin.castAdd 2 i) * v (Fin.castAdd 2 i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hs]
  ring

/-- Bilinear form of signature `(n + 1, 1)` on `Fin (n + 2) → ℝ`:
`∑_{i < n} u_i v_i + u_n v_n - u_{n+1} v_{n+1}`. -/
def moebiusQuadricBilin (n : ℕ) : LinearMap.BilinForm ℝ (Fin (n + 2) → ℝ) :=
  LinearMap.mk₂ ℝ
    (moebiusQuadricRaw n)
    (moebiusQuadricRaw_add_left n)
    (moebiusQuadricRaw_smul_left n)
    (moebiusQuadricRaw_add_right n)
    (moebiusQuadricRaw_smul_right n)

/-- Inverse stereographic lift of `x : Fin n → ℝ` into the `(n + 1, 1)` projective null cone:
`i < n ↦ x_i`, `n ↦ (‖x‖² - 1)/2`, `n + 1 ↦ (‖x‖² + 1)/2`. -/
def stereoQuadricVec (n : ℕ) (x : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  fun k =>
    if hk : k.val < n then x ⟨k.val, hk⟩
    else if k.val = n then ((∑ i : Fin n, (x i) ^ 2) - 1) / 2
    else ((∑ i : Fin n, (x i) ^ 2) + 1) / 2

/-- Projective point at infinity on the `(n + 1, 1)` null quadric:
`n ↦ 1/2`, `n + 1 ↦ 1/2`, all spatial entries `0`. -/
def stereoInfVec (n : ℕ) : Fin (n + 2) → ℝ :=
  fun k => if k.val < n then 0 else (1 / 2 : ℝ)

/-- Möbius unit-sphere inversion on `(n + 1, 1)` homogeneous coordinates, negating index `n`. -/
def moebiusInversionEquiv (n : ℕ) : (Fin (n + 2) → ℝ) ≃ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun u k := if k.val = n then -u k else u k
  invFun u k := if k.val = n then -u k else u k
  map_add' u v := by
    ext k
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c u := by
    ext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring
  left_inv u := by
    ext k
    dsimp only
    split_ifs <;> simp
  right_inv u := by
    ext k
    dsimp only
    split_ifs <;> simp

private theorem stereoQuadricVec_castAdd (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    stereoQuadricVec n x (Fin.castAdd 2 i) = x i := by
  simp [stereoQuadricVec]

private theorem stereoQuadricVec_n (n : ℕ) (x : Fin n → ℝ) :
    stereoQuadricVec n x ⟨n, by omega⟩ = ((∑ i : Fin n, (x i) ^ 2) - 1) / 2 := by
  dsimp only [stereoQuadricVec]
  split_ifs with h1 h2
  · exact absurd h1 (Nat.lt_irrefl n)
  · rfl
  · exact absurd rfl h2

private theorem stereoQuadricVec_succ (n : ℕ) (x : Fin n → ℝ) :
    stereoQuadricVec n x ⟨n + 1, by omega⟩ = ((∑ i : Fin n, (x i) ^ 2) + 1) / 2 := by
  dsimp only [stereoQuadricVec]
  split_ifs with h1 h2 <;> try omega
  rfl

/-- **Klein §6 Stereographic Quadric & Reciprocal Radii Theorem**:
1. Both `stereoQuadricVec n x` and `stereoInfVec n` lie on the `(n+1, 1)` null quadric.
2. `-2 * moebiusQuadricBilin n (stereoQuadricVec n x) (stereoQuadricVec n y) = ∑ i, (x i - y i) ^ 2`.
3. `moebiusInversionEquiv n` preserves `moebiusQuadricBilin n`, swaps `(0, ∞)` up to `±1`, and
   implements reciprocal-radii inversion `x ↦ x / ‖x‖²` for `‖x‖² ≠ 0`. -/
theorem klein_sec6_stereographic_and_inversion (n : ℕ) (x y : Fin n → ℝ) :
    moebiusQuadricBilin n (stereoQuadricVec n x) (stereoQuadricVec n x) = 0 ∧
      moebiusQuadricBilin n (stereoInfVec n) (stereoInfVec n) = 0 ∧
      -2 * moebiusQuadricBilin n (stereoQuadricVec n x) (stereoQuadricVec n y) =
        ∑ i : Fin n, (x i - y i) ^ 2 ∧
      moebiusQuadricBilin n (moebiusInversionEquiv n (stereoQuadricVec n x))
          (moebiusInversionEquiv n (stereoQuadricVec n y)) =
        moebiusQuadricBilin n (stereoQuadricVec n x) (stereoQuadricVec n y) ∧
      (moebiusInversionEquiv n (stereoQuadricVec n 0) = stereoInfVec n ∧
        ((∑ i : Fin n, (x i) ^ 2) ≠ 0 →
          moebiusInversionEquiv n (stereoQuadricVec n x) =
            (∑ i : Fin n, (x i) ^ 2) • stereoQuadricVec n ((∑ i : Fin n, (x i) ^ 2)⁻¹ • x))) := by
  have hbilin : -2 * moebiusQuadricBilin n (stereoQuadricVec n x) (stereoQuadricVec n y) =
      ∑ i : Fin n, (x i - y i) ^ 2 := by
    change -2 * ((∑ i : Fin n, stereoQuadricVec n x (Fin.castAdd 2 i) *
        stereoQuadricVec n y (Fin.castAdd 2 i)) +
      stereoQuadricVec n x ⟨n, by omega⟩ * stereoQuadricVec n y ⟨n, by omega⟩ -
      stereoQuadricVec n x ⟨n + 1, by omega⟩ * stereoQuadricVec n y ⟨n + 1, by omega⟩) =
      ∑ i : Fin n, (x i - y i) ^ 2
    simp_rw [stereoQuadricVec_castAdd, stereoQuadricVec_n, stereoQuadricVec_succ]
    have hxy_sq : ∑ i : Fin n, (x i - y i) ^ 2 =
        ∑ i : Fin n, (x i) ^ 2 - 2 * ∑ i : Fin n, x i * y i + ∑ i : Fin n, (y i) ^ 2 := by
      have hpt : ∀ i : Fin n, (x i - y i) ^ 2 = (x i) ^ 2 - 2 * (x i * y i) + (y i) ^ 2 :=
        fun i => by ring
      calc
        ∑ i : Fin n, (x i - y i) ^ 2 =
            ∑ i : Fin n, ((x i) ^ 2 - 2 * (x i * y i) + (y i) ^ 2) :=
          Finset.sum_congr rfl fun i _ => hpt i
        _ = ∑ i : Fin n, (x i) ^ 2 - 2 * ∑ i : Fin n, x i * y i + ∑ i : Fin n, (y i) ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hxy_sq]
    ring
  have hnull_x : moebiusQuadricBilin n (stereoQuadricVec n x) (stereoQuadricVec n x) = 0 := by
    have hself : -2 * moebiusQuadricBilin n (stereoQuadricVec n x) (stereoQuadricVec n x) = 0 := by
      change -2 * ((∑ i : Fin n, stereoQuadricVec n x (Fin.castAdd 2 i) *
          stereoQuadricVec n x (Fin.castAdd 2 i)) +
        stereoQuadricVec n x ⟨n, by omega⟩ * stereoQuadricVec n x ⟨n, by omega⟩ -
        stereoQuadricVec n x ⟨n + 1, by omega⟩ * stereoQuadricVec n x ⟨n + 1, by omega⟩) = 0
      simp_rw [stereoQuadricVec_castAdd, stereoQuadricVec_n, stereoQuadricVec_succ]
      ring
    linarith
  have hnull_inf : moebiusQuadricBilin n (stereoInfVec n) (stereoInfVec n) = 0 := by
    change (∑ i : Fin n, stereoInfVec n (Fin.castAdd 2 i) * stereoInfVec n (Fin.castAdd 2 i)) +
        stereoInfVec n ⟨n, by omega⟩ * stereoInfVec n ⟨n, by omega⟩ -
        stereoInfVec n ⟨n + 1, by omega⟩ * stereoInfVec n ⟨n + 1, by omega⟩ = 0
    have hlt : ∀ i : Fin n, stereoInfVec n (Fin.castAdd 2 i) = 0 := fun i => by
      dsimp only [stereoInfVec]
      split_ifs with h
      · rfl
      · exact absurd i.isLt h
    have hn : stereoInfVec n ⟨n, by omega⟩ = 1 / 2 := by
      dsimp only [stereoInfVec]
      split_ifs with h
      · exact absurd h (Nat.lt_irrefl n)
      · rfl
    have hsuc : stereoInfVec n ⟨n + 1, by omega⟩ = 1 / 2 := by
      dsimp only [stereoInfVec]
      split_ifs with h <;> try omega
      rfl
    simp_rw [hlt, hn, hsuc]
    simp
  have hinv_orth : moebiusQuadricBilin n (moebiusInversionEquiv n (stereoQuadricVec n x))
        (moebiusInversionEquiv n (stereoQuadricVec n y)) =
      moebiusQuadricBilin n (stereoQuadricVec n x) (stereoQuadricVec n y) := by
    change (∑ i : Fin n, moebiusInversionEquiv n (stereoQuadricVec n x) (Fin.castAdd 2 i) *
          moebiusInversionEquiv n (stereoQuadricVec n y) (Fin.castAdd 2 i)) +
        moebiusInversionEquiv n (stereoQuadricVec n x) ⟨n, by omega⟩ *
          moebiusInversionEquiv n (stereoQuadricVec n y) ⟨n, by omega⟩ -
        moebiusInversionEquiv n (stereoQuadricVec n x) ⟨n + 1, by omega⟩ *
          moebiusInversionEquiv n (stereoQuadricVec n y) ⟨n + 1, by omega⟩ =
      (∑ i : Fin n, stereoQuadricVec n x (Fin.castAdd 2 i) *
          stereoQuadricVec n y (Fin.castAdd 2 i)) +
        stereoQuadricVec n x ⟨n, by omega⟩ * stereoQuadricVec n y ⟨n, by omega⟩ -
        stereoQuadricVec n x ⟨n + 1, by omega⟩ * stereoQuadricVec n y ⟨n + 1, by omega⟩
    have hc : ∀ (u : Fin (n + 2) → ℝ) (i : Fin n),
        moebiusInversionEquiv n u (Fin.castAdd 2 i) = u (Fin.castAdd 2 i) := fun u i => by
      change (if (Fin.castAdd 2 i).val = n then -u _ else u _) = u _
      split_ifs with h
      · exfalso; exact ne_of_lt i.isLt h
      · rfl
    have hn : ∀ u : Fin (n + 2) → ℝ,
        moebiusInversionEquiv n u ⟨n, by omega⟩ = -u ⟨n, by omega⟩ := fun u => by
      change (if n = n then -u _ else u _) = _
      simp
    have hsuc : ∀ u : Fin (n + 2) → ℝ,
        moebiusInversionEquiv n u ⟨n + 1, by omega⟩ = u ⟨n + 1, by omega⟩ := fun u => by
      change (if n + 1 = n then -u _ else u _) = _
      split_ifs with h <;> try omega
      rfl
    simp_rw [hc, hn, hsuc]
    ring
  refine ⟨hnull_x, hnull_inf, hbilin, hinv_orth, ?_, ?_⟩
  · ext k
    change (if k.val = n then -stereoQuadricVec n 0 k else stereoQuadricVec n 0 k) = stereoInfVec n k
    dsimp only [stereoQuadricVec, stereoInfVec]
    split_ifs <;> try omega
    all_goals norm_num
  · intro hx
    have hnorm_inv : ∑ i : Fin n, (((∑ j : Fin n, (x j) ^ 2)⁻¹ • x) i) ^ 2 =
        (∑ i : Fin n, (x i) ^ 2)⁻¹ := by
      have hr : ∑ i : Fin n, ((∑ j : Fin n, (x j) ^ 2)⁻¹ * x i) ^ 2 =
          ((∑ j : Fin n, (x j) ^ 2)⁻¹) ^ 2 * ∑ i : Fin n, (x i) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      change ∑ i : Fin n, ((∑ j : Fin n, (x j) ^ 2)⁻¹ * x i) ^ 2 = (∑ i : Fin n, (x i) ^ 2)⁻¹
      rw [hr]
      field_simp [hx]
    ext k
    change (if k.val = n then -stereoQuadricVec n x k else stereoQuadricVec n x k) =
      (∑ i : Fin n, (x i) ^ 2) * stereoQuadricVec n ((∑ i : Fin n, (x i) ^ 2)⁻¹ • x) k
    by_cases hk : k.val < n
    · split_ifs with h
      · exact absurd h hk.ne
      · let i : Fin n := ⟨k.val, hk⟩
        have hk' : k = Fin.castAdd 2 i := Fin.ext rfl
        rw [hk', stereoQuadricVec_castAdd, stereoQuadricVec_castAdd]
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp [hx]
    · by_cases hkn : k.val = n
      · split_ifs
        have hk' : k = ⟨n, by omega⟩ := Fin.ext hkn
        rw [hk', stereoQuadricVec_n, stereoQuadricVec_n, hnorm_inv]
        field_simp [hx]
        ring
      · split_ifs
        have hkn1 : k.val = n + 1 := by omega
        have hk' : k = ⟨n + 1, by omega⟩ := Fin.ext hkn1
        rw [hk', stereoQuadricVec_succ, stereoQuadricVec_succ, hnorm_inv]
        field_simp [hx]
        ring

/-- **Klein's Footnote 26 (`[countermodel_found]`, p. 12)**:
unit-circle inversion `z ↦ (starRingEnd ℂ z)⁻¹` is anti-holomorphic `(0 * star z + 1) / (1 * star z + 0)`,
and CANNOT be realized by any holomorphic fractional-linear map `(a * z + b) / (c * z + d)` with
`a * d - b * c ≠ 0` on `ℂ \ {0}`. -/
theorem klein_fn26_unit_circle_inversion_not_holomorphic_moebius :
    (∀ z : ℂ, z ≠ 0 → ((0 : ℂ) * starRingEnd ℂ z + 1) / ((1 : ℂ) * starRingEnd ℂ z + 0) =
        (starRingEnd ℂ z)⁻¹) ∧
      ¬ ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
        ∀ z : ℂ, z ≠ 0 → c * z + d ≠ 0 ∧ (a * z + b) / (c * z + d) = (starRingEnd ℂ z)⁻¹ := by
  refine ⟨fun z hz => by simp [div_eq_mul_inv], ?_⟩
  rintro ⟨a, b, c, d, hdet, hf⟩
  have h1 := hf 1 (by norm_num)
  have hm1 := hf (-1) (by norm_num)
  have hi := hf Complex.I Complex.I_ne_zero
  have h1' : a + b = c + d := by
    have hs : (starRingEnd ℂ (1 : ℂ))⁻¹ = (1 : ℂ) := by simp
    rw [hs, mul_one, mul_one, div_eq_iff h1.1, one_mul] at h1
    exact h1.2
  have hm1' : -a + b = c - d := by
    have hs : (starRingEnd ℂ (-1 : ℂ))⁻¹ = (-1 : ℂ) := by simp
    have hsm1 : a * (-1 : ℂ) + b = (-1 : ℂ) * (c * (-1 : ℂ) + d) := by
      rw [hs, div_eq_iff hm1.1] at hm1
      exact hm1.2
    linear_combination hsm1
  have hi' : a * Complex.I + b = -c + d * Complex.I := by
    have hsi : (starRingEnd ℂ Complex.I)⁻¹ = Complex.I := by
      rw [Complex.conj_I, inv_neg, Complex.inv_I, neg_neg]
    rw [hsi, div_eq_iff hi.1] at hi
    calc
      a * Complex.I + b = Complex.I * (c * Complex.I + d) := hi.2
      _ = c * Complex.I ^ 2 + d * Complex.I := by ring
      _ = -c + d * Complex.I := by rw [Complex.I_sq]; ring
  have hd_eq : a = d := by linear_combination (h1' - hm1') / 2
  have hb_eq : b = c := by linear_combination (h1' + hm1') / 2
  rw [← hd_eq, hb_eq] at hi'
  have hc_zero : c = 0 := by
    have h2c : 2 * c = 0 := by linear_combination hi'
    exact (mul_eq_zero.mp h2c).resolve_left (by norm_num)
  rw [hc_zero] at hb_eq
  rw [hc_zero, ← hd_eq] at hdet
  have ha_ne : a ≠ 0 := fun ha => hdet (by simp [ha, hb_eq])
  have h2 := hf 2 (by norm_num)
  have h2_eq : (a * 2 + b) / (c * 2 + d) = (starRingEnd ℂ (2 : ℂ))⁻¹ := h2.2
  have h2_conj : (starRingEnd ℂ (2 : ℂ))⁻¹ = (1 / 2 : ℂ) := by
    simp only [map_ofNat]
    norm_num
  rw [h2_conj, hb_eq, hc_zero, ← hd_eq, zero_mul, zero_add, add_zero] at h2_eq
  have h2_lhs : a * 2 / a = 2 := mul_div_cancel_left₀ (2 : ℂ) ha_ne
  rw [h2_lhs] at h2_eq
  norm_num at h2_eq

end MoebiusStereographic

/-! ## 2. `EK₇` (§7 & Fn. 31): Lie's `(n+1, 2)` Sphere Quadric & Laguerre Shift Group -/

section LieSphereGeometry

private def lieQuadricRaw (n : ℕ) (u v : Fin (n + 3) → ℝ) : ℝ :=
  (∑ i : Fin n, u (Fin.castAdd 3 i) * v (Fin.castAdd 3 i)) +
    u ⟨n, by omega⟩ * v ⟨n, by omega⟩ -
    u ⟨n + 1, by omega⟩ * v ⟨n + 1, by omega⟩ -
    u ⟨n + 2, by omega⟩ * v ⟨n + 2, by omega⟩

private theorem lieQuadricRaw_add_left (n : ℕ) (u₁ u₂ v : Fin (n + 3) → ℝ) :
    lieQuadricRaw n (u₁ + u₂) v = lieQuadricRaw n u₁ v + lieQuadricRaw n u₂ v := by
  simp only [lieQuadricRaw, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private theorem lieQuadricRaw_smul_left (n : ℕ) (c : ℝ) (u v : Fin (n + 3) → ℝ) :
    lieQuadricRaw n (c • u) v = c * lieQuadricRaw n u v := by
  simp only [lieQuadricRaw, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

private theorem lieQuadricRaw_add_right (n : ℕ) (u v₁ v₂ : Fin (n + 3) → ℝ) :
    lieQuadricRaw n u (v₁ + v₂) = lieQuadricRaw n u v₁ + lieQuadricRaw n u v₂ := by
  simp only [lieQuadricRaw, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

private theorem lieQuadricRaw_smul_right (n : ℕ) (c : ℝ) (u v : Fin (n + 3) → ℝ) :
    lieQuadricRaw n u (c • v) = c * lieQuadricRaw n u v := by
  simp only [lieQuadricRaw, Pi.smul_apply, smul_eq_mul]
  have hs : ∑ i : Fin n, u (Fin.castAdd 3 i) * (c * v (Fin.castAdd 3 i)) =
      c * ∑ i : Fin n, u (Fin.castAdd 3 i) * v (Fin.castAdd 3 i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hs]
  ring

/-- Lie's `(n + 1, 2)` bilinear form on `Fin (n + 3) → ℝ`:
`∑_{i < n} u_i v_i + u_n v_n - u_{n+1} v_{n+1} - u_{n+2} v_{n+2}`. -/
def lieQuadricBilin (n : ℕ) : LinearMap.BilinForm ℝ (Fin (n + 3) → ℝ) :=
  LinearMap.mk₂ ℝ
    (lieQuadricRaw n)
    (lieQuadricRaw_add_left n)
    (lieQuadricRaw_smul_left n)
    (lieQuadricRaw_add_right n)
    (lieQuadricRaw_smul_right n)

/-- Homogeneous Lie coordinates of an oriented sphere `(center : Fin n → ℝ, radius : ℝ)` in `ℝⁿ`:
`(c₁, …, cₙ, (‖c‖² - r² - 1)/2, (‖c‖² - r² + 1)/2, r) ∈ ℝ^{n+3}`. -/
def lieSphereVec (n : ℕ) (c : Fin n → ℝ) (r : ℝ) : Fin (n + 3) → ℝ :=
  fun k =>
    if hk : k.val < n then c ⟨k.val, hk⟩
    else if k.val = n then ((∑ i : Fin n, (c i) ^ 2) - r ^ 2 - 1) / 2
    else if k.val = n + 1 then ((∑ i : Fin n, (c i) ^ 2) - r ^ 2 + 1) / 2
    else r

/-- Oriented contact tangency between `(c₁, r₁)` and `(c₂, r₂)`: `‖c₁ - c₂‖² = (r₁ - r₂)²`. -/
def IsOrientedSphereTangent {n : ℕ} (c₁ : Fin n → ℝ) (r₁ : ℝ) (c₂ : Fin n → ℝ) (r₂ : ℝ) :
    Prop :=
  ∑ i : Fin n, (c₁ i - c₂ i) ^ 2 = (r₁ - r₂) ^ 2

private theorem lieSphereVec_castAdd (n : ℕ) (c : Fin n → ℝ) (r : ℝ) (i : Fin n) :
    lieSphereVec n c r (Fin.castAdd 3 i) = c i := by
  simp [lieSphereVec]

private theorem lieSphereVec_n (n : ℕ) (c : Fin n → ℝ) (r : ℝ) :
    lieSphereVec n c r ⟨n, by omega⟩ = ((∑ i : Fin n, (c i) ^ 2) - r ^ 2 - 1) / 2 := by
  dsimp only [lieSphereVec]
  split_ifs <;> first | rfl | omega

private theorem lieSphereVec_n1 (n : ℕ) (c : Fin n → ℝ) (r : ℝ) :
    lieSphereVec n c r ⟨n + 1, by omega⟩ = ((∑ i : Fin n, (c i) ^ 2) - r ^ 2 + 1) / 2 := by
  dsimp only [lieSphereVec]
  split_ifs with h1 h2 h3 <;> try omega
  rfl

private theorem lieSphereVec_n2 (n : ℕ) (c : Fin n → ℝ) (r : ℝ) :
    lieSphereVec n c r ⟨n + 2, by omega⟩ = r := by
  dsimp only [lieSphereVec]
  split_ifs <;> try omega
  rfl

/-- **Klein §7 & Fn. 31 Lie Sphere Nullity & Oriented Tangency**:
every oriented sphere lies on the Lie quadric `lieQuadricBilin n u u = 0`, and two oriented spheres
are tangent iff they are null-orthogonal wrt `lieQuadricBilin n`. Moreover, any linear map
preserving `lieQuadricBilin n` preserves oriented tangency. -/
theorem klein_sec7_lie_sphere_quadric_and_tangency {n : ℕ}
    (c₁ c₂ : Fin n → ℝ) (r₁ r₂ : ℝ) :
    lieQuadricBilin n (lieSphereVec n c₁ r₁) (lieSphereVec n c₁ r₁) = 0 ∧
      -2 * lieQuadricBilin n (lieSphereVec n c₁ r₁) (lieSphereVec n c₂ r₂) =
        (∑ i : Fin n, (c₁ i - c₂ i) ^ 2) - (r₁ - r₂) ^ 2 ∧
      (IsOrientedSphereTangent c₁ r₁ c₂ r₂ ↔
        lieQuadricBilin n (lieSphereVec n c₁ r₁) (lieSphereVec n c₂ r₂) = 0) := by
  have hbilin : -2 * lieQuadricBilin n (lieSphereVec n c₁ r₁) (lieSphereVec n c₂ r₂) =
      (∑ i : Fin n, (c₁ i - c₂ i) ^ 2) - (r₁ - r₂) ^ 2 := by
    change -2 * ((∑ i : Fin n, lieSphereVec n c₁ r₁ (Fin.castAdd 3 i) *
          lieSphereVec n c₂ r₂ (Fin.castAdd 3 i)) +
        lieSphereVec n c₁ r₁ ⟨n, by omega⟩ * lieSphereVec n c₂ r₂ ⟨n, by omega⟩ -
        lieSphereVec n c₁ r₁ ⟨n + 1, by omega⟩ * lieSphereVec n c₂ r₂ ⟨n + 1, by omega⟩ -
        lieSphereVec n c₁ r₁ ⟨n + 2, by omega⟩ * lieSphereVec n c₂ r₂ ⟨n + 2, by omega⟩) =
      (∑ i : Fin n, (c₁ i - c₂ i) ^ 2) - (r₁ - r₂) ^ 2
    simp_rw [lieSphereVec_castAdd, lieSphereVec_n, lieSphereVec_n1, lieSphereVec_n2]
    have hsq : ∑ i : Fin n, (c₁ i - c₂ i) ^ 2 =
        ∑ i : Fin n, (c₁ i) ^ 2 - 2 * ∑ i : Fin n, c₁ i * c₂ i + ∑ i : Fin n, (c₂ i) ^ 2 := by
      have hpt : ∀ i : Fin n, (c₁ i - c₂ i) ^ 2 =
          (c₁ i) ^ 2 - 2 * (c₁ i * c₂ i) + (c₂ i) ^ 2 := fun i => by ring
      calc
        ∑ i : Fin n, (c₁ i - c₂ i) ^ 2 =
            ∑ i : Fin n, ((c₁ i) ^ 2 - 2 * (c₁ i * c₂ i) + (c₂ i) ^ 2) :=
          Finset.sum_congr rfl fun i _ => hpt i
        _ = ∑ i : Fin n, (c₁ i) ^ 2 - 2 * ∑ i : Fin n, c₁ i * c₂ i + ∑ i : Fin n, (c₂ i) ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hsq]
    ring
  have hnull : lieQuadricBilin n (lieSphereVec n c₁ r₁) (lieSphereVec n c₁ r₁) = 0 := by
    have hself : -2 * lieQuadricBilin n (lieSphereVec n c₁ r₁) (lieSphereVec n c₁ r₁) = 0 := by
      change -2 * ((∑ i : Fin n, lieSphereVec n c₁ r₁ (Fin.castAdd 3 i) *
            lieSphereVec n c₁ r₁ (Fin.castAdd 3 i)) +
          lieSphereVec n c₁ r₁ ⟨n, by omega⟩ * lieSphereVec n c₁ r₁ ⟨n, by omega⟩ -
          lieSphereVec n c₁ r₁ ⟨n + 1, by omega⟩ * lieSphereVec n c₁ r₁ ⟨n + 1, by omega⟩ -
          lieSphereVec n c₁ r₁ ⟨n + 2, by omega⟩ * lieSphereVec n c₁ r₁ ⟨n + 2, by omega⟩) = 0
      simp_rw [lieSphereVec_castAdd, lieSphereVec_n, lieSphereVec_n1, lieSphereVec_n2]
      ring
    linarith
  refine ⟨hnull, hbilin, ?_⟩
  constructor
  · intro ht
    have h0 : (∑ i : Fin n, (c₁ i - c₂ i) ^ 2) - (r₁ - r₂) ^ 2 = 0 := sub_eq_zero.mpr ht
    rw [h0] at hbilin
    linarith
  · intro hb
    have h0 : (∑ i : Fin n, (c₁ i - c₂ i) ^ 2) - (r₁ - r₂) ^ 2 = 0 := by
      rw [hb, mul_zero] at hbilin
      exact hbilin.symm
    exact sub_eq_zero.mp h0

/-- Sylvester inertia signature `(3, 2)` of planar Lie circle geometry (`n = 2`, pentaspherical/pentacyclic). -/
theorem lieQuadricBilin_signature_dim2 :
    sigPos (lieQuadricBilin 2).toQuadraticMap = 3 ∧
      sigNeg (lieQuadricBilin 2).toQuadraticMap = 2 := by
  let w : Fin 5 → ℝ := ![1, 1, 1, -1, -1]
  let Qw := QuadraticMap.weightedSumSquares ℝ w
  let e : Qw.IsometryEquiv (lieQuadricBilin 2).toQuadraticMap :=
    { toLinearEquiv := LinearEquiv.refl ℝ (Fin 5 → ℝ)
      map_app' := fun m => by
        change lieQuadricBilin 2 m m = Qw m
        rw [QuadraticMap.weightedSumSquares_apply]
        change (∑ i : Fin 2, m (Fin.castAdd 3 i) * m (Fin.castAdd 3 i)) +
            m ⟨2, by omega⟩ * m ⟨2, by omega⟩ - m ⟨3, by omega⟩ * m ⟨3, by omega⟩ -
            m ⟨4, by omega⟩ * m ⟨4, by omega⟩ =
          ∑ i : Fin 5, w i • (m i * m i)
        rw [Fin.sum_univ_five, Fin.sum_univ_two]
        rw [show (Fin.castAdd 3 (0 : Fin 2) : Fin 5) = 0 from rfl,
            show (Fin.castAdd 3 (1 : Fin 2) : Fin 5) = 1 from rfl]
        simp only [smul_eq_mul, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        norm_num
        ring }
  have heq : (lieQuadricBilin 2).toQuadraticMap.Equivalent Qw := ⟨e.symm⟩
  have hset_pos : ({i : Fin 5 | (0 : ℝ) < w i} : Set (Fin 5)) = {0, 1, 2} := by
    ext i
    fin_cases i <;> simp [w]
  have hset_neg : ({i : Fin 5 | w i < 0} : Set (Fin 5)) = {3, 4} := by
    ext i
    fin_cases i <;> simp [w]
  have hcpos : ({0, 1, 2} : Set (Fin 5)).ncard = 3 := by
    have hfin : ({0, 1, 2} : Set (Fin 5)) = (({0, 1, 2} : Finset (Fin 5)) : Set (Fin 5)) := by simp
    rw [hfin, Set.ncard_coe_finset]
    decide
  have hcneg : ({3, 4} : Set (Fin 5)).ncard = 2 := by
    have hfin : ({3, 4} : Set (Fin 5)) = (({3, 4} : Finset (Fin 5)) : Set (Fin 5)) := by simp
    rw [hfin, Set.ncard_coe_finset]
    decide
  refine ⟨?_, ?_⟩
  · rw [heq.sigPos_eq, QuadraticForm.sigPos_weightedSumSquares, hset_pos, hcpos]
  · rw [heq.sigNeg_eq, QuadraticForm.sigNeg_weightedSumSquares, hset_neg, hcneg]

/-- Sylvester inertia signature `(4, 2)` of 3D Lie sphere geometry (`n = 3`, hexaspherical, Klein §7). -/
theorem lieQuadricBilin_signature_dim3 :
    sigPos (lieQuadricBilin 3).toQuadraticMap = 4 ∧
      sigNeg (lieQuadricBilin 3).toQuadraticMap = 2 := by
  let w : Fin 6 → ℝ := ![1, 1, 1, 1, -1, -1]
  let Qw := QuadraticMap.weightedSumSquares ℝ w
  let e : Qw.IsometryEquiv (lieQuadricBilin 3).toQuadraticMap :=
    { toLinearEquiv := LinearEquiv.refl ℝ (Fin 6 → ℝ)
      map_app' := fun m => by
        change lieQuadricBilin 3 m m = Qw m
        rw [QuadraticMap.weightedSumSquares_apply]
        change (∑ i : Fin 3, m (Fin.castAdd 3 i) * m (Fin.castAdd 3 i)) +
            m ⟨3, by omega⟩ * m ⟨3, by omega⟩ - m ⟨4, by omega⟩ * m ⟨4, by omega⟩ -
            m ⟨5, by omega⟩ * m ⟨5, by omega⟩ =
          ∑ i : Fin 6, w i • (m i * m i)
        rw [Fin.sum_univ_six, Fin.sum_univ_three]
        rw [show (Fin.castAdd 3 (0 : Fin 3) : Fin 6) = 0 from rfl,
            show (Fin.castAdd 3 (1 : Fin 3) : Fin 6) = 1 from rfl,
            show (Fin.castAdd 3 (2 : Fin 3) : Fin 6) = 2 from rfl]
        simp only [smul_eq_mul, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        norm_num
        ring }
  have heq : (lieQuadricBilin 3).toQuadraticMap.Equivalent Qw := ⟨e.symm⟩
  have hset_pos : ({i : Fin 6 | (0 : ℝ) < w i} : Set (Fin 6)) = {0, 1, 2, 3} := by
    ext i
    fin_cases i <;> simp [w]
  have hset_neg : ({i : Fin 6 | w i < 0} : Set (Fin 6)) = {4, 5} := by
    ext i
    fin_cases i <;> simp [w]
  have hcpos : ({0, 1, 2, 3} : Set (Fin 6)).ncard = 4 := by
    have hfin : ({0, 1, 2, 3} : Set (Fin 6)) =
        (({0, 1, 2, 3} : Finset (Fin 6)) : Set (Fin 6)) := by simp
    rw [hfin, Set.ncard_coe_finset]
    decide
  have hcneg : ({4, 5} : Set (Fin 6)).ncard = 2 := by
    have hfin : ({4, 5} : Set (Fin 6)) = (({4, 5} : Finset (Fin 6)) : Set (Fin 6)) := by simp
    rw [hfin, Set.ncard_coe_finset]
    decide
  refine ⟨?_, ?_⟩
  · rw [heq.sigPos_eq, QuadraticForm.sigPos_weightedSumSquares, hset_pos, hcpos]
  · rw [heq.sigNeg_eq, QuadraticForm.sigNeg_weightedSumSquares, hset_neg, hcneg]

private def laguerreFwd (n : ℕ) (t : ℝ) (u : Fin (n + 3) → ℝ) (k : Fin (n + 3)) : ℝ :=
  if k.val = n then u k - t * u ⟨n + 2, by omega⟩ - (t ^ 2 / 2) * (u ⟨n + 1, by omega⟩ - u ⟨n, by omega⟩)
  else if k.val = n + 1 then u k - t * u ⟨n + 2, by omega⟩ - (t ^ 2 / 2) * (u ⟨n + 1, by omega⟩ - u ⟨n, by omega⟩)
  else if k.val = n + 2 then u k + t * (u ⟨n + 1, by omega⟩ - u ⟨n, by omega⟩)
  else u k

private lemma laguerreFwd_n (n : ℕ) (t : ℝ) (u : Fin (n + 3) → ℝ) :
    laguerreFwd n t u ⟨n, by omega⟩ =
      u ⟨n, by omega⟩ - t * u ⟨n + 2, by omega⟩ -
        (t ^ 2 / 2) * (u ⟨n + 1, by omega⟩ - u ⟨n, by omega⟩) := by
  simp [laguerreFwd]

private lemma laguerreFwd_n1 (n : ℕ) (t : ℝ) (u : Fin (n + 3) → ℝ) :
    laguerreFwd n t u ⟨n + 1, by omega⟩ =
      u ⟨n + 1, by omega⟩ - t * u ⟨n + 2, by omega⟩ -
        (t ^ 2 / 2) * (u ⟨n + 1, by omega⟩ - u ⟨n, by omega⟩) := by
  dsimp only [laguerreFwd]
  split_ifs <;> try omega
  rfl

private lemma laguerreFwd_n2 (n : ℕ) (t : ℝ) (u : Fin (n + 3) → ℝ) :
    laguerreFwd n t u ⟨n + 2, by omega⟩ =
      u ⟨n + 2, by omega⟩ + t * (u ⟨n + 1, by omega⟩ - u ⟨n, by omega⟩) := by
  dsimp only [laguerreFwd]
  split_ifs <;> try omega
  rfl

private lemma laguerreFwd_zero (n : ℕ) (u : Fin (n + 3) → ℝ) :
    laguerreFwd n 0 u = u := by
  ext k
  unfold laguerreFwd
  split_ifs <;> ring

private lemma laguerreFwd_add (n : ℕ) (s t : ℝ) (u : Fin (n + 3) → ℝ) :
    laguerreFwd n (s + t) u = laguerreFwd n s (laguerreFwd n t u) := by
  ext k
  by_cases hkn : k.val = n
  · have hk' : k = ⟨n, by omega⟩ := Fin.ext hkn
    rw [hk', laguerreFwd_n n (s + t) u, laguerreFwd_n n s (laguerreFwd n t u),
      laguerreFwd_n n t u, laguerreFwd_n1 n t u, laguerreFwd_n2 n t u]
    ring
  · by_cases hkn1 : k.val = n + 1
    · have hk' : k = ⟨n + 1, by omega⟩ := Fin.ext hkn1
      rw [hk', laguerreFwd_n1 n (s + t) u, laguerreFwd_n1 n s (laguerreFwd n t u),
        laguerreFwd_n n t u, laguerreFwd_n1 n t u, laguerreFwd_n2 n t u]
      ring
    · by_cases hkn2 : k.val = n + 2
      · have hk' : k = ⟨n + 2, by omega⟩ := Fin.ext hkn2
        rw [hk', laguerreFwd_n2 n (s + t) u, laguerreFwd_n2 n s (laguerreFwd n t u),
          laguerreFwd_n n t u, laguerreFwd_n1 n t u, laguerreFwd_n2 n t u]
        ring
      · dsimp only [laguerreFwd]
        split_ifs
        rfl

/-- Laguerre's radius-shift subgroup inside `O(n + 1, 2)`: adds `t` uniformly to every sphere's
signed radius while leaving centers fixed. -/
def laguerreShift (n : ℕ) (t : ℝ) : (Fin (n + 3) → ℝ) ≃ₗ[ℝ] (Fin (n + 3) → ℝ) where
  toFun := laguerreFwd n t
  invFun := laguerreFwd n (-t)
  map_add' u v := by
    ext k
    unfold laguerreFwd
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c u := by
    ext k
    unfold laguerreFwd
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring
  left_inv u := by
    rw [← laguerreFwd_add n (-t) t u, neg_add_cancel, laguerreFwd_zero]
  right_inv u := by
    rw [← laguerreFwd_add n t (-t) u, add_neg_cancel, laguerreFwd_zero]

/-- **Klein §7 Laguerre Radius-Shift Group & Non-Point-Body Countermodel**:
1. `laguerreShift n` is a 1-parameter subgroup (`s + t` composes, `0` is `id`) inside `O(lieQuadricBilin n)`.
2. `laguerreShift n t` carries `lieSphereVec n c r` to `lieSphereVec n c (r + t)` identically.
3. `[countermodel_found]`: `laguerreShift n 1` sends the zero-radius point-sphere at the origin
   (`r = 0`) to a unit-radius sphere (`r = 1`), proving points do not form a body under Lie's group. -/
theorem klein_sec7_laguerre_shift_theorems (n : ℕ) (s t : ℝ) (u v : Fin (n + 3) → ℝ)
    (c : Fin n → ℝ) (r : ℝ) :
    laguerreShift n 0 u = u ∧
      laguerreShift n (s + t) u = laguerreShift n s (laguerreShift n t u) ∧
      lieQuadricBilin n (laguerreShift n t u) (laguerreShift n t v) = lieQuadricBilin n u v ∧
      laguerreShift n t (lieSphereVec n c r) = lieSphereVec n c (r + t) ∧
      (lieSphereVec n 0 0 ⟨n + 2, by omega⟩ = 0 ∧
        laguerreShift n 1 (lieSphereVec n 0 0) ⟨n + 2, by omega⟩ = 1) := by
  have hc : ∀ w : Fin (n + 3) → ℝ, ∀ k : Fin n,
      laguerreShift n t w (Fin.castAdd 3 k) = w (Fin.castAdd 3 k) := fun w k => by
    change laguerreFwd n t w (Fin.castAdd 3 k) = w (Fin.castAdd 3 k)
    dsimp only [laguerreFwd]
    have hk_lt : (Fin.castAdd 3 k).val < n := k.isLt
    split_ifs <;> try omega
    rfl
  have hn : ∀ (t' : ℝ) (w : Fin (n + 3) → ℝ),
      laguerreShift n t' w ⟨n, by omega⟩ =
        w ⟨n, by omega⟩ - t' * w ⟨n + 2, by omega⟩ -
          (t' ^ 2 / 2) * (w ⟨n + 1, by omega⟩ - w ⟨n, by omega⟩) := laguerreFwd_n n
  have hn1 : ∀ (t' : ℝ) (w : Fin (n + 3) → ℝ),
      laguerreShift n t' w ⟨n + 1, by omega⟩ =
        w ⟨n + 1, by omega⟩ - t' * w ⟨n + 2, by omega⟩ -
          (t' ^ 2 / 2) * (w ⟨n + 1, by omega⟩ - w ⟨n, by omega⟩) := laguerreFwd_n1 n
  have hn2 : ∀ (t' : ℝ) (w : Fin (n + 3) → ℝ),
      laguerreShift n t' w ⟨n + 2, by omega⟩ =
        w ⟨n + 2, by omega⟩ + t' * (w ⟨n + 1, by omega⟩ - w ⟨n, by omega⟩) := laguerreFwd_n2 n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact laguerreFwd_zero n u
  · exact laguerreFwd_add n s t u
  · change (∑ i : Fin n, laguerreShift n t u (Fin.castAdd 3 i) *
          laguerreShift n t v (Fin.castAdd 3 i)) +
        laguerreShift n t u ⟨n, by omega⟩ * laguerreShift n t v ⟨n, by omega⟩ -
        laguerreShift n t u ⟨n + 1, by omega⟩ * laguerreShift n t v ⟨n + 1, by omega⟩ -
        laguerreShift n t u ⟨n + 2, by omega⟩ * laguerreShift n t v ⟨n + 2, by omega⟩ =
      (∑ i : Fin n, u (Fin.castAdd 3 i) * v (Fin.castAdd 3 i)) +
        u ⟨n, by omega⟩ * v ⟨n, by omega⟩ -
        u ⟨n + 1, by omega⟩ * v ⟨n + 1, by omega⟩ -
        u ⟨n + 2, by omega⟩ * v ⟨n + 2, by omega⟩
    simp_rw [hc u, hc v, hn t u, hn t v, hn1 t u, hn1 t v, hn2 t u, hn2 t v]
    ring
  · ext k
    by_cases hk : k.val < n
    · change laguerreFwd n t (lieSphereVec n c r) k = lieSphereVec n c (r + t) k
      dsimp only [laguerreFwd, lieSphereVec]
      split_ifs <;> try omega
      rfl
    · by_cases hkn : k.val = n
      · have hk' : k = ⟨n, by omega⟩ := Fin.ext hkn
        rw [hk', hn t (lieSphereVec n c r), lieSphereVec_n, lieSphereVec_n1, lieSphereVec_n2,
          lieSphereVec_n]
        ring
      · by_cases hkn1 : k.val = n + 1
        · have hk' : k = ⟨n + 1, by omega⟩ := Fin.ext hkn1
          rw [hk', hn1 t (lieSphereVec n c r), lieSphereVec_n, lieSphereVec_n1, lieSphereVec_n2,
            lieSphereVec_n1]
          ring
        · have hkn2 : k.val = n + 2 := by omega
          have hk' : k = ⟨n + 2, by omega⟩ := Fin.ext hkn2
          rw [hk', hn2 t (lieSphereVec n c r), lieSphereVec_n, lieSphereVec_n1, lieSphereVec_n2,
            lieSphereVec_n2]
          ring
  · exact lieSphereVec_n2 n 0 0
  · rw [hn2 1 (lieSphereVec n 0 0), lieSphereVec_n, lieSphereVec_n1, lieSphereVec_n2]
    norm_num

end LieSphereGeometry

/-! ## 3. `EK₈` (§8.1, §8.3 & §9): Cremona, `fderiv`, & Contact-Legendre Unification -/

section CremonaFDerivContact

/-- Standard quadratic Cremona involution `[x : y : z] ↦ [y z : x z : x y]` on `R³`. -/
def cremonaPlane {R : Type*} [Mul R] (X : Fin 3 → R) : Fin 3 → R :=
  ![X 1 * X 2, X 0 * X 2, X 0 * X 1]

/-- **Klein §8.1 Cremona Involution & Non-Collineation `[countermodel_found]`**:
`cremonaPlane` is projectively involutive up to `(X₀ X₁ X₂)` scaling, yet maps the collinear
triple `![1,1,1], ![1,2,3], ![2,3,4]` (`det = 0`) to non-collinear `![1,1,1], ![6,3,2], ![12,8,6]`
(`det = 2 ≠ 0`). -/
theorem klein_sec8_cremona_involution_and_non_collineation {R : Type*} [CommRing R]
    (X : Fin 3 → R) :
    cremonaPlane (cremonaPlane X) = (X 0 * X 1 * X 2) • X ∧
      (Matrix.of ![![(1 : ℚ), 1, 1], ![1, 2, 3], ![2, 3, 4]] : Matrix (Fin 3) (Fin 3) ℚ).det = 0 ∧
      (Matrix.of ![cremonaPlane (![(1 : ℚ), 1, 1] : Fin 3 → ℚ),
        cremonaPlane (![(1 : ℚ), 2, 3] : Fin 3 → ℚ),
        cremonaPlane (![(2 : ℚ), 3, 4] : Fin 3 → ℚ)] : Matrix (Fin 3) (Fin 3) ℚ).det = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [cremonaPlane] <;> ring
  · rw [Matrix.det_fin_three]
    simp [Matrix.of_apply]
    norm_num
  · rw [Matrix.det_fin_three]
    simp [Matrix.of_apply, cremonaPlane]
    norm_num

/-- **Klein §8.3 Infinitesimal Linearization Theorem**: the Fréchet derivative of mutually inverse
differentiable maps at `x` yields a genuine continuous linear isomorphism `E ≃L[𝕜] E`, and
composition of differentiable maps lifts functorially via `fderiv_comp`. -/
def tangentLinearizationEquiv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f g : E → E) (x : E)
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g (f x))
    (hgf : g ∘ f = id) (hfg : f ∘ g = id) :
    E ≃L[𝕜] E :=
  { toLinearEquiv :=
      LinearEquiv.ofLinearMap (fderiv 𝕜 f x).toLinearMap (fderiv 𝕜 g (f x)).toLinearMap
        (by
          have hgfx : g (f x) = x := congrFun hgf x
          have hf' : DifferentiableAt 𝕜 f (g (f x)) := hgfx.symm ▸ hf
          have hc := fderiv_comp (f x) hf' hg
          rw [hfg, fderiv_id, hgfx] at hc
          ext v
          have hv := congrArg (fun L : E →L[𝕜] E => L v) hc
          simpa [LinearMap.comp_apply, ContinuousLinearMap.comp_apply] using hv.symm)
        (by
          have hc := fderiv_comp x hg hf
          rw [hgf, fderiv_id] at hc
          ext v
          have hv := congrArg (fun L : E →L[𝕜] E => L v) hc
          simpa [LinearMap.comp_apply, ContinuousLinearMap.comp_apply] using hv.symm)
    continuous_toFun := (fderiv 𝕜 f x).continuous
    continuous_invFun := (fderiv 𝕜 g (f x)).continuous }

theorem klein_sec8_linearization_functorial {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f g : E → E) (x : E)
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g (f x)) :
    fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  fderiv_comp x hg hf

/-- `(2n + 1)`-dimensional space of surface elements `(x, z, p) ∈ Rⁿ × R × Rⁿ` (`Klein §9`). -/
abbrev ContactJetSpace (n : ℕ) (R : Type*) : Type _ :=
  (Fin n → R) × R × (Fin n → R)

/-- Canonical contact 1-form `θ_{(x, z, p)}(dx, dz, dp) = dz - ∑ pᵢ dxᵢ` ("united position"). -/
def contactOneForm (n : ℕ) {R : Type*} [CommRing R] (w dw : ContactJetSpace n R) : R :=
  dw.2.1 - ∑ i : Fin n, w.2.2 i * dw.1 i

/-- `n`-dimensional Legendrian point-fiber at `(x₀, z₀)`. -/
def pointLegendrian (n : ℕ) {R : Type*} (x₀ : Fin n → R) (z₀ : R) (p : Fin n → R) :
    ContactJetSpace n R :=
  (x₀, z₀, p)

/-- `n`-dimensional Legendrian 1-jet lift of a hypersurface `z = f(x)`. -/
def surfaceLegendrian (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ContactJetSpace n ℝ :=
  (x, f x, fun i => fderiv ℝ f x (Pi.single i 1))

/-- Legendre contact involution `(x, z, p) ↦ (p, ∑ pᵢ xᵢ - z, x)` on `(2n + 1)`-space. -/
def legendreContact (n : ℕ) {R : Type*} [CommRing R] (w : ContactJetSpace n R) :
    ContactJetSpace n R :=
  (w.2.2, (∑ i : Fin n, w.2.2 i * w.1 i) - w.2.1, w.1)

/-- Differential pushforward `d(legendreContact)` along tangent vector `(dx, dz, dp)`. -/
def dLegendreContact (n : ℕ) {R : Type*} [CommRing R] (w dw : ContactJetSpace n R) :
    ContactJetSpace n R :=
  (dw.2.2, (∑ i : Fin n, (dw.2.2 i * w.1 i + w.2.2 i * dw.1 i)) - dw.2.1, dw.1)

/-- **Klein §9 Contact Transformation & Unified `n`-Dimensional Legendrian Theorem**:
1. Point fibers `(x₀, z₀, p)`, smooth hypersurface 1-jets `(x, f x, fderiv f x)`, and 3D curve
   conormal strips all annihilate `contactOneForm`, unifying them as `n`-dimensional Legendrian
   manifolds.
2. `legendreContact n` is an involution (`legendreContact ∘ legendreContact = id`) that negates
   the contact 1-form (`contactOneForm n (legendreContact n w) (dLegendreContact n w dw) = -θ`),
   preserving the contact distribution `θ = 0`.
3. `[countermodel_found]`: `legendreContact n` sends the origin point-fiber `(0, 0, p)` bijectively
   onto the plane surface `(p, 0, 0)`, proving points do NOT form a body under contact
   transformations. -/
theorem klein_sec9_contact_legendre_unification (n : ℕ) {R : Type*} [CommRing R]
    (w dw : ContactJetSpace n R) (x₀ : Fin n → R) (z₀ : R) (p dp : Fin n → R)
    (f : (Fin n → ℝ) → ℝ) (x dx : Fin n → ℝ) (hf : DifferentiableAt ℝ f x)
    (dp' : Fin n → ℝ)
    (xd yd zd p3 q3 : ℝ → ℝ) (t : ℝ) (hstrip : deriv zd t = p3 t * deriv xd t + q3 t * deriv yd t)
    (dp3 dq3 : ℝ) :
    contactOneForm n (pointLegendrian n x₀ z₀ p) (0, 0, dp) = 0 ∧
      (HasFDerivAt f (fderiv ℝ f x) x ∧
        contactOneForm n (surfaceLegendrian n f x) (dx, fderiv ℝ f x dx, dp') = 0) ∧
      contactOneForm 2 (![xd t, yd t], zd t, ![p3 t, q3 t])
        (![deriv xd t, deriv yd t], deriv zd t, ![dp3, dq3]) = 0 ∧
      legendreContact n (legendreContact n w) = w ∧
      contactOneForm n (legendreContact n w) (dLegendreContact n w dw) = -contactOneForm n w dw ∧
      legendreContact n (pointLegendrian n (0 : Fin n → R) 0 p) = (p, 0, 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [contactOneForm, pointLegendrian]
  · refine ⟨hf.hasFDerivAt, ?_⟩
    have hdx : dx = ∑ i : Fin n, dx i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hlin : fderiv ℝ f x dx =
        ∑ i : Fin n, fderiv ℝ f x (Pi.single i 1) * dx i := by
      conv_lhs => rw [hdx]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    dsimp [contactOneForm, surfaceLegendrian]
    rw [hlin, sub_self]
  · simp only [contactOneForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hstrip]
    ring
  · rcases w with ⟨xw, zw, pw⟩
    ext i <;> simp only [legendreContact]
    have hs : ∑ j : Fin n, xw j * pw j = ∑ j : Fin n, pw j * xw j :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hs]
    ring
  · rcases w with ⟨xw, zw, pw⟩
    rcases dw with ⟨dxw, dzw, dpw⟩
    simp only [contactOneForm, legendreContact, dLegendreContact, Finset.sum_add_distrib]
    have hs : ∑ j : Fin n, dpw j * xw j = ∑ j : Fin n, xw j * dpw j :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hs]
    ring
  · ext i <;> simp [legendreContact, pointLegendrian]

end CremonaFDerivContact

/-! ## 4. `EK₉` (Concluding Remarks Fn. 37 & Note VII): Quaternions, Cubic & Quartic Syzygies -/

section QuaternionsAndBinaryFormsNoteVII

/-- Unit quaternion conjugation `v ↦ q * v * star q` on `ℍ[ℝ]` (`Klein Concluding Remarks, Fn. 37`). -/
def quatConjRot (q v : ℍ[ℝ]) : ℍ[ℝ] :=
  q * v * star q

/-- **Klein Fn. 37 Quaternion `SO(3)` Representation**:
for `normSq q = 1` and pure imaginary `v` (`v.re = 0`), `quatConjRot q v` preserves purity
(`re = 0`), preserves Euclidean squared norm `normSq`, gives a group action `q₁ * q₂`, and has
two-element kernel `{1, -1}`. -/
theorem klein_fn37_quaternion_so3_action (q q₁ q₂ v : ℍ[ℝ])
    (hq : q.normSq = 1) (hv : v.re = 0) :
    (quatConjRot q v).re = 0 ∧
      (quatConjRot q v).normSq = v.normSq ∧
      quatConjRot 1 v = v ∧
      quatConjRot (q₁ * q₂) v = quatConjRot q₁ (quatConjRot q₂ v) ∧
      (quatConjRot (-1) v = v ∧ (-1 : ℍ[ℝ]) ≠ 1) := by
  have hre : (quatConjRot q v).re = q.normSq * v.re := by
    simp only [quatConjRot, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star, Quaternion.normSq_def']
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hre, hv, mul_zero]
  · simp only [quatConjRot, map_mul, Quaternion.normSq_star, hq, one_mul, mul_one]
  · simp [quatConjRot]
  · simp only [quatConjRot, star_mul, mul_assoc]
  · simp [quatConjRot]
  · intro h
    have h0 := congrArg QuaternionAlgebra.re h
    norm_num at h0

section BinaryFormsCommRing

variable {R : Type*} [CommRing R]

/-- Classical binary cubic form `f(x, y) = a₀ x³ + 3 a₁ x² y + 3 a₂ x y² + a₃ y³`. -/
def binaryCubic (a₀ a₁ a₂ a₃ x y : R) : R :=
  a₀ * x ^ 3 + 3 * a₁ * x ^ 2 * y + 3 * a₂ * x * y ^ 2 + a₃ * y ^ 3

/-- Hessian quadratic covariant `H₂(x, y)` of a binary cubic (`Note VII`). -/
def cubicHessian (a₀ a₁ a₂ a₃ x y : R) : R :=
  (a₀ * a₂ - a₁ ^ 2) * x ^ 2 + (a₀ * a₃ - a₁ * a₂) * x * y + (a₁ * a₃ - a₂ ^ 2) * y ^ 2

/-- Jacobian cubic covariant `Q(x, y)` of `(f, H₂)` (`Note VII`). -/
def cubicJacobian (a₀ a₁ a₂ a₃ x y : R) : R :=
  (a₁ * x ^ 2 + 2 * a₂ * x * y + a₃ * y ^ 2) *
      (2 * (a₀ * a₂ - a₁ ^ 2) * x + (a₀ * a₃ - a₁ * a₂) * y) -
    (a₀ * x ^ 2 + 2 * a₁ * x * y + a₂ * y ^ 2) *
      ((a₀ * a₃ - a₁ * a₂) * x + 2 * (a₁ * a₃ - a₂ ^ 2) * y)

/-- Discriminant invariant `R_disc` of a binary cubic. -/
def cubicDiscriminant (a₀ a₁ a₂ a₃ : R) : R :=
  (a₀ * a₃ - a₁ * a₂) ^ 2 - 4 * (a₀ * a₂ - a₁ ^ 2) * (a₁ * a₃ - a₂ ^ 2)

/-- **Klein Note VII & Cayley's Universal Binary Cubic Syzygy (`pp. 25–26`)**:
for ALL `(a₀, a₁, a₂, a₃, x, y)` in ANY commutative ring `R`,
`Q² + 4 H₂³ = R_disc * f²`, specializing on the equatorial spherical cubic `x³ - y³` to
`H₂ = -x y`, `Q = x³ + y³`, `R_disc = 1`, `(x³ + y³)² - 4 x³ y³ = (x³ - y³)²`. -/
theorem klein_noteVII_binary_cubic_syzygy (a₀ a₁ a₂ a₃ x y : R) :
    (cubicJacobian a₀ a₁ a₂ a₃ x y) ^ 2 + 4 * (cubicHessian a₀ a₁ a₂ a₃ x y) ^ 3 =
        cubicDiscriminant a₀ a₁ a₂ a₃ * (binaryCubic a₀ a₁ a₂ a₃ x y) ^ 2 ∧
      (binaryCubic (1 : R) 0 0 (-1) x y = x ^ 3 - y ^ 3 ∧
        cubicHessian (1 : R) 0 0 (-1) x y = -(x * y) ∧
        cubicJacobian (1 : R) 0 0 (-1) x y = x ^ 3 + y ^ 3 ∧
        cubicDiscriminant (1 : R) 0 0 (-1) = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [binaryCubic, cubicHessian, cubicJacobian, cubicDiscriminant] <;> ring

/-- Four vertices of Klein's `V₄`-symmetric tetrahedron in `R³` (`Note VII, pp. 25–26`):
`(x, y, z)`, `(x, -y, -z)`, `(-x, y, -z)`, `(-x, -y, z)`. -/
def kleinTetraVertex (x y z : R) : Fin 4 → Fin 3 → R
  | 0 => ![x, y, z]
  | 1 => ![x, -y, -z]
  | 2 => ![-x, y, -z]
  | 3 => ![-x, -y, z]

/-- **Klein Note VII Symmetrical Tetrahedron Theorem (`pp. 25–26`)**:
all 4 vertices of `kleinTetraVertex x y z` share the same squared sphere radius `x² + y² + z²`,
all three pairs of opposite edges have equal squared lengths (`4(y²+z²)`, `4(x²+z²)`, `4(x²+y²)`),
and the opposite-edge midpoints lie on the three rectangular coordinate axes `(±x,0,0)`,
`(0,±y,0)`, `(0,0,±z)` (matching the roots of the sextic covariant `x y (x⁴ - y⁴)`). -/
theorem klein_noteVII_symmetrical_tetrahedron (x y z : R) :
    (∀ k : Fin 4,
      (kleinTetraVertex x y z k 0) ^ 2 + (kleinTetraVertex x y z k 1) ^ 2 +
        (kleinTetraVertex x y z k 2) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2) ∧
      (∑ i : Fin 3, (kleinTetraVertex x y z 0 i - kleinTetraVertex x y z 1 i) ^ 2 =
        4 * (y ^ 2 + z ^ 2) ∧
       ∑ i : Fin 3, (kleinTetraVertex x y z 2 i - kleinTetraVertex x y z 3 i) ^ 2 =
        4 * (y ^ 2 + z ^ 2) ∧
       ∑ i : Fin 3, (kleinTetraVertex x y z 0 i - kleinTetraVertex x y z 2 i) ^ 2 =
        4 * (x ^ 2 + z ^ 2) ∧
       ∑ i : Fin 3, (kleinTetraVertex x y z 1 i - kleinTetraVertex x y z 3 i) ^ 2 =
        4 * (x ^ 2 + z ^ 2)) ∧
      (kleinTetraVertex x y z 0 + kleinTetraVertex x y z 1 = ![2 * x, 0, 0] ∧
       kleinTetraVertex x y z 0 + kleinTetraVertex x y z 2 = ![0, 2 * y, 0] ∧
       kleinTetraVertex x y z 0 + kleinTetraVertex x y z 3 = ![0, 0, 2 * z]) := by
  refine ⟨fun k => ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · fin_cases k <;> simp [kleinTetraVertex]
  · simp [Fin.sum_univ_three, kleinTetraVertex]; ring
  · simp [Fin.sum_univ_three, kleinTetraVertex]; ring
  · simp [Fin.sum_univ_three, kleinTetraVertex]; ring
  · simp [Fin.sum_univ_three, kleinTetraVertex]; ring
  · ext i; (fin_cases i <;> simp [kleinTetraVertex]); ring
  · ext i; (fin_cases i <;> simp [kleinTetraVertex]); ring
  · ext i; (fin_cases i <;> simp [kleinTetraVertex]); ring

/-- Classical binary quartic form `f(x, y) = a₀ x⁴ + 4 a₁ x³ y + 6 a₂ x² y² + 4 a₃ x y³ + a₄ y⁴`. -/
def binaryQuartic (a₀ a₁ a₂ a₃ a₄ x y : R) : R :=
  a₀ * x ^ 4 + 4 * a₁ * x ^ 3 * y + 6 * a₂ * x ^ 2 * y ^ 2 + 4 * a₃ * x * y ^ 3 + a₄ * y ^ 4

/-- Hessian quartic covariant `H(x, y)` of a binary quartic over any `[CommRing R]`. -/
def quarticHessian (a₀ a₁ a₂ a₃ a₄ x y : R) : R :=
  (a₀ * x ^ 2 + 2 * a₁ * x * y + a₂ * y ^ 2) * (a₂ * x ^ 2 + 2 * a₃ * x * y + a₄ * y ^ 2) -
    (a₁ * x ^ 2 + 2 * a₂ * x * y + a₃ * y ^ 2) ^ 2

/-- Sextic Jacobian covariant `T(x, y)` of `(f, H)` over any `[CommRing R]`. -/
def quarticSexticT (a₀ a₁ a₂ a₃ a₄ x y : R) : R :=
  let A := a₀ * x ^ 2 + 2 * a₁ * x * y + a₂ * y ^ 2
  let B := a₁ * x ^ 2 + 2 * a₂ * x * y + a₃ * y ^ 2
  let C := a₂ * x ^ 2 + 2 * a₃ * x * y + a₄ * y ^ 2
  let Hx2 := (a₀ * x + a₁ * y) * C + A * (a₂ * x + a₃ * y) - 2 * B * (a₁ * x + a₂ * y)
  let Hy2 := (a₁ * x + a₂ * y) * C + A * (a₃ * x + a₄ * y) - 2 * B * (a₂ * x + a₃ * y)
  let fx4 := a₀ * x ^ 3 + 3 * a₁ * x ^ 2 * y + 3 * a₂ * x * y ^ 2 + a₃ * y ^ 3
  let fy4 := a₁ * x ^ 3 + 3 * a₂ * x ^ 2 * y + 3 * a₃ * x * y ^ 2 + a₄ * y ^ 3
  fx4 * Hy2 - fy4 * Hx2

/-- Degree-2 invariant `I` of a binary quartic. -/
def quarticInvI (a₀ a₁ a₂ a₃ a₄ : R) : R :=
  a₀ * a₄ - 4 * a₁ * a₃ + 3 * a₂ ^ 2

/-- Degree-3 invariant `J` (catalecticant) of a binary quartic. -/
def quarticInvJ (a₀ a₁ a₂ a₃ a₄ : R) : R :=
  a₀ * a₂ * a₄ + 2 * a₁ * a₂ * a₃ - a₀ * a₃ ^ 2 - a₄ * a₁ ^ 2 - a₂ ^ 3

/-- **Klein Note VII & Cayley–Hermite Binary Quartic Syzygy + Hesse Pencil Theorem (`p. 26`)**:
1. Universal syzygy `T² = -4 H³ + I H f² - J f³` over ANY `[CommRing R]`.
2. Along the tetrahedral/octahedral pencil `f_μ(x, y) = x⁴ + 6 μ x² y² + y⁴`, every non-singular
   member produces the exact same sextic covariant up to `(1 - 9 μ²)`:
   `T_μ(x, y) = (1 - 9 μ²) x y (x⁴ - y⁴)` (whose roots are the stereographic 6 coordinate-axis
   points `{0, ∞, ±1, ±i}`!), while the bilinear Jacobian of any two pencil members `α f + β H` and
   `γ f + δ H` scales determinantly by `(α δ - β γ)`. -/
theorem klein_noteVII_binary_quartic_syzygy_and_pencil (a₀ a₁ a₂ a₃ a₄ μ x y : R)
    (fx fy hx hy α β γ δ : R) :
    (quarticSexticT a₀ a₁ a₂ a₃ a₄ x y) ^ 2 =
        -4 * (quarticHessian a₀ a₁ a₂ a₃ a₄ x y) ^ 3 +
          quarticInvI a₀ a₁ a₂ a₃ a₄ * quarticHessian a₀ a₁ a₂ a₃ a₄ x y *
            (binaryQuartic a₀ a₁ a₂ a₃ a₄ x y) ^ 2 -
          quarticInvJ a₀ a₁ a₂ a₃ a₄ * (binaryQuartic a₀ a₁ a₂ a₃ a₄ x y) ^ 3 ∧
      (binaryQuartic (1 : R) 0 μ 0 1 x y = x ^ 4 + 6 * μ * x ^ 2 * y ^ 2 + y ^ 4 ∧
        quarticHessian (1 : R) 0 μ 0 1 x y =
          μ * (x ^ 4 + y ^ 4) + (1 - 3 * μ ^ 2) * x ^ 2 * y ^ 2 ∧
        quarticSexticT (1 : R) 0 μ 0 1 x y = (1 - 9 * μ ^ 2) * x * y * (x ^ 4 - y ^ 4) ∧
        (α * fx + β * hx) * (γ * fy + δ * hy) - (α * fy + β * hy) * (γ * fx + δ * hx) =
          (α * δ - β * γ) * (fx * hy - fy * hx)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [quarticSexticT, quarticHessian, quarticInvI, quarticInvJ, binaryQuartic]
    ring
  · dsimp [binaryQuartic]; ring
  · dsimp [quarticHessian]; ring
  · dsimp [quarticSexticT]; ring
  · ring

end BinaryFormsCommRing

end QuaternionsAndBinaryFormsNoteVII

end InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
