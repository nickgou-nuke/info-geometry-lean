/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

/-!
# Voigt conformal factor (Pauli 1921 §1 fn. 12 / §4 / §24)

Exact `Mat₄` congruence layer for the real form `η = diag(1,1,1,−1)`
(Pauli §4 Eq. (2), time slot last; null cone `x0²+x1²+x2²−x3² = 0`),
certified against the strict word model
`proofs/voigt_conformal_factor.py` (8/8 checks):

* Voigt 1887 boost (transverse scaling `r`, parallel slide `−b`): conformed,
  not isometric
  `(voigt b r)ᵀ * eta * (voigt b r) = (1 − b²) • eta` — Pauli §1 fn. 12.
* Lorentz boost: isometric
  `(boost b g)ᵀ * eta * (boost b g) = eta` under `g * r = 1`, `r² + b² = 1`
  (Pauli §4 Eqs. (I)/(II) with Eq. (8)).
* `boost b g = g • voigt b r` — Voigt = boost minus the overall dilation
  (verbatim remark of Pauli fn. 12).
* `voigt b r * voigt (−b) r = (1 − b²) • 1` — the unresolved `κ(b)κ(−b)`
  round trip (Pauli §4, pp. 554–555), closed to `1` only after the
  Einstein/Poincaré scale normalization `κ(v) = 1`.
* Spatial swap `x₀ ↔ x₁` and time flip `x₃ ↦ −x₃` stay `η`-isometries
  (Pauli §24 reflection family).

No physics interpretation is asserted beyond these finitely checked
congruences; no tangent, covector, or differential-operator layer exists here.
-/

noncomputable section

namespace InfoGeometry.Physics.VoigtConformalFactor

open Finset
open scoped Matrix

variable {R : Type*} [Ring R]

/-- The Minkowski form `η = diag(1,1,1,−1)` (Pauli §4 Eq. (2), time slot last). -/
def eta : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- Voigt 1887 boost: transverse coordinates divided by `r`, parallel slide
`−b`, unit time-normal block (Pauli §1 fn. 12). -/
def voigt (b r : R) : Matrix (Fin 4) (Fin 4) R :=
  !![r, 0, 0, 0; 0, r, 0, 0; 0, 0, 1, -b; 0, 0, -b, 1]

/-- Lorentz boost with dilation `g` and slide `b` (Pauli §4 Eq. (I)). -/
def boost (b g : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, g, -g * b; 0, 0, -g * b, g]

/-- Spatial axis swap `x₀ ↔ x₁`. -/
def spatialSwap : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- Time flip `x₃ ↦ −x₃`. -/
def timeFlip : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- Directed matrix units in the same four-dimensional carrier as the Lorentz
operators. -/
def operatorUnit01 : Matrix (Fin 4) (Fin 4) R := Matrix.single 0 1 (1 : R)

def operatorUnit10 : Matrix (Fin 4) (Fin 4) R := Matrix.single 1 0 (1 : R)

/-- The four-dimensional matrix carrier is genuinely noncommutative over any
nontrivial coefficient ring: the two directed units multiply to distinct
diagonal units. -/
theorem matrixCarrier_noncommutative [Nontrivial R] :
    operatorUnit01 (R := R) * operatorUnit10 (R := R) ≠
      operatorUnit10 (R := R) * operatorUnit01 (R := R) := by
  intro h
  simp only [operatorUnit01, operatorUnit10] at h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) R => M 0 0) h
  have hOne : (1 : R) = 0 := by simpa [Matrix.single] using h00
  exact one_ne_zero hOne

/-- A `Fin 4` sum splits into four summands. -/
theorem sum_fin4 {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) :
    (∑ k : Fin 4, f k) = f 0 + f 1 + f 2 + f 3 := by
  simp [Fin.sum_univ_succ]
  abel

/-- **Voigt conformality** (Pauli §1 fn. 12): the transverse-scaled boost is
conformal with factor `1 − b²` — light-cone preserving, but not an isometry. -/
theorem voigt_conformal (b r : R) (hr : r * r + b * b = 1) :
    (voigt b r)ᵀ * eta * voigt b r = (1 - b * b) • eta := by
  have hbm : r * r = 1 - b * b := eq_sub_iff_add_eq.mpr hr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sum_fin4, eta, voigt, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul, hbm] <;> noncomm_ring

/-- **Voigt = boost minus the dilation** (verbatim Pauli fn. 12 remark). -/
theorem boost_eq_smul_voigt (b g r : R) (hg : g * r = 1) :
    boost b g = g • voigt b r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost, voigt, Matrix.smul_apply, smul_eq_mul, hg]

/-- **Boost isometry** (Pauli §4 Eqs. (I)/(II) with Eq. (8)). -/
theorem boost_isometric {R : Type*} [CommRing R] (b g r : R) (hr : r * r + b * b = 1) (hg : g * r = 1) :
    (boost b g)ᵀ * eta * boost b g = eta := by
  have hgg : g * g * (r * r) = 1 := by
    have h1 : (g * r) * (g * r) = 1 := by simp only [hg, one_mul]
    calc g * g * (r * r) = (g * r) * (g * r) := by ring
      _ = 1 := h1
  have hb : 1 - b * b = r * r := by rw [← hr, add_sub_cancel_right]
  rw [boost_eq_smul_voigt b g r hg, Matrix.transpose_smul, Matrix.smul_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [voigt_conformal b r hr, hb, smul_smul, hgg, one_smul]

/-- Spatial swap is an `η`-isometry. -/
theorem spatial_swap_isometry :
    spatialSwapᵀ * eta * spatialSwap = (eta : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sum_fin4, eta, spatialSwap, Matrix.transpose_apply, Matrix.mul_apply]

/-- Time flip is an `η`-isometry. -/
theorem time_flip_isometry :
    timeFlipᵀ * eta * timeFlip = (eta : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sum_fin4, eta, timeFlip, Matrix.transpose_apply, Matrix.mul_apply]

/-- **Voigt round trip is the unresolved `κ` product** (Pauli §4, pp. 554–555,
at the conformal level): `κ(b)κ(−b) = 1 − b²`, resolved to `1` only under the
Einstein/Poincaré scale normalization. -/
theorem voigt_roundtrip_conformal (b r : R) (hr : r * r + b * b = 1) :
    voigt b r * voigt (-b) r = (1 - b * b) • (1 : Matrix (Fin 4) (Fin 4) R) := by
  have hbm : r * r = 1 - b * b := eq_sub_iff_add_eq.mpr hr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sum_fin4, voigt, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      hbm] <;> noncomm_ring

/-- Resolved boost round trip (the closed `κ(b)κ(−b) = 1` group identity). -/
theorem boost_roundtrip {R : Type*} [CommRing R] (b g r : R) (hr : r * r + b * b = 1) (hg : g * r = 1) :
    boost b g * boost (-b) g = (1 : Matrix (Fin 4) (Fin 4) R) := by
  have hgg : g * g * (r * r) = 1 := by
    have h1 : (g * r) * (g * r) = 1 := by simp only [hg, one_mul]
    calc g * g * (r * r) = (g * r) * (g * r) := by ring
      _ = 1 := h1
  have hb : 1 - b * b = r * r := by rw [← hr, add_sub_cancel_right]
  rw [boost_eq_smul_voigt b g r hg, boost_eq_smul_voigt (-b) g r hg,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [voigt_roundtrip_conformal b r hr, smul_smul, hb, hgg, one_smul]

end InfoGeometry.Physics.VoigtConformalFactor
