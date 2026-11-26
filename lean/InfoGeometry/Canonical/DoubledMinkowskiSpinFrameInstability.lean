/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Singlet/Triplet Rotating Spin-Frame Instabilities in the Doubled Minkowski Vacuum

Extends `InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge` by formalizing the algebraic
and spectral instability mechanisms distinguishing **singlet (`S = 0`)** and **triplet (`S = 1`)**
states under rotating local spin frames in the doubled Minkowski `(4,4)` Krein carrier:

1. **Spin-1/2 × Spin-1/2 (`Fin 2 × Fin 2 → ℂ`) Singlet/Triplet Decomposition & Local Rotation**:
   Explicit orthogonal projectors `projSinglet` (`tr = 1`) and `projTriplet` (`tr = 3`),
   Casimir identity `S² = 2 P_triplet`, annihilation of the singlet vector by all `su(2)` generators
   `(S_x, S_y, S_z)` and finite local spin-frame rotations `twoSpinRotZ θ`, contrasted with phase
   precession `exp (± i θ)` of the `m_S = ±1` triplet modes.
2. **Rotating-Frame BdG Hamiltonian: Singlet Gap Stability vs. Triplet Coriolis Instability**:
   Under local spin-frame rotation `- Ω S_z`, every doubled singlet state `a • singlet ⊕ b • singlet`
   is strictly immune to `Ω` and retains the uniform spectral gap `(ξ₀² + m²) ≥ m²`, whereas the
   triplet quasiparticle branches split to `√(ξ₀² + m²) ∓ Ω`. At `ξ₀ = 0, m > 0`, the upper branch
   closes its gap at `Ω = m` and becomes strictly negative (`m - Ω < 0`) for `Ω > m`.
3. **Non-Unitary Triplet Pairing (`d × d* ≠ 0`) Band Splitting & Chiral Gap Collapse**:
   Derives the exact identity `Δ Δᴴ = ‖d‖² I₂ + i (d × d*) · σ`, showing vanishing splitting for
   real unitary `d`-vectors and exhibiting a non-unitary chiral triplet `d = (m, i m, 0)` with
   `‖d‖² = 2 m² > 0` whose `4 × 4` BdG Hamiltonian admits an exact zero mode (`gap collapse`).
4. **Doubled Minkowski Krein-Metric Collision & Hyperbolic Sheet-Boost Instability**:
   In the signature-`(4,4)` doubled Minkowski carrier `(Fin 2 × Fin 4 → ℝ, 𝒦_diag = Z ⊗ η_{1,3})`
   and counter-rotating spin-frame carrier `(Fin 2 × Fin 2 → ℝ, K = Z ⊗ I₂)`, `K`-skew-symmetric
   couplings can collide across opposite-Krein-sign sheets: passing from bounded elliptic precession
   (`|g| < |Ω|`) through a non-diagonalizable Jordan nilpotent threshold (`|g| = |Ω|`) to an
   exponentially growing Krein-collision runaway mode `exp(γ t)` (`|g| > |Ω|`, `γ = √(g² - Ω²)`).

## Audit Summary

#### BUCKET 1: CONSTRUCTIVE PROOFS IN THIS OWNER MODULE
* `singlet_triplet_decomposition_and_rotation`
* `rotating_bdg_singlet_stability_vs_triplet_instability`
* `triplet_coriolis_gap_closure_and_instability`
* `nonunitary_triplet_band_splitting_and_gap_collapse`
* `doubled_minkowski_sheet_boost_instability`
* `krein_collision_phase_transition`
* Explicit matrix non-commutativity witnesses on `Fin 2`, `Fin 2 × Fin 2`, `Fin 2 × Fin 4`,
  `Fin 2 ⊕ Fin 2`, and `(Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)`.

#### BUCKET 2: IMPORTED OWNER BOUNDARIES
* `InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge`: reuses `minkowski4`, `zCut2`,
  `xMir2`, and `doubledMinkowskiDiag`.

#### BUCKET 3: OPEN CLOSURE DEBT
* Full continuum QFT vacuum decay rates across rotating relativistic light cylinders
  (`r_⊥ = c / |Ω|`) and interacting 4D non-Abelian gauge path-integral fluctuations remain
  outside finite-dimensional matrix stability analysis.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open scoped Kronecker
open Matrix Complex
open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge

namespace InfoGeometry.Canonical.DoubledMinkowskiSpinFrameInstability

/-! ### Scalar Algebraic Helpers (Zero Matrix Dependence for Policy Cleanliness) -/

private lemma scalar_rot_z_phase (θ : ℝ) :
    Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ)) = 1 := by
  rw [← Complex.exp_add]
  have h : Complex.I * ((θ / 2 : ℝ) : ℂ) + -Complex.I * ((θ / 2 : ℝ) : ℂ) = 0 := by ring
  rw [h, Complex.exp_zero]

private lemma scalar_rot_z_sq (θ : ℝ) :
    Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (θ : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma scalar_rot_z_neg_sq (θ : ℝ) :
    Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * (θ : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma scalar_singlet_normsq (ξ₀ m : ℝ) (a b : ℂ) :
    Complex.normSq (((ξ₀ : ℂ) * a + (m : ℂ) * b)) +
        Complex.normSq (((ξ₀ : ℂ) * a + (m : ℂ) * b) * (-1)) +
        (Complex.normSq (((m : ℂ) * a - (ξ₀ : ℂ) * b)) +
          Complex.normSq (((m : ℂ) * a - (ξ₀ : ℂ) * b) * (-1))) =
      (ξ₀ ^ 2 + m ^ 2) * (2 * (Complex.normSq a + Complex.normSq b)) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
  ring

private lemma scalar_bdg_eig_top (ξ₀ m Ω : ℝ) :
    let E : ℝ := Real.sqrt (ξ₀ ^ 2 + m ^ 2)
    ((ξ₀ : ℂ) - (Ω : ℂ)) * ((ξ₀ + E : ℝ) : ℂ) + (m : ℂ) * (m : ℂ) =
      ((E - Ω : ℝ) : ℂ) * ((ξ₀ + E : ℝ) : ℂ) := by
  intro E
  have hEsq : E ^ 2 = ξ₀ ^ 2 + m ^ 2 := Real.sq_sqrt (by positivity)
  have hreal : (ξ₀ - Ω) * (ξ₀ + E) + m * m = (E - Ω) * (ξ₀ + E) := by
    nlinarith [hEsq]
  exact_mod_cast hreal

private lemma scalar_bdg_eig_bot (ξ₀ m Ω : ℝ) :
    let E : ℝ := Real.sqrt (ξ₀ ^ 2 + m ^ 2)
    (m : ℂ) * ((ξ₀ + E : ℝ) : ℂ) + ((-(ξ₀ : ℂ)) - (Ω : ℂ)) * (m : ℂ) =
      ((E - Ω : ℝ) : ℂ) * (m : ℂ) := by
  intro E
  have hreal : m * (ξ₀ + E) + (-ξ₀ - Ω) * m = (E - Ω) * m := by ring
  exact_mod_cast hreal

private lemma scalar_bdg_minus_top (ξ₀ m Ω : ℝ) :
    let E : ℝ := Real.sqrt (ξ₀ ^ 2 + m ^ 2)
    ((ξ₀ : ℂ) + (Ω : ℂ)) * ((ξ₀ + E : ℝ) : ℂ) + (m : ℂ) * (m : ℂ) =
      ((E + Ω : ℝ) : ℂ) * ((ξ₀ + E : ℝ) : ℂ) := by
  simpa [sub_neg_eq_add] using scalar_bdg_eig_top ξ₀ m (-Ω)

private lemma scalar_bdg_minus_bot (ξ₀ m Ω : ℝ) :
    let E : ℝ := Real.sqrt (ξ₀ ^ 2 + m ^ 2)
    (m : ℂ) * ((ξ₀ + E : ℝ) : ℂ) + ((-(ξ₀ : ℂ)) + (Ω : ℂ)) * (m : ℂ) =
      ((E + Ω : ℝ) : ℂ) * (m : ℂ) := by
  simpa [sub_neg_eq_add] using scalar_bdg_eig_bot ξ₀ m (-Ω)

private lemma scalar_singlet_sq_top (ξ₀ m : ℝ) (a b : ℂ) :
    (ξ₀ : ℂ) * ((ξ₀ : ℂ) * a + (m : ℂ) * b) + (m : ℂ) * ((m : ℂ) * a - (ξ₀ : ℂ) * b) =
      ((ξ₀ ^ 2 + m ^ 2 : ℝ) : ℂ) * a := by
  push_cast
  ring

private lemma scalar_singlet_sq_bot (ξ₀ m : ℝ) (a b : ℂ) :
    (m : ℂ) * ((ξ₀ : ℂ) * a + (m : ℂ) * b) + (-(ξ₀ : ℂ)) * ((m : ℂ) * a - (ξ₀ : ℂ) * b) =
      ((ξ₀ ^ 2 + m ^ 2 : ℝ) : ℂ) * b := by
  push_cast
  ring

private lemma scalar_singlet_vec_top (ξ m a b s : ℂ) :
    a * (ξ * s) + b * (m * s) = (ξ * a + m * b) * s := by
  ring

private lemma scalar_singlet_vec_bot (ξ m a b s : ℂ) :
    a * (m * s) + b * (-ξ * s) = (m * a - ξ * b) * s := by
  ring

private lemma scalar_singlet_sq_top_vec (ξ₀ m : ℝ) (a b s : ℂ) :
    ((ξ₀ : ℂ) * a + (m : ℂ) * b) * ((ξ₀ : ℂ) * s) +
        ((m : ℂ) * a - (ξ₀ : ℂ) * b) * ((m : ℂ) * s) =
      ((ξ₀ ^ 2 + m ^ 2 : ℝ) : ℂ) * (a * s) := by
  push_cast
  ring

private lemma scalar_singlet_sq_bot_vec (ξ₀ m : ℝ) (a b s : ℂ) :
    ((ξ₀ : ℂ) * a + (m : ℂ) * b) * ((m : ℂ) * s) +
        ((m : ℂ) * a - (ξ₀ : ℂ) * b) * ((-(ξ₀ : ℂ)) * s) =
      ((ξ₀ ^ 2 + m ^ 2 : ℝ) : ℂ) * (b * s) := by
  push_cast
  ring

private lemma scalar_bdg_plus_top_vec (ξ₀ m Ω : ℝ) (s : ℂ) :
    let E : ℝ := Real.sqrt (ξ₀ ^ 2 + m ^ 2)
    (((ξ₀ + E : ℝ) : ℂ)) * ((ξ₀ : ℂ) * s - (Ω : ℂ) * s) + (m : ℂ) * ((m : ℂ) * s) =
      ((E - Ω : ℝ) : ℂ) * ((((ξ₀ + E : ℝ) : ℂ)) * s) := by
  intro E
  have h := scalar_bdg_eig_top ξ₀ m Ω
  dsimp at h
  linear_combination h * s

private lemma scalar_bdg_plus_bot_vec (ξ₀ m Ω : ℝ) (s : ℂ) :
    let E : ℝ := Real.sqrt (ξ₀ ^ 2 + m ^ 2)
    (((ξ₀ + E : ℝ) : ℂ)) * ((m : ℂ) * s) + (m : ℂ) * ((-(ξ₀ : ℂ)) * s - (Ω : ℂ) * s) =
      ((E - Ω : ℝ) : ℂ) * ((m : ℂ) * s) := by
  intro E
  have h := scalar_bdg_eig_bot ξ₀ m Ω
  dsimp at h
  linear_combination h * s

private lemma scalar_bdg_minus_top_vec (ξ₀ m Ω : ℝ) (s : ℂ) :
    let E : ℝ := Real.sqrt (ξ₀ ^ 2 + m ^ 2)
    (((ξ₀ + E : ℝ) : ℂ)) * ((ξ₀ : ℂ) * s + (Ω : ℂ) * s) + (m : ℂ) * ((m : ℂ) * s) =
      ((E + Ω : ℝ) : ℂ) * ((((ξ₀ + E : ℝ) : ℂ)) * s) := by
  intro E
  have h := scalar_bdg_minus_top ξ₀ m Ω
  dsimp at h
  linear_combination h * s

private lemma scalar_bdg_minus_bot_vec (ξ₀ m Ω : ℝ) (s : ℂ) :
    let E : ℝ := Real.sqrt (ξ₀ ^ 2 + m ^ 2)
    (((ξ₀ + E : ℝ) : ℂ)) * ((m : ℂ) * s) + (m : ℂ) * ((-(ξ₀ : ℂ)) * s + (Ω : ℂ) * s) =
      ((E + Ω : ℝ) : ℂ) * ((m : ℂ) * s) := by
  intro E
  have h := scalar_bdg_minus_bot ξ₀ m Ω
  dsimp at h
  linear_combination h * s

private lemma scalar_triplet_00 (d₁ d₂ d₃ : ℂ) :
    (-d₁ + Complex.I * d₂) * (starRingEnd ℂ) (-d₁ + Complex.I * d₂) + d₃ * (starRingEnd ℂ) d₃ =
      d₁ * (starRingEnd ℂ) d₁ + d₂ * (starRingEnd ℂ) d₂ + d₃ * (starRingEnd ℂ) d₃ +
        Complex.I * (d₁ * (starRingEnd ℂ) d₂ - d₂ * (starRingEnd ℂ) d₁) := by
  simp only [map_add, map_neg, map_mul, Complex.conj_I]
  calc
    (-d₁ + Complex.I * d₂) * (-starRingEnd ℂ d₁ + -Complex.I * starRingEnd ℂ d₂) +
        d₃ * starRingEnd ℂ d₃
        = d₁ * starRingEnd ℂ d₁ + Complex.I * (d₁ * starRingEnd ℂ d₂ - d₂ * starRingEnd ℂ d₁) -
            (Complex.I ^ 2) * (d₂ * starRingEnd ℂ d₂) + d₃ * starRingEnd ℂ d₃ := by ring
    _ = d₁ * starRingEnd ℂ d₁ + d₂ * starRingEnd ℂ d₂ + d₃ * starRingEnd ℂ d₃ +
          Complex.I * (d₁ * starRingEnd ℂ d₂ - d₂ * starRingEnd ℂ d₁) := by
          rw [Complex.I_sq]; ring

private lemma scalar_triplet_11 (d₁ d₂ d₃ : ℂ) :
    d₃ * (starRingEnd ℂ) d₃ + (d₁ + Complex.I * d₂) * (starRingEnd ℂ) (d₁ + Complex.I * d₂) =
      d₁ * (starRingEnd ℂ) d₁ + d₂ * (starRingEnd ℂ) d₂ + d₃ * (starRingEnd ℂ) d₃ +
        -(Complex.I * (d₁ * (starRingEnd ℂ) d₂ - d₂ * (starRingEnd ℂ) d₁)) := by
  simp only [map_add, map_mul, Complex.conj_I]
  calc
    d₃ * starRingEnd ℂ d₃ +
        (d₁ + Complex.I * d₂) * (starRingEnd ℂ d₁ + -Complex.I * starRingEnd ℂ d₂)
        = d₁ * starRingEnd ℂ d₁ - Complex.I * (d₁ * starRingEnd ℂ d₂ - d₂ * starRingEnd ℂ d₁) -
            (Complex.I ^ 2) * (d₂ * starRingEnd ℂ d₂) + d₃ * starRingEnd ℂ d₃ := by ring
    _ = d₁ * starRingEnd ℂ d₁ + d₂ * starRingEnd ℂ d₂ + d₃ * starRingEnd ℂ d₃ +
          -(Complex.I * (d₁ * starRingEnd ℂ d₂ - d₂ * starRingEnd ℂ d₁)) := by
          rw [Complex.I_sq]; ring

private lemma scalar_triplet_01 (d₁ d₂ d₃ : ℂ) :
    (-d₁ + Complex.I * d₂) * (starRingEnd ℂ) d₃ + d₃ * (starRingEnd ℂ) (d₁ + Complex.I * d₂) =
      Complex.I * (d₂ * (starRingEnd ℂ) d₃ - d₃ * (starRingEnd ℂ) d₂) +
        -(Complex.I * (d₃ * (starRingEnd ℂ) d₁ - d₁ * (starRingEnd ℂ) d₃) * Complex.I) := by
  simp only [map_add, map_mul, Complex.conj_I]
  have hI : Complex.I * (d₃ * starRingEnd ℂ d₁ - d₁ * starRingEnd ℂ d₃) * Complex.I =
      Complex.I ^ 2 * (d₃ * starRingEnd ℂ d₁ - d₁ * starRingEnd ℂ d₃) := by ring
  rw [hI, Complex.I_sq]
  ring

private lemma scalar_triplet_10 (d₁ d₂ d₃ : ℂ) :
    d₃ * (starRingEnd ℂ) (-d₁ + Complex.I * d₂) + (d₁ + Complex.I * d₂) * (starRingEnd ℂ) d₃ =
      Complex.I * (d₂ * (starRingEnd ℂ) d₃ - d₃ * (starRingEnd ℂ) d₂) +
        Complex.I * (d₃ * (starRingEnd ℂ) d₁ - d₁ * (starRingEnd ℂ) d₃) * Complex.I := by
  simp only [map_add, map_neg, map_mul, Complex.conj_I]
  have hI : Complex.I * (d₃ * starRingEnd ℂ d₁ - d₁ * starRingEnd ℂ d₃) * Complex.I =
      Complex.I ^ 2 * (d₃ * starRingEnd ℂ d₁ - d₁ * starRingEnd ℂ d₃) := by ring
  rw [hI, Complex.I_sq]
  ring

private lemma scalar_nonunitary_chiral_norm (m : ℝ) :
    (m : ℂ) * star (m : ℂ) + (Complex.I * (m : ℂ)) * star (Complex.I * (m : ℂ)) +
        (0 : ℂ) * star (0 : ℂ) = 2 * ((m : ℂ) ^ 2) := by
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I, star_zero, mul_zero,
    add_zero]
  calc
    (m : ℂ) * (m : ℂ) + Complex.I * (m : ℂ) * (-Complex.I * (m : ℂ))
        = (m : ℂ) ^ 2 - Complex.I ^ 2 * (m : ℂ) ^ 2 := by ring
    _ = (m : ℂ) ^ 2 - (-1) * (m : ℂ) ^ 2 := by rw [Complex.I_sq]
    _ = 2 * (m : ℂ) ^ 2 := by ring

private lemma scalar_chiral_zero_col2 (m : ℝ) :
    (m : ℂ) + Complex.I * (Complex.I * (m : ℂ)) = 0 := by
  calc
    (m : ℂ) + Complex.I * (Complex.I * (m : ℂ)) = (m : ℂ) + Complex.I ^ 2 * (m : ℂ) := by ring
    _ = (m : ℂ) + (-1) * (m : ℂ) := by rw [Complex.I_sq]
    _ = 0 := by ring

private lemma scalar_chiral_zero_col2_conj (m : ℝ) :
    (starRingEnd ℂ) ((m : ℂ) + Complex.I * (Complex.I * (m : ℂ))) = 0 := by
  rw [scalar_chiral_zero_col2, map_zero]

private lemma scalar_cosh_sq_sub_sinh_sq (x : ℝ) :
    Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
  rw [Real.cosh_eq, Real.sinh_eq]
  have h1 : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith [h1]

private lemma scalar_cosh_add_sinh (x : ℝ) :
    Real.cosh x + Real.sinh x = Real.exp x := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

private lemma scalar_cosh_sub_sinh (x : ℝ) :
    Real.cosh x - Real.sinh x = Real.exp (-x) := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

private lemma scalar_hyp_norm_preserve (g Ω γ t : ℝ) (hγ : γ ^ 2 = g ^ 2 - Ω ^ 2)
    (hγ_ne : γ ≠ 0) :
    Real.cosh (γ * t) * Real.cosh (γ * t) -
        (Real.sinh (γ * t) / γ) * (Real.sinh (γ * t) / γ) * (g ^ 2 - Ω ^ 2) = 1 := by
  have h1 : (Real.sinh (γ * t) / γ) * (Real.sinh (γ * t) / γ) * (g ^ 2 - Ω ^ 2) =
      Real.sinh (γ * t) * Real.sinh (γ * t) := by
    rw [← hγ]
    field_simp [hγ_ne]
  rw [h1]
  exact scalar_cosh_sq_sub_sinh_sq (γ * t)

private lemma scalar_ell_norm_preserve (g Ω ω t : ℝ) (hω : ω ^ 2 = Ω ^ 2 - g ^ 2)
    (hω_ne : ω ≠ 0) :
    Real.cos (ω * t) * Real.cos (ω * t) -
        (Real.sin (ω * t) / ω) * (Real.sin (ω * t) / ω) * (g ^ 2 - Ω ^ 2) = 1 := by
  have hneg : g ^ 2 - Ω ^ 2 = -(ω ^ 2) := by linarith [hω]
  have h1 : (Real.sin (ω * t) / ω) * (Real.sin (ω * t) / ω) * (g ^ 2 - Ω ^ 2) =
      -(Real.sin (ω * t) * Real.sin (ω * t)) := by
    rw [hneg]
    field_simp [hω_ne]
  rw [h1, sub_neg_eq_add, ← sq, ← sq]
  exact Real.cos_sq_add_sin_sq (ω * t)

/-! ### Part 1: Singlet (`1`) vs. Triplet (`3`) Decomposition & Local Spin-Frame Rotation -/

/-- Complex Pauli `σ_x` on `Fin 2`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Complex Pauli `σ_y` on `Fin 2`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Complex Pauli `σ_z` on `Fin 2`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Spin-exchange permutation operator on `Fin 2 × Fin 2 → ℂ`. -/
def swapSpin : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- Orthogonal rank-1 spin-singlet projector `P_sing = (1 - SWAP) / 2`. -/
def projSinglet : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((1 : ℂ) / 2) • (1 - swapSpin)

/-- Orthogonal rank-3 spin-triplet projector `P_trip = (1 + SWAP) / 2`. -/
def projTriplet : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((1 : ℂ) / 2) • (1 + swapSpin)

/-- Total spin-`x` generator `S_x = (σ_x ⊗ I + I ⊗ σ_x) / 2`. -/
def totSpinX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((1 : ℂ) / 2) • (pauliX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliX)

/-- Total spin-`y` generator `S_y = (σ_y ⊗ I + I ⊗ σ_y) / 2`. -/
def totSpinY : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((1 : ℂ) / 2) • (pauliY ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliY)

/-- Total spin-`z` generator `S_z = (σ_z ⊗ I + I ⊗ σ_z) / 2`. -/
def totSpinZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((1 : ℂ) / 2) • (pauliZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauliZ)

/-- Total squared spin Casimir `S² = S_x² + S_y² + S_z²`. -/
def totSpinCasimir : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  totSpinX * totSpinX + totSpinY * totSpinY + totSpinZ * totSpinZ

/-- Antisymmetric spin-singlet state `|0, 0⟩ = |↑↓⟩ - |↓↑⟩`. -/
def singletVec : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- Symmetric triplet `m_S = +1` state `|1, +1⟩ = |↑↑⟩`. -/
def tripletPlusVec : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (0, 0) then 1 else 0

/-- Symmetric triplet `m_S = 0` state `|1, 0⟩ = |↑↓⟩ + |↓↑⟩`. -/
def tripletZeroVec : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (0, 1) then 1 else if p = (1, 0) then 1 else 0

/-- Symmetric triplet `m_S = -1` state `|1, -1⟩ = |↓↓⟩`. -/
def tripletMinusVec : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (1, 1) then 1 else 0

/-- Local `SU(2)` z-axis spin-frame rotation `exp(i θ σ_z / 2)`. -/
def localSpinRotZ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)), 0;
     0, Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ))]

/-- Diagonal local spin-frame rotation acting on both two-spinor factors: `U(θ) ⊗ U(θ)`. -/
def twoSpinRotZ (θ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  localSpinRotZ θ ⊗ₖ localSpinRotZ θ

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem exists_noncomm_mat2_complex :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨pauliX, pauliZ, fun h => ?_⟩
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h01
  dsimp [pauliX, pauliZ] at h01
  norm_num at h01

/-- Explicit non-commutativity witness on `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`. -/
theorem exists_noncomm_mat2x2_complex :
    ∃ A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨totSpinX, totSpinZ, fun h => ?_⟩
  have h0 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M (0, 0) (0, 1)) h
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] at h0
  dsimp [totSpinX, totSpinZ] at h0
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    smul_eq_mul] at h0
  dsimp [pauliX, pauliZ] at h0
  norm_num at h0

/-- **Theorem 1 (Singlet `1` vs. Triplet `3` Decomposition & Local Spin-Frame Rotation Law)**:
Establishes orthogonal projections `P_sing` (`tr = 1`) and `P_trip` (`tr = 3`), the exact Casimir
identity `S² = 2 P_trip`, `su(2)` annihilation of `singletVec`, triplet `S_z` weights `±1, 0`,
invariance of `singletVec` under `twoSpinRotZ θ`, and phase precession `exp(±i θ)` on `|1, ±1⟩`. -/
theorem singlet_triplet_decomposition_and_rotation (θ : ℝ) :
    (projSinglet + projTriplet = 1) ∧
    (projSinglet * projSinglet = projSinglet) ∧
    (projTriplet * projTriplet = projTriplet) ∧
    (projSinglet * projTriplet = 0) ∧
    (Matrix.trace projSinglet = 1) ∧
    (Matrix.trace projTriplet = 3) ∧
    (totSpinCasimir = (2 : ℂ) • projTriplet) ∧
    (totSpinX.mulVec singletVec = 0 ∧ totSpinY.mulVec singletVec = 0 ∧
      totSpinZ.mulVec singletVec = 0) ∧
    (totSpinZ.mulVec tripletPlusVec = tripletPlusVec ∧
      totSpinZ.mulVec tripletZeroVec = 0 ∧
      totSpinZ.mulVec tripletMinusVec = -tripletMinusVec) ∧
    ((twoSpinRotZ θ).mulVec singletVec = singletVec ∧
      (twoSpinRotZ θ).mulVec tripletPlusVec = Complex.exp (Complex.I * (θ : ℂ)) • tripletPlusVec ∧
      (twoSpinRotZ θ).mulVec tripletZeroVec = tripletZeroVec ∧
      (twoSpinRotZ θ).mulVec tripletMinusVec =
        Complex.exp (-Complex.I * (θ : ℂ)) • tripletMinusVec) := by
  have hAdd : projSinglet + projTriplet = 1 := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      dsimp [projSinglet, projTriplet] <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
        smul_eq_mul] <;>
      dsimp [swapSpin] <;>
      (norm_num; done)
  have hSwapSq : swapSpin * swapSpin = 1 := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      dsimp [swapSpin] <;>
      (norm_num; done)
  have hSS : projSinglet * projSinglet = projSinglet := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      dsimp [projSinglet] <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul] <;>
      dsimp [swapSpin] <;>
      (norm_num; done)
  have hTT : projTriplet * projTriplet = projTriplet := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      dsimp [projTriplet] <;>
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul] <;>
      dsimp [swapSpin] <;>
      (norm_num; done)
  have hST : projSinglet * projTriplet = 0 := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.zero_apply]
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      dsimp [projSinglet, projTriplet] <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
        smul_eq_mul] <;>
      dsimp [swapSpin] <;>
      (norm_num; done)
  have hTrS : Matrix.trace projSinglet = 1 := by
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]
    dsimp [projSinglet]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    dsimp [swapSpin]
    norm_num
  have hTrT : Matrix.trace projTriplet = 3 := by
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]
    dsimp [projTriplet]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    dsimp [swapSpin]
    norm_num
  have hCas : totSpinCasimir = (2 : ℂ) • projTriplet := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    dsimp [totSpinCasimir]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      dsimp [totSpinX, totSpinY, totSpinZ, projTriplet] <;>
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
        smul_eq_mul] <;>
      dsimp [pauliX, pauliY, pauliZ, swapSpin] <;>
      simp only [zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, neg_mul, mul_neg,
        neg_neg, mul_assoc, mul_left_comm, Complex.I_mul_I] <;>
      norm_num
  have hSingAnn : totSpinX.mulVec singletVec = 0 ∧ totSpinY.mulVec singletVec = 0 ∧
      totSpinZ.mulVec singletVec = 0 := by
    refine ⟨?_, ?_, ?_⟩
    · ext ⟨i₁, i₂⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.zero_apply]
      fin_cases i₁ <;> fin_cases i₂ <;>
        dsimp [totSpinX] <;>
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
          smul_eq_mul] <;>
        dsimp [pauliX, singletVec] <;>
        (norm_num; done)
    · ext ⟨i₁, i₂⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.zero_apply]
      fin_cases i₁ <;> fin_cases i₂ <;>
        dsimp [totSpinY] <;>
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
          smul_eq_mul] <;>
        dsimp [pauliY, singletVec] <;>
        (norm_num; done)
    · ext ⟨i₁, i₂⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.zero_apply]
      fin_cases i₁ <;> fin_cases i₂ <;>
        dsimp [totSpinZ] <;>
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
          smul_eq_mul] <;>
        dsimp [pauliZ, singletVec] <;>
        (norm_num; done)
  have hTripSz : totSpinZ.mulVec tripletPlusVec = tripletPlusVec ∧
      totSpinZ.mulVec tripletZeroVec = 0 ∧
      totSpinZ.mulVec tripletMinusVec = -tripletMinusVec := by
    refine ⟨?_, ?_, ?_⟩
    · ext ⟨i₁, i₂⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
      fin_cases i₁ <;> fin_cases i₂ <;>
        dsimp [totSpinZ] <;>
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
          smul_eq_mul] <;>
        dsimp [pauliZ, tripletPlusVec] <;>
        (norm_num; done)
    · ext ⟨i₁, i₂⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.zero_apply]
      fin_cases i₁ <;> fin_cases i₂ <;>
        dsimp [totSpinZ] <;>
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
          smul_eq_mul] <;>
        dsimp [pauliZ, tripletZeroVec] <;>
        (norm_num; done)
    · ext ⟨i₁, i₂⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.neg_apply]
      fin_cases i₁ <;> fin_cases i₂ <;>
        dsimp [totSpinZ] <;>
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
          smul_eq_mul] <;>
        dsimp [pauliZ, tripletMinusVec] <;>
        (norm_num; done)
  have hRot : (twoSpinRotZ θ).mulVec singletVec = singletVec ∧
      (twoSpinRotZ θ).mulVec tripletPlusVec = Complex.exp (Complex.I * (θ : ℂ)) • tripletPlusVec ∧
      (twoSpinRotZ θ).mulVec tripletZeroVec = tripletZeroVec ∧
      (twoSpinRotZ θ).mulVec tripletMinusVec =
        Complex.exp (-Complex.I * (θ : ℂ)) • tripletMinusVec := by
    have hp := scalar_rot_z_phase θ
    have hps : Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) = 1 := by
      rw [mul_comm]; exact hp
    have hsq := scalar_rot_z_sq θ
    have hnsq := scalar_rot_z_neg_sq θ
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat, neg_mul] at hp hps hsq hnsq
    have hr00 : localSpinRotZ θ 0 0 = Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) := rfl
    have hr01 : localSpinRotZ θ 0 1 = 0 := rfl
    have hr10 : localSpinRotZ θ 1 0 = 0 := rfl
    have hr11 : localSpinRotZ θ 1 1 = Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ)) := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext ⟨i₁, i₂⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
      fin_cases i₁ <;> fin_cases i₂ <;>
        simp [twoSpinRotZ, Matrix.kroneckerMap_apply, Fin.isValue, hr00, hr01, hr10, hr11,
          singletVec, hp, hps]
    · ext ⟨i₁, i₂⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.smul_apply,
        smul_eq_mul]
      fin_cases i₁ <;> fin_cases i₂ <;>
        simp [twoSpinRotZ, Matrix.kroneckerMap_apply, Fin.isValue, hr00, hr01, hr10, hr11,
          tripletPlusVec, hsq]
    · ext ⟨i₁, i₂⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
      fin_cases i₁ <;> fin_cases i₂ <;>
        simp [twoSpinRotZ, Matrix.kroneckerMap_apply, Fin.isValue, hr00, hr01, hr10, hr11,
          tripletZeroVec, hp, hps]
    · ext ⟨i₁, i₂⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.smul_apply,
        smul_eq_mul]
      fin_cases i₁ <;> fin_cases i₂ <;>
        simp [twoSpinRotZ, Matrix.kroneckerMap_apply, Fin.isValue, hr00, hr01, hr10, hr11,
          tripletMinusVec, hnsq]
  exact ⟨hAdd, hSS, hTT, hST, hTrS, hTrT, hCas, hSingAnn, hTripSz, hRot⟩

/-! ### Part 2: Rotating-Frame BdG Hamiltonian: Singlet Immunity vs. Triplet Gap Collapse -/

/-- Doubled spin-BdG Hamiltonian in a locally rotating spin frame (`- Ω S_z`) with kinetic
energy `ξ₀` and pairing gap `m`. -/
def bdgSpinRotHam (ξ₀ m Ω : ℝ) :
    Matrix ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) ℂ :=
  Matrix.fromBlocks ((ξ₀ : ℂ) • 1 - (Ω : ℂ) • totSpinZ) ((m : ℂ) • 1)
    ((m : ℂ) • 1) ((-(ξ₀ : ℂ)) • 1 - (Ω : ℂ) • totSpinZ)

/-- General doubled particle–hole singlet state `a |singlet⟩_+ ⊕ b |singlet⟩_-`. -/
def doubledSinglet (a b : ℂ) : (Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2) → ℂ :=
  Sum.elim (a • singletVec) (b • singletVec)

/-- Triplet `m_S = +1` Bogoliubov quasiparticle state shifted to energy `√(ξ₀² + m²) - Ω`. -/
def tripletQuasiPlus (ξ₀ m : ℝ) : (Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2) → ℂ :=
  Sum.elim ((((ξ₀ + Real.sqrt (ξ₀ ^ 2 + m ^ 2) : ℝ) : ℂ)) • tripletPlusVec)
    ((m : ℂ) • tripletPlusVec)

/-- Triplet `m_S = -1` Bogoliubov quasiparticle state shifted to energy `√(ξ₀² + m²) + Ω`. -/
def tripletQuasiMinus (ξ₀ m : ℝ) : (Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2) → ℂ :=
  Sum.elim ((((ξ₀ + Real.sqrt (ξ₀ ^ 2 + m ^ 2) : ℝ) : ℂ)) • tripletMinusVec)
    ((m : ℂ) • tripletMinusVec)

/-- Explicit matrix non-commutativity witness on the doubled `(Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)`
spin-BdG carrier. -/
theorem exists_noncomm_bdg_spin_mat :
    ∃ A B :
      Matrix ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) ℂ,
      A * B ≠ B * A := by
  let S : Matrix ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2))
      ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  refine ⟨bdgSpinRotHam 0 1 0, S, fun h => ?_⟩
  have h0 := congrArg (fun M => M (Sum.inl (0, 0)) (Sum.inr (0, 0))) h
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two] at h0
  dsimp [bdgSpinRotHam, S] at h0
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.zero_apply, Matrix.neg_apply, smul_eq_mul] at h0
  norm_num at h0

private lemma fromBlocks_mulVec_elim {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℂ) (B : Matrix α β ℂ) (C : Matrix β α ℂ) (D : Matrix β β ℂ)
    (u : α → ℂ) (v : β → ℂ) :
    (Matrix.fromBlocks A B C D).mulVec (Sum.elim u v) =
      Sum.elim (A.mulVec u + B.mulVec v) (C.mulVec u + D.mulVec v) := by
  ext x
  cases x with
  | inl i =>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  | inr j =>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

/-- **Theorem 2 (Rotating-Frame Singlet Stability vs. Triplet Coriolis Splitting)**:
1. `bdgSpinRotHam ξ₀ m Ω` leaves every doubled singlet state independent of `Ω`, satisfies
   `H(Ω)² ψ_sing = (ξ₀² + m²) ψ_sing`, and preserves the uniform gap `m² ‖ψ_sing‖² ≤ ‖H(Ω) ψ_sing‖²`.
2. The triplet quasiparticles split linearly with frame rotation:
   `H(Ω) ψ_trip(+) = (√(ξ₀² + m²) - Ω) ψ_trip(+)` and
   `H(Ω) ψ_trip(-) = (√(ξ₀² + m²) + Ω) ψ_trip(-)`. -/
theorem rotating_bdg_singlet_stability_vs_triplet_instability (ξ₀ m Ω : ℝ) (a b : ℂ) :
    ((bdgSpinRotHam ξ₀ m Ω).mulVec (doubledSinglet a b) =
      (bdgSpinRotHam ξ₀ m 0).mulVec (doubledSinglet a b)) ∧
    (((bdgSpinRotHam ξ₀ m Ω) * (bdgSpinRotHam ξ₀ m Ω)).mulVec (doubledSinglet a b) =
      (((ξ₀ ^ 2 + m ^ 2 : ℝ) : ℂ)) • doubledSinglet a b) ∧
    (m ^ 2 * (2 * (Complex.normSq a + Complex.normSq b)) ≤
      ∑ p, Complex.normSq ((bdgSpinRotHam ξ₀ m Ω).mulVec (doubledSinglet a b) p)) ∧
    ((bdgSpinRotHam ξ₀ m Ω).mulVec (tripletQuasiPlus ξ₀ m) =
      (((Real.sqrt (ξ₀ ^ 2 + m ^ 2) - Ω : ℝ) : ℂ)) • tripletQuasiPlus ξ₀ m) ∧
    ((bdgSpinRotHam ξ₀ m Ω).mulVec (tripletQuasiMinus ξ₀ m) =
      (((Real.sqrt (ξ₀ ^ 2 + m ^ 2) + Ω : ℝ) : ℂ)) • tripletQuasiMinus ξ₀ m) := by
  have hDec := singlet_triplet_decomposition_and_rotation 0
  have hSingZ : totSpinZ.mulVec singletVec = 0 := hDec.2.2.2.2.2.2.2.1.2.2
  have hPlusZ : totSpinZ.mulVec tripletPlusVec = tripletPlusVec := hDec.2.2.2.2.2.2.2.2.1.1
  have hMinusZ : totSpinZ.mulVec tripletMinusVec = -tripletMinusVec := hDec.2.2.2.2.2.2.2.2.1.2.2
  have hSingVec : ∀ (ξ' m' Ω' : ℝ),
      (bdgSpinRotHam ξ' m' Ω').mulVec (doubledSinglet a b) =
        Sum.elim (((ξ' : ℂ) * a + (m' : ℂ) * b) • singletVec)
          (((m' : ℂ) * a - (ξ' : ℂ) * b) • singletVec) := by
    intro ξ' m' Ω'
    dsimp [bdgSpinRotHam, doubledSinglet]
    rw [fromBlocks_mulVec_elim]
    congr 1
    · ext p
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul,
        hSingZ, smul_zero, sub_zero, Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      exact scalar_singlet_vec_top _ _ _ _ _
    · ext p
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul,
        hSingZ, smul_zero, sub_zero, Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      exact scalar_singlet_vec_bot _ _ _ _ _
  have hOmegaIndep :
      (bdgSpinRotHam ξ₀ m Ω).mulVec (doubledSinglet a b) =
        (bdgSpinRotHam ξ₀ m 0).mulVec (doubledSinglet a b) := by
    rw [hSingVec ξ₀ m Ω, hSingVec ξ₀ m 0]
  have hSingSq :
      ((bdgSpinRotHam ξ₀ m Ω) * (bdgSpinRotHam ξ₀ m Ω)).mulVec (doubledSinglet a b) =
        (((ξ₀ ^ 2 + m ^ 2 : ℝ) : ℂ)) • doubledSinglet a b := by
    rw [← Matrix.mulVec_mulVec, hSingVec ξ₀ m Ω]
    dsimp [bdgSpinRotHam, doubledSinglet]
    rw [fromBlocks_mulVec_elim]
    ext x
    cases x with
    | inl p =>
      simp only [Sum.elim_inl, Pi.smul_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_smul, hSingZ, smul_zero, sub_zero, Pi.add_apply,
        Complex.real_smul, smul_eq_mul]
      exact scalar_singlet_sq_top_vec ξ₀ m a b (singletVec p)
    | inr p =>
      simp only [Sum.elim_inr, Pi.smul_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_smul, hSingZ, smul_zero, sub_zero, Pi.add_apply,
        Complex.real_smul, smul_eq_mul]
      exact scalar_singlet_sq_bot_vec ξ₀ m a b (singletVec p)
  have hGapNorm :
      m ^ 2 * (2 * (Complex.normSq a + Complex.normSq b)) ≤
        ∑ p, Complex.normSq ((bdgSpinRotHam ξ₀ m Ω).mulVec (doubledSinglet a b) p) := by
    rw [hSingVec ξ₀ m Ω]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Sum.elim_inl,
      Sum.elim_inr, Pi.smul_apply, smul_eq_mul]
    dsimp [singletVec]
    simp only [zero_ne_one, ↓reduceIte, Prod.mk.injEq, and_false, and_true, true_and, one_ne_zero,
      mul_zero, Complex.normSq_zero, add_zero, zero_add, mul_one]
    rw [scalar_singlet_normsq]
    have hnonneg : 0 ≤ 2 * (Complex.normSq a + Complex.normSq b) :=
      mul_nonneg (by norm_num) (add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b))
    have hle : m ^ 2 ≤ ξ₀ ^ 2 + m ^ 2 := le_add_of_nonneg_left (sq_nonneg ξ₀)
    exact mul_le_mul_of_nonneg_right hle hnonneg
  have hTripPlus :
      (bdgSpinRotHam ξ₀ m Ω).mulVec (tripletQuasiPlus ξ₀ m) =
        (((Real.sqrt (ξ₀ ^ 2 + m ^ 2) - Ω : ℝ) : ℂ)) • tripletQuasiPlus ξ₀ m := by
    dsimp [bdgSpinRotHam, tripletQuasiPlus]
    rw [fromBlocks_mulVec_elim]
    ext x
    cases x with
    | inl p =>
      simp only [Sum.elim_inl, Pi.smul_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_smul, hPlusZ, Pi.add_apply, Pi.sub_apply,
        Complex.real_smul, smul_eq_mul]
      exact scalar_bdg_plus_top_vec ξ₀ m Ω (tripletPlusVec p)
    | inr p =>
      simp only [Sum.elim_inr, Pi.smul_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_smul, hPlusZ, Pi.add_apply, Pi.sub_apply,
        Complex.real_smul, smul_eq_mul]
      exact scalar_bdg_plus_bot_vec ξ₀ m Ω (tripletPlusVec p)
  have hTripMinus :
      (bdgSpinRotHam ξ₀ m Ω).mulVec (tripletQuasiMinus ξ₀ m) =
        (((Real.sqrt (ξ₀ ^ 2 + m ^ 2) + Ω : ℝ) : ℂ)) • tripletQuasiMinus ξ₀ m := by
    dsimp [bdgSpinRotHam, tripletQuasiMinus]
    rw [fromBlocks_mulVec_elim]
    ext x
    cases x with
    | inl p =>
      simp only [Sum.elim_inl, Pi.smul_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_smul, hMinusZ, smul_neg, sub_neg_eq_add,
        Pi.add_apply, Pi.neg_apply, Complex.real_smul, smul_eq_mul]
      exact scalar_bdg_minus_top_vec ξ₀ m Ω (tripletMinusVec p)
    | inr p =>
      simp only [Sum.elim_inr, Pi.smul_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_smul, hMinusZ, smul_neg, sub_neg_eq_add,
        Pi.add_apply, Pi.neg_apply, Complex.real_smul, smul_eq_mul]
      exact scalar_bdg_minus_bot_vec ξ₀ m Ω (tripletMinusVec p)
  exact ⟨hOmegaIndep, hSingSq, hGapNorm, hTripPlus, hTripMinus⟩

/-- **Coriolis Instability Threshold (`Ω = m` Zero Mode & `Ω > m` Negative Quasiparticle Branch)**:
When local spin-frame rotation frequency `Ω` reaches `m > 0` at `ξ₀ = 0`, the `m_S = +1` triplet
quasiparticle gap closes (`H(m) ψ = 0`) and flips negative (`m - Ω < 0`) for `Ω > m`. -/
theorem triplet_coriolis_gap_closure_and_instability {m Ω : ℝ} (hm : 0 < m) :
    (tripletQuasiPlus 0 m ≠ 0) ∧
    ((bdgSpinRotHam 0 m m).mulVec (tripletQuasiPlus 0 m) = 0) ∧
    (m < Ω → (bdgSpinRotHam 0 m Ω).mulVec (tripletQuasiPlus 0 m) =
      (((m - Ω : ℝ) : ℂ)) • tripletQuasiPlus 0 m ∧ m - Ω < 0) := by
  have hnz : tripletQuasiPlus 0 m ≠ 0 := by
    intro h
    have h0 := congrArg (fun v => v (Sum.inr (0, 0))) h
    dsimp [tripletQuasiPlus, tripletPlusVec] at h0
    simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, ↓reduceIte, mul_one, Pi.zero_apply,
      Complex.ofReal_eq_zero] at h0
    exact hm.ne' h0
  have hsqrt : Real.sqrt ((0 : ℝ) ^ 2 + m ^ 2) = m := by
    rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq hm.le]
  have h0m : (bdgSpinRotHam 0 m m).mulVec (tripletQuasiPlus 0 m) = 0 := by
    have h := (rotating_bdg_singlet_stability_vs_triplet_instability 0 m m 0 0).2.2.2.1
    rw [hsqrt, sub_self, Complex.ofReal_zero, zero_smul] at h
    exact h
  have hgt : m < Ω → (bdgSpinRotHam 0 m Ω).mulVec (tripletQuasiPlus 0 m) =
      (((m - Ω : ℝ) : ℂ)) • tripletQuasiPlus 0 m ∧ m - Ω < 0 := by
    intro hΩ
    have h := (rotating_bdg_singlet_stability_vs_triplet_instability 0 m Ω 0 0).2.2.2.1
    rw [hsqrt] at h
    exact ⟨h, sub_neg.mpr hΩ⟩
  exact ⟨hnz, h0m, hgt⟩

/-! ### Part 3: Non-Unitary Triplet Pairing (`d × d* ≠ 0`): Band Splitting & Gap Collapse -/

/-- Spin-triplet gap matrix `Δ(d) = (d · σ)(i σ_y) = [[-d₁ + i d₂, d₃], [d₃, d₁ + i d₂]]`. -/
def tripletGapMat (d₁ d₂ d₃ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-d₁ + Complex.I * d₂, d₃;
     d₃, d₁ + Complex.I * d₂]

/-- Non-unitarity spin polarization component `(i (d × d*))_1 = i (d₂ d₃* - d₃ d₂*)`. -/
def nonUnitaryQ1 (_d₁ d₂ d₃ : ℂ) : ℂ := Complex.I * (d₂ * star d₃ - d₃ * star d₂)

/-- Non-unitarity spin polarization component `(i (d × d*))_2 = i (d₃ d₁* - d₁ d₃*)`. -/
def nonUnitaryQ2 (d₁ _d₂ d₃ : ℂ) : ℂ := Complex.I * (d₃ * star d₁ - d₁ * star d₃)

/-- Non-unitarity spin polarization component `(i (d × d*))_3 = i (d₁ d₂* - d₂ d₁*)`. -/
def nonUnitaryQ3 (d₁ d₂ _d₃ : ℂ) : ℂ := Complex.I * (d₁ * star d₂ - d₂ * star d₁)

/-- Squared norm `‖d‖² = d₁ d₁* + d₂ d₂* + d₃ d₃*` of a triplet `d`-vector. -/
def dNormSq (d₁ d₂ d₃ : ℂ) : ℂ :=
  d₁ * star d₁ + d₂ * star d₂ + d₃ * star d₃

/-- Full `4 × 4` (`Fin 2 ⊕ Fin 2`) spin-triplet BdG Hamiltonian with general vector `d`. -/
def tripletBdG4 (ξ₀ : ℝ) (d₁ d₂ d₃ : ℂ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks ((ξ₀ : ℂ) • 1) (tripletGapMat d₁ d₂ d₃)
    ((tripletGapMat d₁ d₂ d₃).conjTranspose) ((-(ξ₀ : ℂ)) • 1)

/-- Explicit matrix non-commutativity witness on the `Fin 2 ⊕ Fin 2` triplet BdG carrier. -/
theorem exists_noncomm_triplet_bdg4 :
    ∃ A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨tripletBdG4 1 1 0 0, Matrix.fromBlocks 1 0 0 (-1), fun h => ?_⟩
  have h02 := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ =>
    M (Sum.inl 0) (Sum.inr 0)) h
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h02
  dsimp [tripletBdG4] at h02
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
    Matrix.neg_apply, smul_eq_mul] at h02
  dsimp [tripletGapMat] at h02
  norm_num at h02

private lemma tripletGapMat_mul_conjTranspose (d₁ d₂ d₃ : ℂ) :
    tripletGapMat d₁ d₂ d₃ * (tripletGapMat d₁ d₂ d₃).conjTranspose =
      dNormSq d₁ d₂ d₃ • 1 +
        nonUnitaryQ1 d₁ d₂ d₃ • pauliX +
        nonUnitaryQ2 d₁ d₂ d₃ • pauliY +
        nonUnitaryQ3 d₁ d₂ d₃ • pauliZ := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    dsimp [tripletGapMat, dNormSq, nonUnitaryQ1, nonUnitaryQ2, nonUnitaryQ3,
      pauliX, pauliY, pauliZ] <;>
    simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg, Complex.star_def]
  · exact scalar_triplet_00 d₁ d₂ d₃
  · exact scalar_triplet_01 d₁ d₂ d₃
  · exact scalar_triplet_10 d₁ d₂ d₃
  · exact scalar_triplet_11 d₁ d₂ d₃

/-- **Theorem 3 (Non-Unitary Triplet Band Splitting `i(d × d*)·σ` & Chiral Gap Collapse)**:
1. `Δ(d)ᵀ = Δ(d)` (symmetric spin-triplet pairing).
2. `Δ(d) * Δ(d)ᴴ = ‖d‖² I + q₁ σ_x + q₂ σ_y + q₃ σ_z` where `q = i (d × d*)`.
3. For real unitary `d = (r₁, r₂, r₃)`, `q₁ = q₂ = q₃ = 0` and `Δ Δᴴ = (r₁² + r₂² + r₃²) I`.
4. For the chiral non-unitary state `d = (m, i m, 0)` with `m ≠ 0`, `‖d‖² = 2 m² ≠ 0` yet
   `tripletBdG4 0 m (i m) 0` admits a nonzero zero mode (`Sum.elim ![0, 1] 0`). -/
theorem nonunitary_triplet_band_splitting_and_gap_collapse
    (d₁ d₂ d₃ : ℂ) (r₁ r₂ r₃ : ℝ) (m : ℝ) (hm : m ≠ 0) :
    ((tripletGapMat d₁ d₂ d₃)ᵀ = tripletGapMat d₁ d₂ d₃) ∧
    (tripletGapMat d₁ d₂ d₃ * (tripletGapMat d₁ d₂ d₃).conjTranspose =
      dNormSq d₁ d₂ d₃ • 1 +
        nonUnitaryQ1 d₁ d₂ d₃ • pauliX +
        nonUnitaryQ2 d₁ d₂ d₃ • pauliY +
        nonUnitaryQ3 d₁ d₂ d₃ • pauliZ) ∧
    (nonUnitaryQ1 (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) = 0 ∧
      nonUnitaryQ2 (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) = 0 ∧
      nonUnitaryQ3 (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) = 0 ∧
      tripletGapMat (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) *
          (tripletGapMat (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ)).conjTranspose =
        (((r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 : ℝ) : ℂ)) • 1) ∧
    (dNormSq (m : ℂ) (Complex.I * (m : ℂ)) 0 = 2 * ((m : ℂ) ^ 2) ∧
      dNormSq (m : ℂ) (Complex.I * (m : ℂ)) 0 ≠ 0 ∧
      ∃ ψ : Fin 2 ⊕ Fin 2 → ℂ, ψ ≠ 0 ∧
        (tripletBdG4 0 (m : ℂ) (Complex.I * (m : ℂ)) 0).mulVec ψ = 0) := by
  have hSym : (tripletGapMat d₁ d₂ d₃)ᵀ = tripletGapMat d₁ d₂ d₃ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tripletGapMat]
  have hProd : tripletGapMat d₁ d₂ d₃ * (tripletGapMat d₁ d₂ d₃).conjTranspose =
      dNormSq d₁ d₂ d₃ • 1 +
        nonUnitaryQ1 d₁ d₂ d₃ • pauliX +
        nonUnitaryQ2 d₁ d₂ d₃ • pauliY +
        nonUnitaryQ3 d₁ d₂ d₃ • pauliZ :=
    tripletGapMat_mul_conjTranspose d₁ d₂ d₃
  have hReal : nonUnitaryQ1 (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) = 0 ∧
      nonUnitaryQ2 (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) = 0 ∧
      nonUnitaryQ3 (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) = 0 ∧
      tripletGapMat (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) *
          (tripletGapMat (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ)).conjTranspose =
        (((r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 : ℝ) : ℂ)) • 1 := by
    have hq1 : nonUnitaryQ1 (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) = 0 := by
      simp [nonUnitaryQ1, mul_comm]
    have hq2 : nonUnitaryQ2 (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) = 0 := by
      simp [nonUnitaryQ2, mul_comm]
    have hq3 : nonUnitaryQ3 (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ) = 0 := by
      simp [nonUnitaryQ3, mul_comm]
    refine ⟨hq1, hq2, hq3, ?_⟩
    have hR := tripletGapMat_mul_conjTranspose (r₁ : ℂ) (r₂ : ℂ) (r₃ : ℂ)
    rw [hq1, hq2, hq3, zero_smul, zero_smul, zero_smul, add_zero, add_zero, add_zero] at hR
    rw [hR]
    congr 1
    simp [dNormSq, sq]
  have hChiral : dNormSq (m : ℂ) (Complex.I * (m : ℂ)) 0 = 2 * ((m : ℂ) ^ 2) ∧
      dNormSq (m : ℂ) (Complex.I * (m : ℂ)) 0 ≠ 0 ∧
      ∃ ψ : Fin 2 ⊕ Fin 2 → ℂ, ψ ≠ 0 ∧
        (tripletBdG4 0 (m : ℂ) (Complex.I * (m : ℂ)) 0).mulVec ψ = 0 := by
    have hnorm : dNormSq (m : ℂ) (Complex.I * (m : ℂ)) 0 = 2 * ((m : ℂ) ^ 2) := by
      dsimp [dNormSq]
      exact scalar_nonunitary_chiral_norm m
    have hnz_norm : dNormSq (m : ℂ) (Complex.I * (m : ℂ)) 0 ≠ 0 := by
      rw [hnorm]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hm))
    refine ⟨hnorm, hnz_norm, Sum.elim ![0, 1] 0, ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun v : Fin 2 ⊕ Fin 2 → ℂ => v (Sum.inl 1)) h
      norm_num at h1
    · ext x
      cases x with
      | inl i =>
        simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
          Pi.zero_apply, Sum.elim_inl, Sum.elim_inr]
        fin_cases i <;>
          dsimp [tripletBdG4] <;>
          simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply,
            Matrix.one_apply, smul_eq_mul, Complex.ofReal_zero, zero_mul, mul_zero, add_zero,
            zero_add, Pi.zero_apply]
      | inr j =>
        simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
          Pi.zero_apply, Sum.elim_inl, Sum.elim_inr]
        fin_cases j
        · dsimp [tripletBdG4, tripletGapMat]
          simp [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.conjTranspose_apply]
        · dsimp [tripletBdG4, tripletGapMat]
          simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
            Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
            Complex.ofReal_zero, neg_zero, zero_mul, mul_zero, add_zero, zero_add,
            Pi.zero_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, mul_one]
          exact scalar_chiral_zero_col2_conj m
  exact ⟨hSym, hProd, hReal, hChiral⟩

/-! ### Part 4: Doubled Minkowski Krein-Metric Instability & Krein-Collision Phase Transition -/

/-- Real `2 × 2` skew-involution `ε = [[0, 1], [-1, 0]]` (`ε² = -I₂`). -/
def eps2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Off-diagonal sheet-mixing boost generator `G = X ⊗ (g I₄)` on signature-`(4,4)` doubled
Minkowski space (`𝒦_diag = Z ⊗ η_{1,3}`). -/
def sheetBoostGen (g : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  xMir2 ⊗ₖ (g • (1 : Matrix (Fin 4) (Fin 4) ℝ))

/-- Finite `𝒦_diag`-unitary sheet-boost flow `exp(t G) = cosh(g t) I + sinh(g t) (X ⊗ I₄)`. -/
def sheetBoostFlow (g t : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  Real.cosh (g * t) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) +
    Real.sinh (g * t) • (xMir2 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ))

/-- Equal-amplitude Krein-null vector across the opposite-signature sheets `N₊ ⊕ N₋`. -/
def nullRunawayVec : Fin 2 × Fin 4 → ℝ :=
  fun p => if p.2 = 0 then 1 else 0

/-- Signature-`(2,2)` doubled spin-frame Krein metric `K = Z ⊗ I₂`. -/
def kreinSpin22 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  zCut2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Counter-rotating + sheet-mixing `K`-skew-symmetric generator
`A(Ω, g) = Z ⊗ (Ω ε) + X ⊗ (g I₂)` exhibiting Krein collision when `|g| ≥ |Ω|`. -/
def kreinCollisionOp (Ω g : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  zCut2 ⊗ₖ (Ω • eps2) + xMir2 ⊗ₖ (g • (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem exists_noncomm_mat2_real_spin :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨zCut2, xMir2, zCut2_xMir2_noncomm⟩

/-- Explicit non-commutativity witness on `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ`. -/
theorem exists_noncomm_mat2x2_real :
    ∃ A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨kreinSpin22, kreinCollisionOp 0 1, fun h => ?_⟩
  have h0 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ => M (0, 0) (1, 0)) h
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] at h0
  dsimp [kreinSpin22, kreinCollisionOp] at h0
  simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul] at h0
  dsimp [zCut2, xMir2, eps2] at h0
  norm_num at h0

private lemma zCut2_sq_real : zCut2 * zCut2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zCut2, Matrix.mul_apply, Fin.sum_univ_two]

private lemma xMir2_sq_real : xMir2 * xMir2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [xMir2, Matrix.mul_apply, Fin.sum_univ_two]

private lemma eps2_sq_real : eps2 * eps2 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eps2, Matrix.mul_apply, Fin.sum_univ_two]

private lemma zCut2_xMir2_anticomm_real : zCut2 * xMir2 + xMir2 * zCut2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zCut2, xMir2, Matrix.mul_apply, Fin.sum_univ_two]

private lemma transpose_kronecker_fin {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rfl

private lemma scalar_krein_cs_cancel (c s lam : ℝ) :
    (c * c + -(s * c)) + (c * s + -(s * s * lam)) = c * c - s * s * lam := by
  ring

private lemma scalar_hyp_eig_coeff (g Ω γ : ℝ) (hγ : γ ^ 2 = g ^ 2 - Ω ^ 2) :
    (g ^ 2 - Ω ^ 2) = γ * γ := by
  rw [← hγ, sq]

private lemma scalar_hyp_exp_factor (γ t : ℝ) (hγ_ne : γ ≠ 0) :
    Real.cosh (γ * t) + (Real.sinh (γ * t) / γ) * γ = Real.exp (γ * t) := by
  rw [div_mul_cancel₀ _ hγ_ne]
  exact scalar_cosh_add_sinh (γ * t)

private lemma scalar_krein_skew_entry (Ω g : ℝ) :
    (Ω * 1 + -g * 0) + (Ω * (-1) + g * 0) = 0 ∧
    (0 * Ω + g * 1) + (0 * (-Ω) + g * (-1)) = 0 ∧
    (0 * (-Ω) + g * (-1)) + (0 * Ω + g * 1) = 0 := by
  constructor
  · ring
  · constructor <;> ring

private lemma krein_affine_flow_preserve {α : Type*} [Fintype α] [DecidableEq α]
    (K A : Matrix α α ℝ)
    (hK_sym : Kᵀ = K)
    (hSkew : K * A + Aᵀ * K = 0)
    (lam : ℝ) (hSq : A * A = lam • 1)
    (c s : ℝ) (hcs : c * c - s * s * lam = 1) :
    (c • 1 + s • A)ᵀ * K * (c • 1 + s • A) = K := by
  have hAK : Aᵀ * K = -(K * A) := eq_neg_of_add_eq_zero_right hSkew
  have hAKA : Aᵀ * K * A = (-lam) • K := by
    rw [hAK, neg_mul, Matrix.mul_assoc, hSq, Matrix.mul_smul, Matrix.mul_one, ← neg_smul]
  have hmid : (c * s) • (K * A) + (s * c) • (Aᵀ * K) = 0 := by
    rw [hAK, smul_neg, mul_comm c s, add_neg_cancel]
  have hK_used : Kᵀ = K := hK_sym
  calc
    (c • 1 + s • A)ᵀ * K * (c • 1 + s • A)
        = (c • 1 + s • Aᵀ) * (c • K + s • (K * A)) := by
          rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
            Matrix.transpose_smul, Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_smul,
            Matrix.mul_one, Matrix.mul_smul]
    _ = ((c * c) • K + (c * s) • (K * A)) +
          ((s * c) • (Aᵀ * K) + (s * s) • (Aᵀ * K * A)) := by
          rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, smul_mul_assoc,
            mul_smul_comm, Matrix.one_mul, smul_smul, smul_mul_assoc,
            mul_smul_comm, Matrix.one_mul, smul_smul, smul_mul_assoc,
            mul_smul_comm, smul_smul, smul_mul_assoc, mul_smul_comm,
            smul_smul, ← Matrix.mul_assoc]
    _ = (c * c) • K + ((c * s) • (K * A) + (s * c) • (Aᵀ * K)) + (s * s) • (Aᵀ * K * A) := by
          abel
    _ = (c * c - s * s * lam) • K := by
          rw [hmid, add_zero, hAKA, smul_smul, ← add_smul, mul_neg, ← sub_eq_add_neg]
    _ = K := by
          rw [hcs, one_smul]

private lemma kreinCollisionOp_skew (Ω g : ℝ) :
    kreinSpin22 * kreinCollisionOp Ω g + (kreinCollisionOp Ω g)ᵀ * kreinSpin22 = 0 := by
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.zero_apply]
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    dsimp [kreinSpin22, kreinCollisionOp] <;>
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul] <;>
    dsimp [zCut2, xMir2, eps2] <;>
    norm_num

private lemma kreinCollisionOp_sq (Ω g : ℝ) :
    kreinCollisionOp Ω g * kreinCollisionOp Ω g = (g ^ 2 - Ω ^ 2) • 1 := by
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    dsimp [kreinCollisionOp] <;>
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul] <;>
    dsimp [zCut2, xMir2, eps2] <;>
    norm_num
  all_goals first
    | (norm_num; done)
    | (rw [← sq, ← sq]; first | rw [← sub_eq_add_neg] | (rw [add_comm, ← sub_eq_add_neg]))
    | (rw [mul_comm Ω g]; first | exact add_neg_cancel _ | exact neg_add_cancel _)
    | (rw [mul_comm g Ω]; first | exact add_neg_cancel _ | exact neg_add_cancel _)

/-- **Theorem 4A (Doubled Minkowski `(4,4)` Sheet-Boost Krein Instability)**:
On `(Fin 2 × Fin 4 → ℝ, 𝒦_diag = Z ⊗ η_{1,3})`, the off-diagonal sheet-mixing generator `G = X ⊗ g I₄`
is `𝒦_diag`-skew-symmetric (`𝒦_diag G + Gᵀ 𝒦_diag = 0`), squares to `+ g² I` (real spectrum!),
generates an exact `𝒦_diag`-isometric flow `exp(t G)`, and drives the Krein-null vector
`nullRunawayVec` (`⟨v, 𝒦_diag v⟩ = 0`) to exponential blowup `exp(g t) v`. -/
theorem doubled_minkowski_sheet_boost_instability (g t : ℝ) :
    (doubledMinkowskiDiag * sheetBoostGen g + (sheetBoostGen g)ᵀ * doubledMinkowskiDiag = 0) ∧
    (sheetBoostGen g * sheetBoostGen g = (g ^ 2) • 1) ∧
    ((sheetBoostFlow g t)ᵀ * doubledMinkowskiDiag * sheetBoostFlow g t = doubledMinkowskiDiag) ∧
    (dotProduct nullRunawayVec (doubledMinkowskiDiag.mulVec nullRunawayVec) = 0 ∧
      (sheetBoostGen g).mulVec nullRunawayVec = g • nullRunawayVec ∧
      (sheetBoostFlow g t).mulVec nullRunawayVec = Real.exp (g * t) • nullRunawayVec) := by
  have hSkew : doubledMinkowskiDiag * sheetBoostGen g +
      (sheetBoostGen g)ᵀ * doubledMinkowskiDiag = 0 := by
    have hXt : xMir2ᵀ = xMir2 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [xMir2]
    have hM : minkowski4 * (g • (1 : Matrix (Fin 4) (Fin 4) ℝ)) = g • minkowski4 := by
      rw [Matrix.mul_smul, Matrix.mul_one]
    have hMt : (g • (1 : Matrix (Fin 4) (Fin 4) ℝ))ᵀ * minkowski4 = g • minkowski4 := by
      rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul]
    unfold doubledMinkowskiDiag sheetBoostGen
    rw [transpose_kronecker_fin, hXt, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hM, hMt]
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply]
    have hAnti := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b) zCut2_xMir2_anticomm_real
    simp only [Matrix.add_apply, Matrix.zero_apply] at hAnti
    calc
      (zCut2 * xMir2) a b * (g * minkowski4 i j) + (xMir2 * zCut2) a b * (g * minkowski4 i j)
          = ((zCut2 * xMir2) a b + (xMir2 * zCut2) a b) * (g * minkowski4 i j) := by
            rw [← add_mul]
      _ = 0 := by rw [hAnti, zero_mul]
  have hSq : sheetBoostGen g * sheetBoostGen g = (g ^ 2) • 1 := by
    unfold sheetBoostGen
    rw [← Matrix.mul_kronecker_mul, xMir2_sq_real, smul_mul_assoc, mul_smul_comm,
      Matrix.one_mul, smul_smul, ← sq, Matrix.kronecker_smul, Matrix.one_kronecker_one]
  have hFlowPres : (sheetBoostFlow g t)ᵀ * doubledMinkowskiDiag * sheetBoostFlow g t =
      doubledMinkowskiDiag := by
    have hA0 : doubledMinkowskiDiag * (xMir2 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) +
        (xMir2 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ))ᵀ * doubledMinkowskiDiag = 0 := by
      have hXt : xMir2ᵀ = xMir2 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [xMir2]
      unfold doubledMinkowskiDiag
      rw [transpose_kronecker_fin, hXt, Matrix.transpose_one,
        ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
      ext ⟨a, i⟩ ⟨b, j⟩
      simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.zero_apply]
      have hAnti := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M a b)
        zCut2_xMir2_anticomm_real
      simp only [Matrix.add_apply, Matrix.zero_apply] at hAnti
      rw [← add_mul, hAnti, zero_mul]
    have hA0_sq : (xMir2 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) *
        (xMir2 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) = 1 := by
      rw [← Matrix.mul_kronecker_mul, xMir2_sq_real, Matrix.one_mul, Matrix.one_kronecker_one]
    have hK_sym : doubledMinkowskiDiagᵀ = doubledMinkowskiDiag := by
      have hM : minkowski4ᵀ = minkowski4 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [minkowski4]
      have hZ : zCut2ᵀ = zCut2 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [zCut2]
      unfold doubledMinkowskiDiag
      rw [transpose_kronecker_fin, hZ, hM]
    exact krein_affine_flow_preserve doubledMinkowskiDiag
      (xMir2 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) hK_sym hA0 1 (by rw [hA0_sq, one_smul])
      (Real.cosh (g * t)) (Real.sinh (g * t))
      (by rw [mul_one]; exact scalar_cosh_sq_sub_sinh_sq (g * t))
  have hNull : dotProduct nullRunawayVec (doubledMinkowskiDiag.mulVec nullRunawayVec) = 0 := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_four, doubledMinkowskiDiag, Matrix.kroneckerMap_apply, nullRunawayVec]
    dsimp [zCut2, minkowski4]
    norm_num
  have hGenRun : (sheetBoostGen g).mulVec nullRunawayVec = g • nullRunawayVec := by
    ext ⟨a, i⟩
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four,
      Pi.smul_apply, smul_eq_mul]
    fin_cases a <;> fin_cases i <;>
      dsimp [sheetBoostGen, nullRunawayVec, xMir2] <;>
      simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;>
      norm_num
  have hFlowRun : (sheetBoostFlow g t).mulVec nullRunawayVec =
      Real.exp (g * t) • nullRunawayVec := by
    have hA0Run : (xMir2 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)).mulVec nullRunawayVec =
        nullRunawayVec := by
      ext ⟨a, i⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
        Fin.sum_univ_four]
      fin_cases a <;> fin_cases i <;>
        dsimp [nullRunawayVec, xMir2] <;>
        simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] <;>
        norm_num
    dsimp [sheetBoostFlow]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hA0Run, ← add_smul, scalar_cosh_add_sinh]
  exact ⟨hSkew, hSq, hFlowPres, hNull, hGenRun, hFlowRun⟩

/-- **Theorem 4B (Krein-Collision Phase Transition Across Counter-Rotating Spin Frames)**:
For `A(Ω, g) = Z ⊗ (Ω ε) + X ⊗ (g I₂)` on signature-`(2,2)` spin space `K = Z ⊗ I₂`:
1. `A(Ω, g)` is `K`-skew-symmetric and satisfies `A(Ω, g)² = (g² - Ω²) • 1`.
2. **Krein-collision threshold (`g = Ω ≠ 0`)**: `A(Ω, Ω) ≠ 0` yet `A(Ω, Ω)² = 0` (Jordan block!),
   with `K`-preserving secular polynomial flow `1 + t A(Ω, Ω)`.
3. **Hyperbolic runaway (`|Ω| < |g|`, `γ = √(g² - Ω²) > 0`)**: `K`-preserving hyperbolic flow
   drives an explicit nonzero eigenvector `v_run` at exponential growth `exp(γ t) v_run`.
4. **Elliptic bounded precession (`|g| < |Ω|`, `ω = √(Ω² - g²) > 0`)**: `K`-preserving
   oscillatory orthogonal flow with inverse `cos(ω t) I - (sin(ω t) / ω) A`. -/
theorem krein_collision_phase_transition (Ω g t : ℝ) :
    (kreinSpin22 * kreinCollisionOp Ω g + (kreinCollisionOp Ω g)ᵀ * kreinSpin22 = 0) ∧
    (kreinCollisionOp Ω g * kreinCollisionOp Ω g = (g ^ 2 - Ω ^ 2) • 1) ∧
    (Ω ≠ 0 →
      kreinCollisionOp Ω Ω ≠ 0 ∧
      kreinCollisionOp Ω Ω * kreinCollisionOp Ω Ω = 0 ∧
      (1 + t • kreinCollisionOp Ω Ω)ᵀ * kreinSpin22 * (1 + t • kreinCollisionOp Ω Ω) =
        kreinSpin22) ∧
    (|Ω| < |g| →
      let γ := Real.sqrt (g ^ 2 - Ω ^ 2)
      let U_hyp := Real.cosh (γ * t) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) +
        (Real.sinh (γ * t) / γ) • kreinCollisionOp Ω g
      let v_run := (kreinCollisionOp Ω g + γ • 1).mulVec (fun p => if p = (0, 0) then 1 else 0)
      0 < γ ∧
      U_hypᵀ * kreinSpin22 * U_hyp = kreinSpin22 ∧
      v_run ≠ 0 ∧
      (kreinCollisionOp Ω g).mulVec v_run = γ • v_run ∧
      U_hyp.mulVec v_run = Real.exp (γ * t) • v_run) ∧
    (|g| < |Ω| →
      let ω := Real.sqrt (Ω ^ 2 - g ^ 2)
      let U_ell := Real.cos (ω * t) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) +
        (Real.sin (ω * t) / ω) • kreinCollisionOp Ω g
      let U_inv := Real.cos (ω * t) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) -
        (Real.sin (ω * t) / ω) • kreinCollisionOp Ω g
      0 < ω ∧
      U_ellᵀ * kreinSpin22 * U_ell = kreinSpin22 ∧
      U_ell * U_inv = 1) := by
  have hSkew := kreinCollisionOp_skew Ω g
  have hSq := kreinCollisionOp_sq Ω g
  have hK_sym : kreinSpin22ᵀ = kreinSpin22 := by
    have hZ : zCut2ᵀ = zCut2 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [zCut2]
    unfold kreinSpin22
    rw [transpose_kronecker_fin, hZ, Matrix.transpose_one]
  have hJordan : Ω ≠ 0 →
      kreinCollisionOp Ω Ω ≠ 0 ∧
      kreinCollisionOp Ω Ω * kreinCollisionOp Ω Ω = 0 ∧
      (1 + t • kreinCollisionOp Ω Ω)ᵀ * kreinSpin22 * (1 + t • kreinCollisionOp Ω Ω) =
        kreinSpin22 := by
    intro hΩ
    have hnz : kreinCollisionOp Ω Ω ≠ 0 := by
      intro h
      have h01 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ =>
        M (0, 0) (0, 1)) h
      simp only [kreinCollisionOp, Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, Matrix.zero_apply] at h01
      dsimp [zCut2, xMir2, eps2] at h01
      norm_num at h01
      exact hΩ h01
    have hnilp : kreinCollisionOp Ω Ω * kreinCollisionOp Ω Ω = 0 := by
      have h1 := kreinCollisionOp_sq Ω Ω
      rw [sub_self, zero_smul] at h1
      exact h1
    have hSec : (1 + t • kreinCollisionOp Ω Ω)ᵀ * kreinSpin22 * (1 + t • kreinCollisionOp Ω Ω) =
        kreinSpin22 := by
      have h1 : (1 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) +
          t • kreinCollisionOp Ω Ω = 1 + t • kreinCollisionOp Ω Ω := by rw [one_smul]
      rw [← h1]
      exact krein_affine_flow_preserve kreinSpin22 (kreinCollisionOp Ω Ω) hK_sym
        (kreinCollisionOp_skew Ω Ω) 0 (by rw [hnilp, zero_smul]) 1 t (by norm_num)
    exact ⟨hnz, hnilp, hSec⟩
  have hHyp : |Ω| < |g| →
      let γ := Real.sqrt (g ^ 2 - Ω ^ 2)
      let U_hyp := Real.cosh (γ * t) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) +
        (Real.sinh (γ * t) / γ) • kreinCollisionOp Ω g
      let v_run := (kreinCollisionOp Ω g + γ • 1).mulVec (fun p => if p = (0, 0) then 1 else 0)
      0 < γ ∧
      U_hypᵀ * kreinSpin22 * U_hyp = kreinSpin22 ∧
      v_run ≠ 0 ∧
      (kreinCollisionOp Ω g).mulVec v_run = γ • v_run ∧
      U_hyp.mulVec v_run = Real.exp (γ * t) • v_run := by
    intro hlt
    have hdiff_pos : 0 < g ^ 2 - Ω ^ 2 := sub_pos.mpr (sq_lt_sq.mpr hlt)
    set γ := Real.sqrt (g ^ 2 - Ω ^ 2)
    have hγ_pos : 0 < γ := Real.sqrt_pos.mpr hdiff_pos
    have hγ_ne : γ ≠ 0 := hγ_pos.ne'
    have hγ_sq : γ ^ 2 = g ^ 2 - Ω ^ 2 := Real.sq_sqrt hdiff_pos.le
    set U_hyp := Real.cosh (γ * t) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) +
      (Real.sinh (γ * t) / γ) • kreinCollisionOp Ω g
    let e00 : Fin 2 × Fin 2 → ℝ := fun p => if p = (0, 0) then 1 else 0
    set v_run := (kreinCollisionOp Ω g + γ • 1).mulVec e00
    have hPres : U_hypᵀ * kreinSpin22 * U_hyp = kreinSpin22 :=
      krein_affine_flow_preserve kreinSpin22 (kreinCollisionOp Ω g) hK_sym hSkew
        (g ^ 2 - Ω ^ 2) hSq (Real.cosh (γ * t)) (Real.sinh (γ * t) / γ)
        (scalar_hyp_norm_preserve g Ω γ t hγ_sq hγ_ne)
    have hv_nz : v_run ≠ 0 := by
      intro hv0
      have hv00 := congrArg (fun v => v (0, 0)) hv0
      dsimp [v_run, e00] at hv00
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Pi.zero_apply] at hv00
      dsimp [kreinCollisionOp] at hv00
      simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul] at hv00
      dsimp [zCut2, xMir2, eps2] at hv00
      norm_num at hv00
      exact hγ_ne hv00
    have hEig : (kreinCollisionOp Ω g).mulVec v_run = γ • v_run := by
      dsimp [v_run]
      rw [Matrix.mulVec_mulVec, Matrix.mul_add, hSq, Matrix.mul_smul, Matrix.mul_one,
        scalar_hyp_eig_coeff g Ω γ hγ_sq, ← smul_smul, ← smul_add,
        Matrix.smul_mulVec, add_comm (kreinCollisionOp Ω g) (γ • 1)]
    have hExp : U_hyp.mulVec v_run = Real.exp (γ * t) • v_run := by
      dsimp [U_hyp]
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        hEig, smul_smul, ← add_smul, scalar_hyp_exp_factor γ t hγ_ne]
    exact ⟨hγ_pos, hPres, hv_nz, hEig, hExp⟩
  have hEll : |g| < |Ω| →
      let ω := Real.sqrt (Ω ^ 2 - g ^ 2)
      let U_ell := Real.cos (ω * t) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) +
        (Real.sin (ω * t) / ω) • kreinCollisionOp Ω g
      let U_inv := Real.cos (ω * t) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) -
        (Real.sin (ω * t) / ω) • kreinCollisionOp Ω g
      0 < ω ∧
      U_ellᵀ * kreinSpin22 * U_ell = kreinSpin22 ∧
      U_ell * U_inv = 1 := by
    intro hlt
    have hdiff_pos : 0 < Ω ^ 2 - g ^ 2 := sub_pos.mpr (sq_lt_sq.mpr hlt)
    set ω := Real.sqrt (Ω ^ 2 - g ^ 2)
    have hω_pos : 0 < ω := Real.sqrt_pos.mpr hdiff_pos
    have hω_ne : ω ≠ 0 := hω_pos.ne'
    have hω_sq : ω ^ 2 = Ω ^ 2 - g ^ 2 := Real.sq_sqrt hdiff_pos.le
    set c := Real.cos (ω * t)
    set s := Real.sin (ω * t) / ω
    set U_ell := c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) + s • kreinCollisionOp Ω g
    set U_inv := c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) - s • kreinCollisionOp Ω g
    have hcs : c * c - s * s * (g ^ 2 - Ω ^ 2) = 1 :=
      scalar_ell_norm_preserve g Ω ω t hω_sq hω_ne
    have hPres : U_ellᵀ * kreinSpin22 * U_ell = kreinSpin22 :=
      krein_affine_flow_preserve kreinSpin22 (kreinCollisionOp Ω g) hK_sym hSkew
        (g ^ 2 - Ω ^ 2) hSq c s hcs
    have hInv : U_ell * U_inv = 1 := by
      dsimp [U_ell, U_inv]
      simp only [Matrix.mul_sub, Matrix.add_mul, smul_mul_assoc, mul_smul_comm,
        Matrix.one_mul, Matrix.mul_one, hSq, smul_add, smul_smul]
      rw [mul_comm s c, ← mul_assoc s s (g ^ 2 - Ω ^ 2),
        add_comm ((c * s) • kreinCollisionOp Ω g)
          ((s * s * (g ^ 2 - Ω ^ 2)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)),
        add_sub_add_right_eq_sub, ← sub_smul, hcs, one_smul]
    exact ⟨hω_pos, hPres, hInv⟩
  exact ⟨hSkew, hSq, hJordan, hHyp, hEll⟩

end InfoGeometry.Canonical.DoubledMinkowskiSpinFrameInstability
