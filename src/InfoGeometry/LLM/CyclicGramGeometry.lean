/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.LLM.ZModFourierBridge
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Centering and cyclic autocorrelation Gram matrices

## i. Overview

The centering matrix is the native matrix `I - N⁻¹ J`. Its two-sided action
on a circulant matrix subtracts the mean of the difference kernel. The
autocorrelation below is unnormalized: it is a sum, not an average, and its
circulant is the actual Gram matrix of cyclically shifted feature rows.
An explicit real two-coordinate Fourier feature matrix realizes a real
character kernel as its Gram matrix with constant squared row norm.

## ii. Key results

- Centering is idempotent, self-adjoint, and subtracts the arithmetic mean.
- Two-sided centering of a circulant subtracts its kernel mean exactly.
- Nontrivial characters are fixed by centering; the constant mode is removed.
- The centered matrix retains original Fourier eigenvalues at nonzero
  frequencies and has eigenvalue zero at the constant mode.
- Native DFT diagonalizes the full centered matrix action.
- Centering preserves positive semidefiniteness via self-adjoint projection.
- The cyclic autocorrelation matrix is the Gram matrix of cyclically
  shifted feature rows, hence positive semidefinite.
- The autocorrelation spectrum is the squared complex Fourier amplitude.
- Centered autocorrelation has the explicit centered shifted-feature
  factorization.
- The real two-coordinate Fourier feature matrix has a real circulant Gram
  matrix with constant squared row norm `a²`.

## iii. Table of contents

- `cyclicCentering` — orthogonal centering matrix `I - N⁻¹ • J`
- `cyclicCentering_mulVec` — centering subtracts the arithmetic mean
- `cyclicCentering_mul_self` — centering is idempotent
- `cyclicCentering_conjTranspose` — centering is self-adjoint
- `cyclicCentering_circulant` — two-sided centering subtracts kernel mean
- `cyclicCentering_mulVec_addChar` — nontrivial characters fixed by centering
- `centered_circulant_mulVec_stdAddChar` — centered eigenvalues
- `centered_circulant_hasEigenvector_stdAddChar` — nonzero eigenvectors
- `dft_centered_circulant_mulVec` — DFT diagonalizes centered action
- `centered_circulant_mulVec_eq_invDFT` — Fourier inversion reconstruction
- `cyclicCentering_posSemidef` — centering preserves positive semidefiniteness
- `cyclicAutocorrelation` — unnormalized cyclic autocorrelation
- `cyclicAutocorrelation_gram` — autocorrelation is a Gram matrix
- `cyclicAutocorrelation_posSemidef` — constructed Gram positivity
- `dft_cyclicAutocorrelation_eq_normSq` — spectrum is squared Fourier amplitude
- `centered_cyclicAutocorrelation_gram` — centered Gram factorization
- `cyclicRealFourierPair` — real two-coordinate Fourier feature matrix
- `cyclicRealFourierPair_gram_eq_circulant` — real Gram is circulant
- `cyclicRealFourierPair_gram_diag` — constant squared row norm `a²`

## iv. References

- arXiv:2602.15029 — "Symmetry in language statistics shapes the geometry of
  model representations" (Karkada, Korchinski, Nava, Wyart, Bahri, ICML 2026)
- QMS-SOP-ALC-001 — Quality Management System

### Three-Bucket Audit Classification

- **BUCKET 1 — Proved Kernel Content:**
  - `cyclicCentering_mulVec`, `cyclicCentering_mul_self`, `cyclicCentering_conjTranspose`, `cyclicCentering_circulant`,
  - `cyclicCentering_mulVec_addChar`, `cyclicCentering_mulVec_stdAddChar`, `centered_circulant_mulVec_stdAddChar`, `centered_circulant_hasEigenvector_stdAddChar`,
  - `dft_centered_circulant_mulVec`, `centered_circulant_mulVec_eq_invDFT`, `cyclicCentering_posSemidef`,
  - `cyclicAutocorrelation_gram`, `cyclicAutocorrelation_posSemidef`, `dft_cyclicAutocorrelation_eq_normSq`, `centered_cyclicAutocorrelation_gram`,
  - `cyclicRealFourierPair_gram_apply`, `cyclicRealFourierPair_gram_eq_circulant`, `cyclicRealFourierPair_gram_diag`.
- **BUCKET 2 — Conditional / Interface Boundaries:**
  - `NeZero N` supplies nonemptiness and invertibility of `(N : ℂ)` in `cyclicCentering N`.
- **BUCKET 3 — Out-of-Scope Empirical Claims:**
  - Empirical corpus statistics and neural training dynamics of arXiv:2602.15029 remain outside this finite cyclic Gram owner.
-/

namespace InfoGeometry.LLM

open Matrix
open scoped ComplexOrder

variable {N : ℕ} [NeZero N]

/-- Orthogonal centering of vectors indexed by the finite cycle. -/
noncomputable def cyclicCentering (N : ℕ) [NeZero N] :
    Matrix (ZMod N) (ZMod N) ℂ :=
  1 - (N : ℂ)⁻¹ • Matrix.circulant (fun _ => 1)

/-- Centering subtracts the same arithmetic mean from each coordinate. -/
lemma cyclicCentering_mulVec (v : ZMod N → ℂ) :
    cyclicCentering N *ᵥ v = fun i => v i - (N : ℂ)⁻¹ * ∑ j, v j := by
  simp only [cyclicCentering, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Every centered vector has coordinate sum zero. -/
lemma sum_cyclicCentering_mulVec (v : ZMod N → ℂ) :
    ∑ i, (cyclicCentering N *ᵥ v) i = 0 := by
  rw [cyclicCentering_mulVec]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N)),
    one_mul, sub_self]

/-- Centering fixes a vector with zero coordinate sum. -/
lemma cyclicCentering_mulVec_of_sum_zero (v : ZMod N → ℂ)
    (hv : ∑ i, v i = 0) : cyclicCentering N *ᵥ v = v := by
  rw [cyclicCentering_mulVec]
  simp [hv]

/-- The fixed vectors of the centering matrix are exactly the zero-sum vectors. -/
lemma cyclicCentering_mulVec_eq_self_iff (v : ZMod N → ℂ) :
    cyclicCentering N *ᵥ v = v ↔ ∑ i, v i = 0 := by
  constructor
  · intro h
    rw [← h]
    exact sum_cyclicCentering_mulVec v
  · exact cyclicCentering_mulVec_of_sum_zero v

/-- The constant mode is removed. -/
lemma cyclicCentering_mulVec_one :
    cyclicCentering N *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  rw [cyclicCentering_mulVec]
  ext i
  simp [ZMod.card, Nat.cast_ne_zero.mpr (NeZero.ne N)]

/-- Centering is idempotent as a full matrix product. -/
lemma cyclicCentering_mul_self :
    cyclicCentering N * cyclicCentering N = cyclicCentering N := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec]
  exact cyclicCentering_mulVec_of_sum_zero _ (sum_cyclicCentering_mulVec v)

/-- The centering matrix is self-adjoint. -/
lemma cyclicCentering_conjTranspose :
    (cyclicCentering N)ᴴ = cyclicCentering N := by
  have hs : star (fun _ : ZMod N => (1 : ℂ)) = (fun _ => (1 : ℂ)) := by
    ext i
    simp
  simp [cyclicCentering, Matrix.conjTranspose_circulant, hs]

/-- Each row sum of a circulant is the sum of its generating kernel. -/
lemma circulant_mul_ones (κ : ZMod N → ℂ) :
    Matrix.circulant κ * Matrix.circulant (fun _ => 1) =
      (∑ a, κ a) • Matrix.circulant (fun _ : ZMod N => (1 : ℂ)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.circulant_apply, mul_one,
    Matrix.smul_apply, smul_eq_mul]
  refine Fintype.sum_equiv (Equiv.subLeft i) _ _ ?_
  intro a
  rfl

/-- Centering commutes with a circulant, without asserting commutation for
arbitrary matrices. -/
lemma cyclicCentering_mul_circulant_comm (κ : ZMod N → ℂ) :
    cyclicCentering N * Matrix.circulant κ =
      Matrix.circulant κ * cyclicCentering N := by
  simp only [cyclicCentering, sub_mul, mul_sub, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [Matrix.circulant_mul_comm]

/-- Two-sided centering subtracts the kernel mean, exactly. -/
lemma cyclicCentering_circulant (κ : ZMod N → ℂ) :
    cyclicCentering N * Matrix.circulant κ * cyclicCentering N =
      Matrix.circulant (fun a => κ a - (N : ℂ)⁻¹ * ∑ b, κ b) := by
  calc
    cyclicCentering N * Matrix.circulant κ * cyclicCentering N =
        Matrix.circulant κ * (cyclicCentering N * cyclicCentering N) := by
      rw [cyclicCentering_mul_circulant_comm, Matrix.mul_assoc]
    _ = Matrix.circulant κ * cyclicCentering N := by
      rw [cyclicCentering_mul_self]
    _ = Matrix.circulant κ - (N : ℂ)⁻¹ •
        ((∑ b, κ b) • Matrix.circulant (fun _ => (1 : ℂ))) := by
      rw [cyclicCentering, mul_sub, mul_one, Matrix.mul_smul, circulant_mul_ones]
    _ = _ := by
      ext i j
      simp

/-- Nontrivial characters have zero mean and are fixed by centering. -/
lemma cyclicCentering_mulVec_addChar (χ : AddChar (ZMod N) ℂ) (hχ : χ ≠ 1) :
    cyclicCentering N *ᵥ (χ : ZMod N → ℂ) = (χ : ZMod N → ℂ) := by
  simpa using cyclicCentering_mulVec_of_sum_zero (χ : ZMod N → ℂ)
    (AddChar.sum_eq_zero_of_ne_one hχ)

/-- Primitivity of the standard character discharges nontriviality at every
nonzero frequency, including the even-cycle Nyquist frequency. -/
lemma cyclicCentering_mulVec_stdAddChar (k : ZMod N) (hk : k ≠ 0) :
    cyclicCentering N *ᵥ (fun i => ZMod.stdAddChar (k * i)) =
      (fun i => ZMod.stdAddChar (k * i)) := by
  have hχ : ((ZMod.stdAddChar (N := N)).mulShift k : ZMod N → ℂ) =
      fun i => ZMod.stdAddChar (k * i) := by
    funext i
    exact AddChar.mulShift_apply
  rw [← hχ]
  exact cyclicCentering_mulVec_addChar ((ZMod.stdAddChar (N := N)).mulShift k)
    (ZMod.isPrimitive_stdAddChar N hk)

/-- The centered matrix has the original Fourier eigenvalues at nonzero
frequencies and eigenvalue zero at the constant mode. -/
lemma centered_circulant_mulVec_stdAddChar (κ : ZMod N → ℂ) (k : ZMod N) :
    (cyclicCentering N * Matrix.circulant κ * cyclicCentering N) *ᵥ
        (fun i => ZMod.stdAddChar (k * i)) =
      (if k = 0 then 0 else ZMod.dft κ k) • (fun i => ZMod.stdAddChar (k * i)) := by
  by_cases hk : k = 0
  · subst k
    simp [← Matrix.mulVec_mulVec, cyclicCentering_mulVec_one]
  · simp only [hk, ↓reduceIte, ← Matrix.mulVec_mulVec,
      cyclicCentering_mulVec_stdAddChar k hk, circulant_mulVec_stdAddChar,
      Matrix.mulVec_smul]

/-- Every standard Fourier character is a nonzero eigenvector of the centered
operator, including the constant character with eigenvalue zero. -/
lemma centered_circulant_hasEigenvector_stdAddChar
    (κ : ZMod N → ℂ) (k : ZMod N) :
    Module.End.HasEigenvector
      (cyclicCentering N * Matrix.circulant κ * cyclicCentering N).mulVecLin
      (if k = 0 then 0 else ZMod.dft κ k) (fun i => ZMod.stdAddChar (k * i)) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨centered_circulant_mulVec_stdAddChar κ k, ?_⟩
  intro hzero
  have h := congrFun hzero 0
  simp only [mul_zero, AddChar.map_zero_eq_one, Pi.zero_apply, one_ne_zero] at h

/-- Subtracting a kernel's mean changes precisely its DC Fourier coefficient. -/
lemma dft_centered_cyclicKernel (κ : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun a => κ a - (N : ℂ)⁻¹ * ∑ b, κ b) k =
      if k = 0 then 0 else ZMod.dft κ k := by
  have h := centered_circulant_mulVec_stdAddChar κ k
  rw [cyclicCentering_circulant, circulant_mulVec_stdAddChar] at h
  have hzero := congrFun h 0
  simpa using hzero

/-- The native DFT diagonalizes the entire centered matrix action. -/
lemma dft_centered_circulant_mulVec (κ v : ZMod N → ℂ) :
    ZMod.dft ((cyclicCentering N * Matrix.circulant κ * cyclicCentering N) *ᵥ v) =
      fun k => (if k = 0 then 0 else ZMod.dft κ k) * ZMod.dft v k := by
  rw [cyclicCentering_circulant, dft_circulant_mulVec]
  ext k
  rw [Pi.mul_apply, dft_centered_cyclicKernel]

/-- Fourier inversion reconstructs the centered matrix action on every
vector; no completeness of a supplied eigenbasis is assumed. -/
lemma centered_circulant_mulVec_eq_invDFT (κ v : ZMod N → ℂ) :
    (cyclicCentering N * Matrix.circulant κ * cyclicCentering N) *ᵥ v =
      ZMod.dft.symm
        (fun k => (if k = 0 then 0 else ZMod.dft κ k) * ZMod.dft v k) := by
  apply ZMod.dft.injective
  rw [ZMod.dft.apply_symm_apply]
  exact dft_centered_circulant_mulVec κ v

/-- Centering preserves positive semidefiniteness through native matrix
congruence by the constructed self-adjoint projection. -/
lemma cyclicCentering_posSemidef (M : Matrix (ZMod N) (ZMod N) ℂ)
    (hM : M.PosSemidef) :
    (cyclicCentering N * M * cyclicCentering N).PosSemidef := by
  simpa [cyclicCentering_conjTranspose] using
    hM.mul_mul_conjTranspose_same (cyclicCentering N)

/-- Unnormalized complex cyclic autocorrelation. -/
noncomputable def cyclicAutocorrelation (g : ZMod N → ℂ) (a : ZMod N) : ℂ :=
  ∑ t, g (a + t) * star (g t)

/-- The autocorrelation difference matrix is the Gram matrix of the rows of
the shifted-feature matrix `circulant g`. -/
lemma cyclicAutocorrelation_gram (g : ZMod N → ℂ) :
    Matrix.circulant (cyclicAutocorrelation g) =
      Matrix.circulant g * (Matrix.circulant g)ᴴ := by
  rw [Matrix.conjTranspose_circulant, Matrix.circulant_mul]
  congr 1
  ext a
  change (∑ t, g (a + t) * star (g t)) =
    ∑ t, g (a - t) * star (g (-t))
  refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ ?_
  intro t
  simp

/-- Positive semidefiniteness is a consequence of the explicit Gram
factorization; it is not a supplied kernel assumption. -/
lemma cyclicAutocorrelation_posSemidef (g : ZMod N → ℂ) :
    (Matrix.circulant (cyclicAutocorrelation g)).PosSemidef := by
  rw [cyclicAutocorrelation_gram]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The unnormalized autocorrelation spectrum is the squared complex
Fourier amplitude. An averaged autocorrelation would include `1/N`. -/
lemma dft_cyclicAutocorrelation (g : ZMod N → ℂ) :
    ZMod.dft (cyclicAutocorrelation g) = ZMod.dft g * star (ZMod.dft g) := by
  have h := cyclicAutocorrelation_gram g
  rw [Matrix.conjTranspose_circulant, Matrix.circulant_mul] at h
  have hk := Matrix.circulant_injective h
  change cyclicAutocorrelation g =
    Matrix.circulant g *ᵥ (fun a => star (g (-a))) at hk
  rw [hk, dft_circulant_mulVec, dft_star_comp_neg]

/-- The autocorrelation Fourier eigenvalue is explicitly a real nonnegative
squared norm. -/
lemma dft_cyclicAutocorrelation_eq_normSq (g : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (cyclicAutocorrelation g) k = (Complex.normSq (ZMod.dft g k) : ℂ) := by
  rw [dft_cyclicAutocorrelation]
  exact Complex.mul_conj (ZMod.dft g k)

/-- Centered autocorrelation has the explicit centered shifted-feature
factorization, preserving the order of the matrix products. -/
lemma centered_cyclicAutocorrelation_gram (g : ZMod N → ℂ) :
    cyclicCentering N * Matrix.circulant (cyclicAutocorrelation g) * cyclicCentering N =
      (cyclicCentering N * Matrix.circulant g) *
        (cyclicCentering N * Matrix.circulant g)ᴴ := by
  rw [cyclicAutocorrelation_gram, Matrix.conjTranspose_mul,
    cyclicCentering_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- A native real feature matrix with the real and imaginary coordinates of
the cyclic Fourier character of frequency `k`, scaled by `a`. -/
noncomputable def cyclicRealFourierPair (a : ℝ) (k : ZMod N) :
    Matrix (ZMod N) (Fin 2) ℝ :=
  fun i => ![a * (ZMod.stdAddChar (k * i)).re,
    a * (ZMod.stdAddChar (k * i)).im]

/-- The real feature Gram matrix is a difference kernel obtained from the
real part of the native cyclic character. -/
lemma cyclicRealFourierPair_gram_apply (a : ℝ) (k i j : ZMod N) :
    (cyclicRealFourierPair a k * (cyclicRealFourierPair a k).transpose) i j =
      a ^ 2 * (ZMod.stdAddChar (k * (i - j))).re := by
  have hstar (x : ZMod N) : star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    have hN : 0 < ringChar (ZMod N) := by
      rw [ZMod.ringChar_zmod_n]
      exact Nat.pos_of_ne_zero (NeZero.ne N)
    simpa only [AddChar.inv_apply, starRingEnd_apply] using
      (AddChar.starComp_apply (φ := ZMod.stdAddChar) hN x)
  have hmul : ZMod.stdAddChar (k * i) * star (ZMod.stdAddChar (k * j)) =
      ZMod.stdAddChar (k * (i - j)) := by
    rw [hstar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hre :
      (ZMod.stdAddChar (k * i)).re * (ZMod.stdAddChar (k * j)).re +
        (ZMod.stdAddChar (k * i)).im * (ZMod.stdAddChar (k * j)).im =
      (ZMod.stdAddChar (k * (i - j))).re := by
    simpa only [Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, mul_neg, sub_neg_eq_add] using congrArg Complex.re hmul
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  change
    (a * (ZMod.stdAddChar (k * i)).re) * (a * (ZMod.stdAddChar (k * j)).re) +
      (a * (ZMod.stdAddChar (k * i)).im) * (a * (ZMod.stdAddChar (k * j)).im) =
    a ^ 2 * (ZMod.stdAddChar (k * (i - j))).re
  rw [← hre]
  ring

/-- The full real Gram matrix is the native circulant associated with the
scaled real character kernel. -/
lemma cyclicRealFourierPair_gram_eq_circulant (a : ℝ) (k : ZMod N) :
    cyclicRealFourierPair a k * (cyclicRealFourierPair a k).transpose =
      Matrix.circulant (fun i => a ^ 2 * (ZMod.stdAddChar (k * i)).re) := by
  ext i j
  exact cyclicRealFourierPair_gram_apply a k i j

/-- Every row has squared Euclidean length `a²`, read directly from the
diagonal of its real Gram matrix. -/
lemma cyclicRealFourierPair_gram_diag (a : ℝ) (k i : ZMod N) :
    (cyclicRealFourierPair a k * (cyclicRealFourierPair a k).transpose) i i =
      a ^ 2 := by
  rw [cyclicRealFourierPair_gram_apply]
  simp only [sub_self, mul_zero, AddChar.map_zero_eq_one, Complex.one_re, mul_one]

end InfoGeometry.LLM
