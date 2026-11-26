/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Basic.Real.Sign

/-!
# Native spectral sign of finite Hermitian matrices

The sign is constructed by Mathlib's real continuous functional calculus on
the full matrix algebra over an arbitrary `RCLike` field. Both real and complex
matrices are covered. The finite spectrum makes every scalar function
continuous on that spectrum, including `Real.sign`.

For a Hermitian input, the constructed sign squares to one exactly when the
input is invertible. Commutation with another operator is preserved without
requiring the ambient matrix algebra to be commutative. No diagonalization
data or sign-law certificate is supplied by the caller.

These are pointwise finite-dimensional statements. They do not assert a
uniform spectral gap, smoothness of a parameter family, or lattice locality.
-/

noncomputable section

namespace InfoGeometry.Analysis.MatrixSpectralSign

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- Apply the real scalar sign function through native matrix functional
calculus. On non-Hermitian inputs, the underlying calculus returns zero. -/
def spectralSign (H : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  cfc Real.sign H

/-- The constructed sign is Hermitian, including the calculus's zero value
outside the Hermitian domain. -/
theorem spectralSign_isHermitian (H : Matrix n n 𝕜) :
    (spectralSign H).IsHermitian := by
  change IsSelfAdjoint (cfc Real.sign H)
  exact cfc_predicate Real.sign H

/-- The native spectral theorem identifies the construction with the scalar
signs of the actual eigenvalues in the internally constructed eigenbasis. -/
theorem spectralSign_eq_spectral {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    spectralSign H =
      Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) hH.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ Real.sign ∘ hH.eigenvalues)) := by
  simpa only [spectralSign, Matrix.IsHermitian.cfc] using hH.cfc_eq Real.sign

/-- Invertibility excludes the zero spectral value and makes the actual
spectral sign an involution. -/
theorem spectralSign_mul_self {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (hunit : IsUnit H) :
    spectralSign H * spectralSign H = 1 := by
  have hf : ContinuousOn Real.sign (spectrum ℝ H) :=
    H.finite_real_spectrum.continuousOn Real.sign
  change cfc Real.sign H * cfc Real.sign H = 1
  rw [← cfc_mul Real.sign Real.sign H hf hf]
  calc
    cfc (fun x : ℝ => Real.sign x * Real.sign x) H =
        cfc (fun _ : ℝ => 1) H := by
      apply cfc_congr
      intro x hx
      have hx0 : x ≠ 0 := by
        intro hzero
        subst x
        exact ((spectrum.zero_notMem_iff ℝ).mpr hunit) hx
      rcases Real.sign_apply_eq_of_ne_zero x hx0 with hs | hs <;> simp [hs]
    _ = 1 := cfc_const_one ℝ H hH.isSelfAdjoint

/-- The invertibility hypothesis is exact: a zero spectral mode prevents
the Hermitian sign from squaring to one. -/
theorem spectralSign_mul_self_eq_one_iff {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) :
    spectralSign H * spectralSign H = 1 ↔ IsUnit H := by
  constructor
  · intro hsquare
    have hsignUnit : IsUnit (spectralSign H) :=
      ⟨⟨spectralSign H, spectralSign H, hsquare, hsquare⟩, rfl⟩
    have hf : ContinuousOn Real.sign (spectrum ℝ H) :=
      H.finite_real_spectrum.continuousOn Real.sign
    have hnonzero :=
      (isUnit_cfc_iff Real.sign H hf hH.isSelfAdjoint).mp hsignUnit
    apply (spectrum.zero_notMem_iff ℝ).mp
    intro hzero
    exact hnonzero 0 hzero Real.sign_zero
  · exact spectralSign_mul_self hH

/-- A Hermitian involution is fixed by the native spectral sign. This gives
concrete inputs to the construction without supplying a separate sign matrix. -/
theorem spectralSign_eq_self_of_mul_self {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (hsquare : H * H = 1) :
    spectralSign H = H := by
  have hpoly : cfc (fun x : ℝ => x ^ 2) H = cfc (fun _ : ℝ => 1) H := by
    rw [cfc_pow_id (R := ℝ) H 2 hH.isSelfAdjoint,
      cfc_const_one ℝ H hH.isSelfAdjoint, pow_two, hsquare]
  have hspectrum := eqOn_of_cfc_eq_cfc hpoly
    (continuousOn_id.pow 2) continuousOn_const hH.isSelfAdjoint
  calc
    spectralSign H = cfc (fun x : ℝ => x) H := by
      apply cfc_congr
      intro x hx
      rcases sq_eq_one_iff.mp (hspectrum hx) with hxone | hxneg
      · rw [hxone, Real.sign_one]
      · rw [hxneg, Real.sign_neg, Real.sign_one]
    _ = H := cfc_id' ℝ H hH.isSelfAdjoint

/-- Functional calculus preserves commutation with an arbitrary operator.
In particular, a real internal phase commuting with `H` commutes with its sign. -/
theorem spectralSign_commute {H B : Matrix n n 𝕜} (hcomm : Commute H B) :
    Commute (spectralSign H) B :=
  hcomm.cfc_real Real.sign

end InfoGeometry.Analysis.MatrixSpectralSign

end
