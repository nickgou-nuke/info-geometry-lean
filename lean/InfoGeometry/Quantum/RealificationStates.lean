/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.Realification
import InfoGeometry.Signal.ComplexRealification
import Mathlib.Analysis.Complex.Order

/-!
# Positive states and Born readout under realification

The native positive-semidefinite cone is preserved and reflected in every
finite dimension. States carry a factor `1/2`; effects do not. Consequently
Born readout is preserved and ordinary trace-square purity is halved.
The proofs act on the full matrix algebra and require no commutation of
the state with the effect.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace InfoGeometry.Quantum.Realification

variable {m n : Type*}

/-- Real coordinates of a vector, with the same phase order as `realify`. -/
def realifyVector (z : n → ℂ) : n ⊕ n → ℝ :=
  Sum.elim (fun i => (z i).re) (fun i => (z i).im)

/-- Reconstruct a complex vector from its two real coordinate blocks. -/
def unrealifyVector (x : n ⊕ n → ℝ) : n → ℂ :=
  fun i => ⟨x (Sum.inl i), x (Sum.inr i)⟩

@[simp] theorem realifyVector_unrealifyVector (x : n ⊕ n → ℝ) :
    realifyVector (unrealifyVector x) = x := by
  funext i
  cases i <;> rfl

@[simp] theorem unrealifyVector_realifyVector (z : n → ℂ) :
    unrealifyVector (realifyVector z) = z := by
  funext i
  exact Complex.eta _

/-- The realified matrix acts on the existing real and imaginary coordinates. -/
theorem realify_mulVec [Fintype n] (A : Matrix m n ℂ) (z : n → ℂ) :
    realify A *ᵥ realifyVector z = realifyVector (A *ᵥ z) := by
  ext i
  cases i <;>
    simp [realifyVector, mulVec, dotProduct, Fintype.sum_sum_type,
      Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring

/-- The paired-plane Hermitian readout owner supplies the scalar pairing. -/
theorem dotProduct_realifyVector [Fintype n] (x y : n → ℂ) :
    realifyVector x ⬝ᵥ realifyVector y = (star x ⬝ᵥ y).re := by
  calc
    realifyVector x ⬝ᵥ realifyVector y =
        InfoGeometry.Signal.ComplexRealification.realDot
          (InfoGeometry.Signal.ComplexRealification.realify x)
          (InfoGeometry.Signal.ComplexRealification.realify y) := by
      simp [realifyVector, dotProduct, Fintype.sum_sum_type,
        InfoGeometry.Signal.ComplexRealification.realDot,
        InfoGeometry.Signal.ComplexRealification.realify, Finset.sum_add_distrib]
    _ = (star x ⬝ᵥ y).re :=
      InfoGeometry.Signal.ComplexRealification.hermitian_re_eq_realDot x y

/-- Exact quadratic-form identity; it does not require Hermiticity. -/
theorem quadratic_realify [Fintype n] (A : Matrix n n ℂ) (z : n → ℂ) :
    star (realifyVector z) ⬝ᵥ (realify A *ᵥ realifyVector z) =
      (star z ⬝ᵥ (A *ᵥ z)).re := by
  rw [realify_mulVec]
  simpa using dotProduct_realifyVector z (A *ᵥ z)

/-- Complex Hermitian matrices are exactly real symmetric encoded matrices. -/
theorem realify_isHermitian_iff (A : Matrix n n ℂ) :
    (realify A).IsHermitian ↔ A.IsHermitian := by
  change (realify A).conjTranspose = realify A ↔ A.conjTranspose = A
  rw [← realify_star]
  exact realify_injective.eq_iff

/-- Positivity is preserved and reflected, with the native matrix cone. -/
theorem realify_posSemidef_iff [Fintype n] (A : Matrix n n ℂ) :
    (realify A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro hA
    have hH := (realify_isHermitian_iff A).mp hA.isHermitian
    apply PosSemidef.of_dotProduct_mulVec_nonneg hH
    intro z
    apply Complex.nonneg_iff.mpr
    constructor
    · simpa only [quadratic_realify] using
        hA.dotProduct_mulVec_nonneg (realifyVector z)
    · have h := congrArg Complex.im (hH.star_dotProduct_mulVec_comm z z)
      simp only [Complex.star_def, Complex.conj_im] at h
      exact (eq_zero_of_neg_eq h).symm
  · intro hA
    apply PosSemidef.of_dotProduct_mulVec_nonneg
      ((realify_isHermitian_iff A).mpr hA.isHermitian)
    intro x
    obtain ⟨z, rfl⟩ : ∃ z, realifyVector z = x :=
      ⟨unrealifyVector x, realifyVector_unrealifyVector x⟩
    rw [quadratic_realify]
    exact (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg z)).1

/-- Ordinary real trace-one encoding of a complex state. -/
def state (ρ : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  (1 / 2 : ℝ) • realify ρ

theorem state_injective : Function.Injective (state (n := n)) := by
  intro A B h
  apply realify_injective
  have h' := congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) ℝ => (2 : ℝ) • M) h
  simpa [state, smul_smul] using h'

theorem state_commutes_internalJ [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) : Commute (state ρ) internalJ := by
  change ((1 / 2 : ℝ) • realify ρ) * internalJ =
    internalJ * ((1 / 2 : ℝ) • realify ρ)
  rw [smul_mul_assoc, mul_smul_comm, (realify_commutes_internalJ ρ).eq]

theorem state_posSemidef [Fintype n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) : (state ρ).PosSemidef :=
  ((realify_posSemidef_iff ρ).mpr hρ).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem trace_state [Fintype n] (ρ : Matrix n n ℂ) :
    trace (state ρ) = (trace ρ).re := by
  rw [state, trace_smul, trace_realify]
  simp [smul_eq_mul]

theorem trace_state_eq_one [Fintype n] {ρ : Matrix n n ℂ}
    (hρ : trace ρ = 1) : trace (state ρ) = 1 := by
  rw [trace_state, hρ]
  rfl

/-- Positivity and normalization are actual conclusions, not witness fields. -/
theorem state_density [Fintype n] {ρ : Matrix n n ℂ}
    (hpos : ρ.PosSemidef) (htrace : trace ρ = 1) :
    (state ρ).PosSemidef ∧ trace (state ρ) = 1 :=
  ⟨state_posSemidef hpos, trace_state_eq_one htrace⟩

/-- Every positive trace-one matrix in the compatible real sector has an
explicit complex density preimage. -/
theorem density_preimage [Fintype n] [DecidableEq n]
    (R : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (hJ : Commute R internalJ) (hpos : R.PosSemidef) (htrace : trace R = 1) :
    ∃ ρ : Matrix n n ℂ, ρ.PosSemidef ∧ trace ρ = 1 ∧ state ρ = R := by
  let ρ := (2 : ℝ) • unrealify R
  have henc : state ρ = R := by
    dsimp [ρ, state]
    rw [realify_smul, realify_unrealify_of_commute R hJ]
    norm_num [smul_smul]
  have hposρ : ρ.PosSemidef := by
    apply (realify_posSemidef_iff ρ).mp
    change (realify ((2 : ℝ) • unrealify R)).PosSemidef
    rw [realify_smul, realify_unrealify_of_commute R hJ]
    exact hpos.smul (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨ρ, hposρ, ?_, henc⟩
  apply Complex.ext
  · have h := trace_state ρ
    rw [henc, htrace] at h
    exact h.symm
  · exact (Complex.nonneg_iff.mp hposρ.trace_nonneg).2.symm

/-- Born readout is preserved without a state/effect commutation hypothesis. -/
theorem born_readout [Fintype n] (E ρ : Matrix n n ℂ) :
    trace (realify E * state ρ) = (trace (E * ρ)).re := by
  rw [state, mul_smul_comm, ← realify_mul, trace_smul, trace_realify]
  simp [smul_eq_mul]

/-- Hermitian inputs have a real trace pairing even when they do not commute. -/
theorem trace_mul_im_eq_zero [Fintype n] {E ρ : Matrix n n ℂ}
    (hE : E.IsHermitian) (hρ : ρ.IsHermitian) : (trace (E * ρ)).im = 0 := by
  have h : star (trace (E * ρ)) = trace (E * ρ) := by
    rw [← trace_conjTranspose, conjTranspose_mul, hE.eq, hρ.eq,
      trace_mul_comm]
  have him := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at him
  exact eq_zero_of_neg_eq him

/-- Equality with the original complex Born value, not only its real part. -/
theorem born_readout_complex [Fintype n] {E ρ : Matrix n n ℂ}
    (hE : E.IsHermitian) (hρ : ρ.IsHermitian) :
    Complex.ofReal (trace (realify E * state ρ)) = trace (E * ρ) := by
  apply Complex.ext
  · simpa using born_readout E ρ
  · simpa using (trace_mul_im_eq_zero hE hρ).symm

/-- Encoded ordinary purity has the necessary factor one half. -/
theorem state_purity [Fintype n] (ρ : Matrix n n ℂ) :
    trace (state ρ * state ρ) = (1 / 2 : ℝ) * (trace (ρ * ρ)).re := by
  rw [state, smul_mul_smul, ← realify_mul, trace_smul, trace_realify]
  simp [smul_eq_mul]
  ring

/-- A normalized complex projection has encoded ordinary purity `1/2`. -/
theorem state_purity_of_idempotent [Fintype n] (ρ : Matrix n n ℂ)
    (hid : ρ * ρ = ρ) (htrace : trace ρ = 1) :
    trace (state ρ * state ρ) = (1 / 2 : ℝ) := by
  rw [state_purity, hid, htrace]
  simp

/-- Realification intertwines the actual two-sided operator action. -/
theorem state_conjugation [Fintype n] (U ρ : Matrix n n ℂ) :
    state (U * ρ * U.conjTranspose) =
      realify U * state ρ * (realify U).transpose := by
  simp [state, smul_mul_assoc, mul_smul_comm]

end InfoGeometry.Quantum.Realification
