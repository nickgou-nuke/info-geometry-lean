/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.PositiveBoundaryConditioning
import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Mixed boundary readouts on the full complex matrix algebra

Contract: `readout ρ E A = trace (E * A * ρ) / trace (E * ρ)` is a
complex-linear functional of the inserted operator. Its unitality and the
trace-one ordered product require nonzero overlap. Positive boundary matrices
give a nonnegative overlap, but they need not commute and the readout need not
be real on Hermitian probes. The adjoint defect records this obstruction.

The pure-boundary theorem uses native `Matrix.vecMulVec` and `Matrix.toLin'`
to identify this mixed formula with the existing regular-boundary functional.
No new dyad or partial-trace API is introduced. The totalized quotient at zero
overlap is not asserted to be a normalized probability or a regular weak value.
-/

noncomputable section

namespace InfoGeometry.Quantum.MixedBoundaryReadout

open Matrix
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n]

/-- The bare boundary overlap; an intervening instrument has its own normalizer. -/
def overlap (ρ E : Matrix n n ℂ) : ℂ := trace (E * ρ)

/-- The ordered complex weak readout of two matrix boundaries. -/
def readout (ρ E A : Matrix n n ℂ) : ℂ := trace (E * A * ρ) / overlap ρ E

theorem overlap_swap (ρ E : Matrix n n ℂ) : overlap ρ E = overlap E ρ :=
  Matrix.trace_mul_comm E ρ

/-- The inserted operator varies through a native complex-linear functional. -/
def readoutLinear (ρ E : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] ℂ where
  toFun := readout ρ E
  map_add' A B := by
    simp only [readout, mul_add, add_mul, trace_add, add_div]
  map_smul' z A := by
    simp only [readout, Matrix.mul_smul, Matrix.smul_mul, trace_smul, smul_eq_mul]
    exact mul_div_assoc z _ _

@[simp] theorem readoutLinear_apply (ρ E A : Matrix n n ℂ) :
    readoutLinear ρ E A = readout ρ E A := rfl

theorem readout_add (ρ E A B : Matrix n n ℂ) :
    readout ρ E (A + B) = readout ρ E A + readout ρ E B :=
  (readoutLinear ρ E).map_add A B

theorem readout_smul (ρ E A : Matrix n n ℂ) (z : ℂ) :
    readout ρ E (z • A) = z * readout ρ E A :=
  (readoutLinear ρ E).map_smul z A

/-- The normalized ordered product represents the readout, but need not be Hermitian. -/
def orderedProduct (ρ E : Matrix n n ℂ) : Matrix n n ℂ :=
  (overlap ρ E)⁻¹ • (ρ * E)

theorem trace_orderedProduct_mul (ρ E A : Matrix n n ℂ) :
    trace (orderedProduct ρ E * A) = readout ρ E A := by
  unfold orderedProduct readout
  rw [smul_mul_assoc, trace_smul, trace_mul_cycle E A ρ]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem trace_orderedProduct {ρ E : Matrix n n ℂ} (hd : overlap ρ E ≠ 0) :
    trace (orderedProduct ρ E) = 1 := by
  unfold orderedProduct
  rw [trace_smul, trace_mul_comm ρ E]
  exact inv_mul_cancel₀ hd

theorem star_overlap {ρ E : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hE : E.IsHermitian) :
    star (overlap ρ E) = overlap ρ E := by
  unfold overlap
  rw [← trace_conjTranspose, conjTranspose_mul, hρ.eq, hE.eq]
  exact trace_mul_comm ρ E

/-- Swapping the Hermitian endpoints conjugates the readout and adjoints the probe. -/
theorem star_readout {ρ E : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hE : E.IsHermitian) (A : Matrix n n ℂ) :
    star (readout ρ E A) = readout E ρ (star A) := by
  simp only [readout, star_div₀]
  rw [star_overlap hρ hE, overlap_swap ρ E]
  congr 1
  rw [← trace_conjTranspose]
  simp only [conjTranspose_mul, hρ.eq, hE.eq, Matrix.star_eq_conjTranspose, mul_assoc]

variable [DecidableEq n]

theorem readout_one {ρ E : Matrix n n ℂ} (hd : overlap ρ E ≠ 0) :
    readout ρ E 1 = 1 := by
  simp only [readout, mul_one]
  exact div_self hd

theorem overlap_nonneg {ρ E : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hE : E.PosSemidef) : 0 ≤ overlap ρ E :=
  BoundaryConditioning.trace_pairing_nonneg hE hρ

omit [DecidableEq n] in
theorem overlap_ne_zero_of_re_pos {ρ E : Matrix n n ℂ}
    (hd : 0 < (overlap ρ E).re) : overlap ρ E ≠ 0 := by
  intro hz
  rw [hz, Complex.zero_re] at hd
  exact (lt_irrefl 0) hd

/-- The imaginary obstruction is the native commutator of the two boundaries. -/
theorem readout_star_defect {ρ E A : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hE : E.IsHermitian) (hA : A.IsHermitian) :
    readout ρ E A - star (readout ρ E A) =
      trace (⁅ρ, E⁆ * A) / overlap ρ E := by
  rw [star_readout hρ hE, hA.star_eq]
  unfold readout
  rw [overlap_swap E ρ, ← sub_div]
  congr 1
  rw [trace_mul_cycle E A ρ, trace_mul_cycle ρ A E]
  simp only [Ring.lie_def, sub_mul, trace_sub]

/-- Normalization does not remove the noncommutative Hermiticity obstruction. -/
theorem orderedProduct_isHermitian_iff {ρ E : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hE : E.IsHermitian) (hd : overlap ρ E ≠ 0) :
    (orderedProduct ρ E).IsHermitian ↔ ρ * E = E * ρ := by
  have hz : IsSelfAdjoint (overlap ρ E) := star_overlap hρ hE
  constructor
  · intro h
    have hs := h.smul hz
    have hprod : (ρ * E).IsHermitian := by
      simpa only [orderedProduct, smul_smul, mul_inv_cancel₀ hd, one_smul] using hs
    exact (BoundaryConditioning.product_isHermitian_iff hρ hE).mp hprod
  · intro h
    exact ((BoundaryConditioning.product_isHermitian_iff hρ hE).mpr h).smul hz.inv₀

section PureBoundaries

open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional (RegularBoundaryPair)

omit [DecidableEq n] in
/-- Native outer products give the full transition numerator without choosing a basis. -/
theorem trace_pure_numerator (u v : n → ℂ) (A : Matrix n n ℂ) :
    trace (vecMulVec v (star v) * A * vecMulVec u (star u)) =
      (star v ⬝ᵥ (A *ᵥ u)) * (star u ⬝ᵥ v) := by
  rw [mul_assoc, mul_vecMulVec, vecMulVec_mul_vecMulVec, trace_vecMulVec,
    dotProduct_smul, smul_eq_mul, dotProduct_comm v (star u)]

theorem overlap_pure (u v : n → ℂ) :
    overlap (vecMulVec u (star u)) (vecMulVec v (star v)) =
      (star v ⬝ᵥ u) * (star u ⬝ᵥ v) := by
  simpa only [overlap, mul_one, one_mulVec] using trace_pure_numerator u v (1 : Matrix n n ℂ)

/-- The existing nonzero vector overlap excludes a zero mixed-state denominator. -/
theorem overlap_pure_ne_zero (p : RegularBoundaryPair n) :
    overlap (vecMulVec p.pre (star p.pre)) (vecMulVec p.post (star p.post)) ≠ 0 := by
  have hp : star p.post ⬝ᵥ p.pre ≠ 0 := p.overlap_ne
  have hrev : star p.pre ⬝ᵥ p.post ≠ 0 := by
    rw [Matrix.star_dotProduct]
    simpa using hp
  rw [overlap_pure]
  exact mul_ne_zero hp hrev

/-- The mixed-state formula specializes to the existing arbitrary-dimensional weak functional. -/
theorem readout_pure_eq (p : RegularBoundaryPair n) (A : Matrix n n ℂ) :
    readout (vecMulVec p.pre (star p.pre)) (vecMulVec p.post (star p.post)) A =
      InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional.weakValue p (Matrix.toLin' A) := by
  have hp : star p.post ⬝ᵥ p.pre ≠ 0 := p.overlap_ne
  have hrev : star p.pre ⬝ᵥ p.post ≠ 0 := by
    rw [Matrix.star_dotProduct]
    simpa using hp
  rw [readout, trace_pure_numerator, overlap_pure]
  change ((star p.post ⬝ᵥ (A *ᵥ p.pre)) * (star p.pre ⬝ᵥ p.post)) /
      ((star p.post ⬝ᵥ p.pre) * (star p.pre ⬝ᵥ p.post)) =
    (star p.post ⬝ᵥ (A *ᵥ p.pre)) / (star p.post ⬝ᵥ p.pre)
  exact mul_div_mul_right _ _ hrev

end PureBoundaries

end InfoGeometry.Quantum.MixedBoundaryReadout
