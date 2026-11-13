/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.RealificationStates
import Mathlib.Analysis.Matrix.Order

/-!
# Tensor composition on the realification image

The operation below transports the complex Kronecker product to real doubled
operators with one shared phase axis. Its output has index `(n × m) ⊕ (n × m)`.
It is therefore not the ordinary real Kronecker product on the ambient doubled
spaces. Multiplicativity, adjoint compatibility, and positivity are asserted
on the image, characterized by commutation with the internal phase axis.

Trace-one states require a factor of two when composed. Local operator actions
are transported exactly; no full real Hilbert-space tensor equivalence is
asserted here.

The total fallback on incompatible inputs uses the first block column. It
does not preserve arbitrary real positivity and is distinct from Appendix E's
positive compression on the larger real tensor space.
-/

noncomputable section

open Matrix
open scoped Kronecker ComplexOrder

namespace InfoGeometry.Quantum.Realification

variable {l m n p : Type*}

@[simp] theorem unrealify_zero :
    unrealify (0 : Matrix (m ⊕ m) (n ⊕ n) ℝ) = 0 := by
  ext i j
  rfl

@[simp] theorem unrealify_add
    (A B : Matrix (m ⊕ m) (n ⊕ n) ℝ) :
    unrealify (A + B) = unrealify A + unrealify B := by
  ext i j
  rfl

@[simp] theorem unrealify_smul (r : ℝ)
    (A : Matrix (m ⊕ m) (n ⊕ n) ℝ) :
    unrealify (r • A) = r • unrealify A := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

@[simp] theorem unrealify_one [DecidableEq n] :
    unrealify (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) = 1 := by
  rw [← realify_one, unrealify_realify]

/-- A composition rule expressed entirely in real blocks. The operation is
 total, but its faithful interpretation is on the complex-linear image. -/
def alignedTensor
    (A : Matrix (m ⊕ m) (n ⊕ n) ℝ)
    (B : Matrix (l ⊕ l) (p ⊕ p) ℝ) :
    Matrix ((m × l) ⊕ (m × l)) ((n × p) ⊕ (n × p)) ℝ :=
  let C := A.toBlocks₁₁ ⊗ₖ B.toBlocks₁₁ - A.toBlocks₂₁ ⊗ₖ B.toBlocks₂₁
  let D := A.toBlocks₁₁ ⊗ₖ B.toBlocks₂₁ + A.toBlocks₂₁ ⊗ₖ B.toBlocks₁₁
  Matrix.fromBlocks C (-D) D C

/-- The independently defined real combination rule agrees with the encoded
complex tensor product. -/
theorem alignedTensor_eq_realify
    (A : Matrix (m ⊕ m) (n ⊕ n) ℝ)
    (B : Matrix (l ⊕ l) (p ⊕ p) ℝ) :
    alignedTensor A B = realify (unrealify A ⊗ₖ unrealify B) := by
  ext i j
  cases i <;> cases j <;>
    simp [alignedTensor, unrealify, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁,
      Matrix.kroneckerMap_apply, Complex.mul_re, Complex.mul_im]

@[simp] theorem alignedTensor_realify (A : Matrix m n ℂ) (B : Matrix l p ℂ) :
    alignedTensor (realify A) (realify B) = realify (A ⊗ₖ B) := by
  simp only [alignedTensor_eq_realify, unrealify_realify]

@[simp] theorem alignedTensor_zero_left
    (B : Matrix (l ⊕ l) (p ⊕ p) ℝ) :
    alignedTensor (0 : Matrix (m ⊕ m) (n ⊕ n) ℝ) B = 0 := by
  simp only [alignedTensor_eq_realify, unrealify_zero, zero_kronecker, realify_zero]

@[simp] theorem alignedTensor_zero_right
    (A : Matrix (m ⊕ m) (n ⊕ n) ℝ) :
    alignedTensor A (0 : Matrix (l ⊕ l) (p ⊕ p) ℝ) = 0 := by
  simp only [alignedTensor_eq_realify, unrealify_zero, kronecker_zero, realify_zero]

theorem alignedTensor_add_left
    (A A' : Matrix (m ⊕ m) (n ⊕ n) ℝ)
    (B : Matrix (l ⊕ l) (p ⊕ p) ℝ) :
    alignedTensor (A + A') B = alignedTensor A B + alignedTensor A' B := by
  simp only [alignedTensor_eq_realify, unrealify_add, add_kronecker, realify_add]

theorem alignedTensor_add_right
    (A : Matrix (m ⊕ m) (n ⊕ n) ℝ)
    (B B' : Matrix (l ⊕ l) (p ⊕ p) ℝ) :
    alignedTensor A (B + B') = alignedTensor A B + alignedTensor A B' := by
  simp only [alignedTensor_eq_realify, unrealify_add, kronecker_add, realify_add]

theorem alignedTensor_smul_left (r : ℝ)
    (A : Matrix (m ⊕ m) (n ⊕ n) ℝ)
    (B : Matrix (l ⊕ l) (p ⊕ p) ℝ) :
    alignedTensor (r • A) B = r • alignedTensor A B := by
  simp only [alignedTensor_eq_realify, unrealify_smul, smul_kronecker, realify_smul]

theorem alignedTensor_smul_right (r : ℝ)
    (A : Matrix (m ⊕ m) (n ⊕ n) ℝ)
    (B : Matrix (l ⊕ l) (p ⊕ p) ℝ) :
    alignedTensor A (r • B) = r • alignedTensor A B := by
  simp only [alignedTensor_eq_realify, unrealify_smul, kronecker_smul, realify_smul]

/-- The composition remains in the image, even for ambient input matrices. -/
theorem alignedTensor_commutes_internalJ [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (B : Matrix (m ⊕ m) (m ⊕ m) ℝ) :
    Commute (alignedTensor A B) internalJ := by
  rw [alignedTensor_eq_realify]
  exact realify_commutes_internalJ _

/-- Reconstructing an ordered product is valid on the complex-linear image. -/
theorem unrealify_mul_of_commute [Fintype n] [DecidableEq n]
    (A B : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (hA : Commute A internalJ) (hB : Commute B internalJ) :
    unrealify (A * B) = unrealify A * unrealify B := by
  calc
    unrealify (A * B) =
        unrealify (realify (unrealify A * unrealify B)) := by
      rw [realify_mul, realify_unrealify_of_commute A hA,
        realify_unrealify_of_commute B hB]
    _ = _ := unrealify_realify _

/-- The mixed-product identity preserves the order inside both factors. -/
theorem alignedTensor_mul [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (A A' : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (B B' : Matrix (m ⊕ m) (m ⊕ m) ℝ)
    (hA : Commute A internalJ) (hA' : Commute A' internalJ)
    (hB : Commute B internalJ) (hB' : Commute B' internalJ) :
    alignedTensor (A * A') (B * B') =
      alignedTensor A B * alignedTensor A' B' := by
  simp only [alignedTensor_eq_realify, unrealify_mul_of_commute A A' hA hA',
    unrealify_mul_of_commute B B' hB hB', mul_kronecker_mul, realify_mul]

/-- Adjoint reconstruction also requires the complex-linear image condition. -/
theorem unrealify_conjTranspose_of_commute [Fintype n] [DecidableEq n]
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (hA : Commute A internalJ) :
    unrealify A.conjTranspose = (unrealify A).conjTranspose := by
  calc
    unrealify A.conjTranspose =
        unrealify (realify (unrealify A).conjTranspose) := by
      rw [realify_star, realify_unrealify_of_commute A hA]
    _ = _ := unrealify_realify _

theorem alignedTensor_conjTranspose [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (B : Matrix (m ⊕ m) (m ⊕ m) ℝ)
    (hA : Commute A internalJ) (hB : Commute B internalJ) :
    alignedTensor A.conjTranspose B.conjTranspose =
      (alignedTensor A B).conjTranspose := by
  simp only [alignedTensor_eq_realify, unrealify_conjTranspose_of_commute A hA,
    unrealify_conjTranspose_of_commute B hB, ← conjTranspose_kronecker,
    realify_star]

/-- Positive encoded inputs compose to a positive encoded operator. -/
theorem alignedTensor_posSemidef [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (B : Matrix (m ⊕ m) (m ⊕ m) ℝ)
    (hA : Commute A internalJ) (hB : Commute B internalJ)
    (hposA : A.PosSemidef) (hposB : B.PosSemidef) :
    (alignedTensor A B).PosSemidef := by
  rw [alignedTensor_eq_realify]
  apply (realify_posSemidef_iff _).mpr
  apply PosSemidef.kronecker
  · apply (realify_posSemidef_iff _).mp
    simpa only [realify_unrealify_of_commute A hA] using hposA
  · apply (realify_posSemidef_iff _).mp
    simpa only [realify_unrealify_of_commute B hB] using hposB

/-- Ordinary trace-one encoding requires a factor two in the transported
product, since each input state already carries a factor one half. -/
theorem state_kronecker (ρ : Matrix n n ℂ) (σ : Matrix m m ℂ) :
    state (ρ ⊗ₖ σ) = (2 : ℝ) • alignedTensor (state ρ) (state σ) := by
  simp only [state, alignedTensor_smul_left, alignedTensor_smul_right,
    alignedTensor_realify, smul_smul]
  norm_num

/-- Both local operator actions are represented by their corresponding
encoded tensor factors, including noncommuting local state/operator pairs. -/
theorem alignedTensor_conjugation_realify [Fintype n] [Fintype m]
    (K ρ : Matrix n n ℂ) (L σ : Matrix m m ℂ) :
    alignedTensor (realify K) (realify L) * state (ρ ⊗ₖ σ) *
        (alignedTensor (realify K) (realify L)).transpose =
      state ((K * ρ * K.conjTranspose) ⊗ₖ (L * σ * L.conjTranspose)) := by
  rw [alignedTensor_realify, ← state_conjugation]
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

/-- Acting on the first subsystem leaves the second input state unchanged. -/
theorem alignedTensor_local_left [Fintype n] [Fintype m] [DecidableEq m]
    (K ρ : Matrix n n ℂ) (σ : Matrix m m ℂ) :
    alignedTensor (realify K) (1 : Matrix (m ⊕ m) (m ⊕ m) ℝ) *
        state (ρ ⊗ₖ σ) *
        (alignedTensor (realify K) (1 : Matrix (m ⊕ m) (m ⊕ m) ℝ)).transpose =
      state ((K * ρ * K.conjTranspose) ⊗ₖ σ) := by
  simpa using alignedTensor_conjugation_realify K ρ (1 : Matrix m m ℂ) σ

/-- The encoded product measurement has exactly the product Born readout
for independent states. Neither local state must commute with its effect. -/
theorem alignedTensor_born_product [Fintype n] [Fintype m]
    (E ρ : Matrix n n ℂ) (F σ : Matrix m m ℂ)
    (hE : E.IsHermitian) (hρ : ρ.IsHermitian)
    (hF : F.IsHermitian) (hσ : σ.IsHermitian) :
    trace (alignedTensor (realify E) (realify F) * state (ρ ⊗ₖ σ)) =
      (trace (E * ρ)).re * (trace (F * σ)).re := by
  rw [alignedTensor_realify, born_readout, ← mul_kronecker_mul, trace_kronecker,
    Complex.mul_re, trace_mul_im_eq_zero hE hρ, trace_mul_im_eq_zero hF hσ]
  ring

end InfoGeometry.Quantum.Realification
