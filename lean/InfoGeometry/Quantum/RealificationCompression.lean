/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.RealificationTensor

/-!
# Positive compression on the full doubled tensor carrier

The common-phase involution is `Jₙ ⊗ₖ Jₘ`, and its negative spectral projector
is `P = (1 - Jₙ ⊗ₖ Jₘ)/2`. This owner constructs the real compression
`P (A ⊗ₖ B) P` on arbitrary doubled real input matrices. Unlike the
first-column reconstruction used in the image composition, this compression
preserves positivity for every pair of positive ambient inputs.

No multiplicativity, trace normalization, rank, or full tensor-equivalence
claim is made for this compression.
-/

noncomputable section

open Matrix
open scoped Kronecker

namespace InfoGeometry.Quantum.Realification

variable {n m : Type*} [DecidableEq n] [DecidableEq m]

/-- The real phase axis is skew-symmetric. -/
theorem internalJ_transpose :
    (internalJ (n := n)).transpose = -internalJ := by
  ext i j
  cases i <;> cases j <;> simp [internalJ, Matrix.one_apply, eq_comm]

/-- The two local phase axes define an involution on the full real product. -/
def phaseInvolution :
    Matrix ((n ⊕ n) × (m ⊕ m)) ((n ⊕ n) × (m ⊕ m)) ℝ :=
  internalJ ⊗ₖ internalJ

theorem phaseInvolution_transpose :
    (phaseInvolution (n := n) (m := m)).transpose = phaseInvolution := by
  simp only [phaseInvolution, ← kroneckerMap_transpose, internalJ_transpose]
  ext i j
  simp [kroneckerMap_apply]

variable [Fintype n] [Fintype m]

@[simp] theorem phaseInvolution_sq :
    phaseInvolution (n := n) (m := m) * phaseInvolution = 1 := by
  change (internalJ (n := n) ⊗ₖ internalJ (n := m)) *
    (internalJ (n := n) ⊗ₖ internalJ (n := m)) = 1
  rw [← mul_kronecker_mul, internalJ_sq, internalJ_sq]
  calc
    (-1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) ⊗ₖ
        (-1 : Matrix (m ⊕ m) (m ⊕ m) ℝ) =
        (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) ⊗ₖ
          (1 : Matrix (m ⊕ m) (m ⊕ m) ℝ) := by
      ext i j
      simp [kroneckerMap_apply]
    _ = 1 := one_kronecker_one

/-- Projection onto the negative eigenspace of the product phase involution. -/
def phaseProjector :
    Matrix ((n ⊕ n) × (m ⊕ m)) ((n ⊕ n) × (m ⊕ m)) ℝ :=
  (1 / 2 : ℝ) • (1 - phaseInvolution)

@[simp] theorem phaseProjector_sq :
    phaseProjector (n := n) (m := m) * phaseProjector = phaseProjector := by
  have hs : (1 - phaseInvolution (n := n) (m := m)) * (1 - phaseInvolution) =
      (2 : ℝ) • (1 - phaseInvolution) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, phaseInvolution_sq, two_smul]
    abel
  simp only [phaseProjector, smul_mul_smul, hs, smul_smul]
  norm_num

omit [Fintype n] [Fintype m] in
theorem phaseProjector_transpose :
    (phaseProjector (n := n) (m := m)).transpose = phaseProjector := by
  simp only [phaseProjector, transpose_smul, transpose_sub, transpose_one,
    phaseInvolution_transpose]

omit [Fintype n] [Fintype m] in
theorem phaseProjector_isHermitian :
    (phaseProjector (n := n) (m := m)).IsHermitian := by
  change (phaseProjector (n := n) (m := m)).conjTranspose = phaseProjector
  simpa using phaseProjector_transpose (n := n) (m := m)

/-- Compress the ordinary real Kronecker product by the common-phase projector. -/
def compressedTensor
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (B : Matrix (m ⊕ m) (m ⊕ m) ℝ) :
    Matrix ((n ⊕ n) × (m ⊕ m)) ((n ⊕ n) × (m ⊕ m)) ℝ :=
  phaseProjector * (A ⊗ₖ B) * phaseProjector

/-- Positivity holds for full ambient inputs, without phase-commutation
hypotheses on either factor. -/
theorem compressedTensor_posSemidef
    {A : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    {B : Matrix (m ⊕ m) (m ⊕ m) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (compressedTensor A B).PosSemidef := by
  have h := (hA.kronecker hB).mul_mul_conjTranspose_same
    (phaseProjector (n := n) (m := m))
  simpa only [compressedTensor, (phaseProjector_isHermitian (n := n) (m := m)).eq]
    using h

theorem compressedTensor_add_left
    (A A' : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (B : Matrix (m ⊕ m) (m ⊕ m) ℝ) :
    compressedTensor (A + A') B = compressedTensor A B + compressedTensor A' B := by
  simp only [compressedTensor, add_kronecker, mul_add, add_mul]

theorem compressedTensor_add_right
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (B B' : Matrix (m ⊕ m) (m ⊕ m) ℝ) :
    compressedTensor A (B + B') = compressedTensor A B + compressedTensor A B' := by
  simp only [compressedTensor, kronecker_add, mul_add, add_mul]

theorem compressedTensor_smul_left (r : ℝ)
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (B : Matrix (m ⊕ m) (m ⊕ m) ℝ) :
    compressedTensor (r • A) B = r • compressedTensor A B := by
  simp only [compressedTensor, smul_kronecker, mul_smul_comm, smul_mul_assoc]

theorem compressedTensor_smul_right (r : ℝ)
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ)
    (B : Matrix (m ⊕ m) (m ⊕ m) ℝ) :
    compressedTensor A (r • B) = r • compressedTensor A B := by
  simp only [compressedTensor, kronecker_smul, mul_smul_comm, smul_mul_assoc]

end InfoGeometry.Quantum.Realification
