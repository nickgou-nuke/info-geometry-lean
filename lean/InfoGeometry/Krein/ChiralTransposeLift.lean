/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.LaggedCoincidenceDiracOperator
import InfoGeometry.Core.DefectIteration
import InfoGeometry.Core.PeirceCompressionDefect

/-!
# The chiral transpose lift and its ordered product obstruction

For an arbitrary real matrix `A`, the equal-sign block lift of its symmetric
and skew parts is self-adjoint for the existing doubled grading. An exact
Hadamard frame identifies it with `diag(A, Aᵀ)`. This preserves squares and
finite idempotency-defect iteration, but preserves a product precisely when
its two inputs commute. The contraction's Gram square is diagonal only after
the indicated change of coordinates.

The coefficient operators are full matrices of arbitrary finite size. No
normality, positivity, causality, or commutation is assumed.
-/

noncomputable section

namespace InfoGeometry.Krein.ChiralTransposeLift

open Matrix
open InfoGeometry.Core.IdempotencyDefect

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The unnormalised Hadamard matrix on the two full operator blocks. -/
def hadamard : DoubledLaggedMatrix n :=
  fromBlocks 1 1 1 (-1)

/-- Similarity by `hadamard`, whose inverse is one half of itself. -/
def frame (X : DoubledLaggedMatrix n) : DoubledLaggedMatrix n :=
  (1 / 2 : ℝ) • (hadamard * X * hadamard)

theorem hadamard_square :
    hadamard (n := n) * hadamard = (2 : ℝ) • 1 := by
  rw [hadamard, fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, Matrix.one_apply] <;>
    split_ifs <;> norm_num

theorem frame_add (X Y : DoubledLaggedMatrix n) :
    frame (X + Y) = frame X + frame Y := by
  simp only [frame, mul_add, add_mul, smul_add]

theorem frame_sub (X Y : DoubledLaggedMatrix n) :
    frame (X - Y) = frame X - frame Y := by
  simp only [frame, mul_sub, sub_mul, smul_sub]

@[simp] theorem frame_zero : frame (0 : DoubledLaggedMatrix n) = 0 := by
  simp [frame]

theorem frame_involutive (X : DoubledLaggedMatrix n) : frame (frame X) = X := by
  have h : hadamard * (hadamard * X * hadamard) * hadamard =
      (hadamard * hadamard) * X * (hadamard * hadamard) := by
    simp only [mul_assoc]
  simp only [frame, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [h, hadamard_square]
  norm_num [smul_smul]

theorem frame_injective : Function.Injective (frame (n := n)) := by
  intro X Y h
  have hh := congrArg frame h
  simpa only [frame_involutive] using hh

theorem frame_mul (X Y : DoubledLaggedMatrix n) :
    frame (X * Y) = frame X * frame Y := by
  have h : (hadamard * X * hadamard) * (hadamard * Y * hadamard) =
      hadamard * X * (hadamard * hadamard) * Y * hadamard := by
    simp only [mul_assoc]
  simp only [frame, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h, hadamard_square]
  norm_num [smul_smul, mul_assoc]

/-- The change of coordinates on a pair of independent diagonal operators. -/
theorem frame_blockDiagonal (A B : Matrix n n ℝ) :
    frame (fromBlocks A 0 0 B) =
      fromBlocks ((1 / 2 : ℝ) • (A + B)) ((1 / 2 : ℝ) • (A - B))
        ((1 / 2 : ℝ) • (A - B)) ((1 / 2 : ℝ) • (A + B)) := by
  simp only [frame, hadamard, fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, sub_eq_add_neg] <;> ring

/-- Equal-sign lift of the existing symmetric and skew parts. -/
def lift (A : Matrix n n ℝ) : DoubledLaggedMatrix n :=
  fromBlocks (reversiblePart A) (circulatingPart A)
    (circulatingPart A) (reversiblePart A)

theorem lift_eq_frame (A : Matrix n n ℝ) :
    lift A = frame (fromBlocks A 0 0 A.transpose) := by
  rw [frame_blockDiagonal]
  rfl

theorem frame_lift (A : Matrix n n ℝ) :
    frame (lift A) = fromBlocks A 0 0 A.transpose := by
  rw [lift_eq_frame, frame_involutive]

theorem lift_injective : Function.Injective (lift (n := n)) := by
  intro A B h
  have hh := congrArg frame h
  rw [frame_lift, frame_lift] at hh
  ext i j
  exact congrFun (congrFun hh (Sum.inl i)) (Sum.inl j)

/-- The second leg records the reversed order under transpose. -/
theorem frame_product_defect (A B : Matrix n n ℝ) :
    frame (lift A * lift B - lift (A * B)) =
      fromBlocks 0 0 0 (B * A - A * B).transpose := by
  rw [frame_sub, frame_mul, frame_lift, frame_lift, frame_lift]
  simp only [fromBlocks_multiply, Matrix.transpose_sub, Matrix.transpose_mul]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

/-- The lift is multiplicative on exactly the commuting pairs. -/
theorem lift_mul_eq_iff (A B : Matrix n n ℝ) :
    lift A * lift B = lift (A * B) ↔ Commute A B := by
  constructor
  · intro h
    have hf := frame_product_defect A B
    rw [h, sub_self, frame_zero] at hf
    have ht : (B * A - A * B).transpose = 0 := by
      ext i j
      exact (congrFun (congrFun hf (Sum.inr i)) (Sum.inr j)).symm
    have hz : B * A - A * B = 0 := by
      simpa using congrArg Matrix.transpose ht
    exact (sub_eq_zero.mp hz).symm
  · intro h
    apply sub_eq_zero.mp
    apply frame_injective
    rw [frame_product_defect, frame_zero, h.eq, sub_self]
    simp

theorem lift_square (A : Matrix n n ℝ) :
    lift A * lift A = lift (A * A) :=
  (lift_mul_eq_iff A A).2 (Commute.refl A)

theorem lift_sub (A B : Matrix n n ℝ) : lift (A - B) = lift A - lift B := by
  apply frame_injective
  rw [frame_sub, frame_lift, frame_lift, frame_lift]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

/-- Doubling transports the obstruction; it does not eliminate it. -/
theorem defect_lift (A : Matrix n n ℝ) : defect (lift A) = lift (defect A) := by
  simp only [defect, lift_sub, lift_square]

/-- Every finite stage of the existing defect orbit is preserved exactly. -/
theorem defect_iterate_lift (A : Matrix n n ℝ) (k : ℕ) :
    defect^[k] (lift A) = lift (defect^[k] A) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Function.iterate_succ_apply', ih, defect_lift]

/-- A single formula reads every finite defect stage in the two ordered sectors. -/
theorem frame_defect_iterate_lift (A : Matrix n n ℝ) (k : ℕ) :
    frame (defect^[k] (lift A)) =
      fromBlocks (defect^[k] A) 0 0 (defect^[k] A).transpose := by
  rw [defect_iterate_lift, frame_lift]

/-- Idempotence is reflected as well as preserved by the doubled lift. -/
theorem lift_idempotent_iff (A : Matrix n n ℝ) :
    IsIdempotentElem (lift A) ↔ IsIdempotentElem A := by
  change lift A * lift A = lift A ↔ A * A = A
  rw [lift_square]
  exact lift_injective.eq_iff

/-- The two ordered errors cancel in the Jordan product. -/
theorem lift_jordan (A B : Matrix n n ℝ) :
    lift (A * B + B * A) = lift A * lift B + lift B * lift A := by
  apply frame_injective
  rw [frame_add, frame_mul, frame_mul, frame_lift, frame_lift, frame_lift]
  simp only [fromBlocks_multiply, Matrix.transpose_add, Matrix.transpose_mul]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, add_comm]

/-- A sandwich retains its product order under transpose reversal. -/
theorem lift_sandwich (P A : Matrix n n ℝ) :
    lift (P * A * P) = lift P * lift A * lift P := by
  apply frame_injective
  simp only [frame_mul, frame_lift, fromBlocks_multiply, Matrix.transpose_mul]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, mul_assoc]

/-- Nested compression and doubled defect readout commute exactly. The
relative-shell correction is determined by the original ordered operator
products; it is not an assumed vanishing or a scalar replacement. -/
theorem framed_compression_flag_defect (p : ℕ → Matrix n n ℝ)
    (A : Matrix n n ℝ) (k : ℕ)
    (hp : ∀ i ≤ k, p i * p i = p i)
    (hleft : ∀ i < k, p (i + 1) * p i = p (i + 1))
    (hright : ∀ i < k, p i * p (i + 1) = p (i + 1)) :
    let R := p k * defect (p 0 * A * p 0) * p k -
      ∑ i ∈ Finset.range k, p k * A * (p i - p (i + 1)) * A * p k
    frame (defect (lift (p k) * lift A * lift (p k))) =
      fromBlocks R 0 0 R.transpose := by
  dsimp only
  rw [← lift_sandwich, defect_lift, frame_lift,
    InfoGeometry.Core.PeirceCompressionDefect.defect_compression_flag p A k hp hleft hright]

/-- The lift is self-adjoint for the existing diagonal Krein grading. -/
theorem lift_kreinSelfAdjoint (A : Matrix n n ℝ) :
    laggedCoincidenceGrading * (lift A).transpose * laggedCoincidenceGrading =
      lift A := by
  simp [lift, laggedCoincidenceGrading, fromBlocks_transpose, fromBlocks_multiply,
    reversiblePart_transpose, circulatingPart_transpose]

/-- Contracting the lift with the diagonal form gives a symmetric matrix. -/
def contraction (A : Matrix n n ℝ) : DoubledLaggedMatrix n :=
  laggedCoincidenceGrading * lift A

theorem contraction_blocks (A : Matrix n n ℝ) :
    contraction A = fromBlocks (reversiblePart A) (circulatingPart A)
      (-circulatingPart A) (-reversiblePart A) := by
  simp [contraction, lift, laggedCoincidenceGrading, fromBlocks_multiply]

theorem contraction_transpose (A : Matrix n n ℝ) :
    (contraction A).transpose = contraction A := by
  simp [contraction_blocks, fromBlocks_transpose,
    reversiblePart_transpose, circulatingPart_transpose]

theorem frame_grading :
    frame (laggedCoincidenceGrading (n := n)) = laggedCoincidenceSwap := by
  simp only [frame, hadamard, laggedCoincidenceGrading, laggedCoincidenceSwap,
    fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks] <;> ring

/-- The symmetric contraction becomes the existing Dirac lift of `Aᵀ`. -/
theorem frame_contraction (A : Matrix n n ℝ) :
    frame (contraction A) = laggedCoincidenceDirac A.transpose := by
  rw [contraction, frame_mul, frame_grading, frame_lift]
  simp [laggedCoincidenceSwap, laggedCoincidenceDirac, fromBlocks_multiply]

/-- The ordered Gramians occur in this frame, with `Aᵀ A` first. -/
theorem frame_contraction_square (A : Matrix n n ℝ) :
    frame (contraction A * contraction A) =
      fromBlocks (A.transpose * A) 0 0 (A * A.transpose) := by
  rw [frame_mul, frame_contraction, laggedCoincidenceDirac_square]
  simp only [Matrix.transpose_transpose]

/-- In the original coordinates the square retains the full commutator. -/
theorem contraction_square (A : Matrix n n ℝ) :
    contraction A * contraction A =
      fromBlocks
        (reversiblePart A * reversiblePart A - circulatingPart A * circulatingPart A)
        (reversiblePart A * circulatingPart A - circulatingPart A * reversiblePart A)
        (reversiblePart A * circulatingPart A - circulatingPart A * reversiblePart A)
        (reversiblePart A * reversiblePart A - circulatingPart A * circulatingPart A) := by
  rw [contraction_blocks, fromBlocks_multiply]
  congr 1 <;> noncomm_ring

/-- The exact idempotency obstruction, retaining both ordered mixed products. -/
theorem defect_lift_blocks (A : Matrix n n ℝ) :
    defect (lift A) =
      fromBlocks
        (reversiblePart A * reversiblePart A + circulatingPart A * circulatingPart A -
          reversiblePart A)
        (reversiblePart A * circulatingPart A + circulatingPart A * reversiblePart A -
          circulatingPart A)
        (reversiblePart A * circulatingPart A + circulatingPart A * reversiblePart A -
          circulatingPart A)
        (reversiblePart A * reversiblePart A + circulatingPart A * circulatingPart A -
          reversiblePart A) := by
  simp only [defect, lift, fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, add_comm]

/-- The difference of the two Gramians measures the symmetric/skew commutator. -/
theorem gram_difference (A : Matrix n n ℝ) :
    A.transpose * A - A * A.transpose =
      (2 : ℕ) • (reversiblePart A * circulatingPart A -
        circulatingPart A * reversiblePart A) := by
  calc
    _ = (reversiblePart A - circulatingPart A) *
          (reversiblePart A + circulatingPart A) -
        (reversiblePart A + circulatingPart A) *
          (reversiblePart A - circulatingPart A) := by
            rw [reversiblePart_sub_circulatingPart, reversiblePart_add_circulatingPart]
    _ = _ := by simp only [two_nsmul]; noncomm_ring

/-- Projection onto the positive eigenspace of the swap, not of the grading. -/
def nullPlus : DoubledLaggedMatrix n := frame (fromBlocks 1 0 0 0)

/-- Projection onto the negative eigenspace of the swap. -/
def nullMinus : DoubledLaggedMatrix n := frame (fromBlocks 0 0 0 1)

theorem nullPlus_blocks :
    nullPlus (n := n) = (1 / 2 : ℝ) • fromBlocks 1 1 1 1 := by
  rw [nullPlus, frame_blockDiagonal]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

theorem nullMinus_blocks :
    nullMinus (n := n) = (1 / 2 : ℝ) • fromBlocks 1 (-1) (-1) 1 := by
  rw [nullMinus, frame_blockDiagonal]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

theorem nullPlus_transpose : (nullPlus (n := n)).transpose = nullPlus := by
  simp [nullPlus_blocks, fromBlocks_transpose]

theorem nullMinus_transpose : (nullMinus (n := n)).transpose = nullMinus := by
  simp [nullMinus_blocks, fromBlocks_transpose]

theorem nullPlus_idempotent : IsIdempotentElem (nullPlus (n := n)) := by
  change frame _ * frame _ = frame _
  rw [← frame_mul]
  congr 1
  simp [fromBlocks_multiply]

theorem nullMinus_idempotent : IsIdempotentElem (nullMinus (n := n)) := by
  change frame _ * frame _ = frame _
  rw [← frame_mul]
  congr 1
  simp [fromBlocks_multiply]

theorem nullPlus_add_nullMinus : nullPlus (n := n) + nullMinus = 1 := by
  rw [nullPlus_blocks, nullMinus_blocks]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, Matrix.one_apply] <;>
    split_ifs <;> norm_num

theorem nullPlus_mul_nullMinus : nullPlus (n := n) * nullMinus = 0 := by
  rw [nullPlus, nullMinus, ← frame_mul]
  simp [fromBlocks_multiply]

/-- Each swap eigenspace is totally null for the diagonal grading. -/
theorem nullPlus_krein_null :
    (nullPlus (n := n)).transpose * laggedCoincidenceGrading * nullPlus = 0 := by
  rw [nullPlus_transpose]
  apply frame_injective
  simp only [frame_mul, nullPlus, frame_involutive, frame_grading, frame_zero]
  simp [laggedCoincidenceSwap, fromBlocks_multiply]

theorem nullMinus_krein_null :
    (nullMinus (n := n)).transpose * laggedCoincidenceGrading * nullMinus = 0 := by
  rw [nullMinus_transpose]
  apply frame_injective
  simp only [frame_mul, nullMinus, frame_involutive, frame_grading, frame_zero]
  simp [laggedCoincidenceSwap, fromBlocks_multiply]

/-- With epsilon equal to swap times grading, this is `(J + epsilon)/2`. -/
theorem null_cross_pairing :
    (nullPlus (n := n)).transpose * laggedCoincidenceGrading * nullMinus =
      (1 / 2 : ℝ) • (laggedCoincidenceGrading +
        laggedCoincidenceSwap * laggedCoincidenceGrading) := by
  rw [nullPlus_transpose, nullPlus_blocks, nullMinus_blocks]
  simp only [laggedCoincidenceGrading, laggedCoincidenceSwap,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks] <;> ring

/-- The structural swap reverses the diagonal form. -/
theorem swap_antiIsometry :
    (laggedCoincidenceSwap (n := n)).transpose * laggedCoincidenceGrading *
      laggedCoincidenceSwap = -laggedCoincidenceGrading := by
  simp only [laggedCoincidenceSwap, laggedCoincidenceGrading,
    fromBlocks_transpose, fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

/-- The ordered product `swap * grading` is skew and squares to minus identity. -/
theorem swap_grading_square :
    (laggedCoincidenceSwap (n := n) * laggedCoincidenceGrading) *
      (laggedCoincidenceSwap * laggedCoincidenceGrading) = -1 := by
  simp only [laggedCoincidenceSwap, laggedCoincidenceGrading, fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, Matrix.one_apply]

theorem swap_grading_transpose :
    (laggedCoincidenceSwap (n := n) * laggedCoincidenceGrading).transpose =
      -(laggedCoincidenceSwap * laggedCoincidenceGrading) := by
  simp only [laggedCoincidenceSwap, laggedCoincidenceGrading,
    fromBlocks_multiply, fromBlocks_transpose]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks]

end InfoGeometry.Krein.ChiralTransposeLift
