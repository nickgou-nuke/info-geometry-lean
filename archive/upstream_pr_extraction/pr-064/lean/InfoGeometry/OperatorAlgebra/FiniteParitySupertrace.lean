import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

open Matrix
open scoped BigOperators

noncomputable section

set_option linter.unusedSimpArgs false

namespace InfoGeometry.OperatorAlgebra.FiniteParitySupertrace

variable {n : Type*} [Fintype n] [DecidableEq n]

def parityOperator (sign : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal sign

def positiveParityProjector (sign : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => (1 + sign i) / 2)

def negativeParityProjector (sign : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => (1 - sign i) / 2)

def supertrace (sign : n → ℝ) (A : Matrix n n ℝ) : ℝ :=
  Matrix.trace (parityOperator sign * A)

omit [Fintype n] in
theorem parityOperator_apply
    (sign : n → ℝ) (i j : n) :
    parityOperator sign i j = if i = j then sign i else 0 := by
  by_cases hij : i = j <;> simp [parityOperator, hij]

theorem parityOperator_sq
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1) :
    parityOperator sign * parityOperator sign = 1 := by
  rw [parityOperator, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [pow_two] using hsign i
  · simp [hij]

omit [Fintype n] in
theorem positiveParityProjector_add_negativeParityProjector
    (sign : n → ℝ) :
    positiveParityProjector sign + negativeParityProjector sign = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [positiveParityProjector, negativeParityProjector]
    ring
  · simp [positiveParityProjector, negativeParityProjector, hij]

omit [Fintype n] in
theorem positiveParityProjector_sub_negativeParityProjector
    (sign : n → ℝ) :
    positiveParityProjector sign - negativeParityProjector sign =
      parityOperator sign := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [positiveParityProjector, negativeParityProjector, parityOperator]
    ring
  · simp [positiveParityProjector, negativeParityProjector, parityOperator, hij]

theorem positiveParityProjector_idempotent
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1) :
    positiveParityProjector sign * positiveParityProjector sign =
      positiveParityProjector sign := by
  rw [positiveParityProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  nlinarith [hsign i]

theorem negativeParityProjector_idempotent
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1) :
    negativeParityProjector sign * negativeParityProjector sign =
      negativeParityProjector sign := by
  rw [negativeParityProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  nlinarith [hsign i]

theorem parityProjectors_orthogonal
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1) :
    positiveParityProjector sign * negativeParityProjector sign = 0 := by
  rw [positiveParityProjector, negativeParityProjector,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
    nlinarith [hsign i]
  · simp [hij]

theorem operator_four_block_decomposition
    (sign : n → ℝ)
    (A : Matrix n n ℝ) :
    A =
      positiveParityProjector sign * A * positiveParityProjector sign +
      positiveParityProjector sign * A * negativeParityProjector sign +
      negativeParityProjector sign * A * positiveParityProjector sign +
      negativeParityProjector sign * A * negativeParityProjector sign := by
  calc
    A = 1 * A * 1 := by simp
    _ = (positiveParityProjector sign + negativeParityProjector sign) * A *
        (positiveParityProjector sign + negativeParityProjector sign) := by
          rw [positiveParityProjector_add_negativeParityProjector]
    _ = _ := by noncomm_ring

theorem supertrace_eq_sum_sign_mul_diagonal
    (sign : n → ℝ) (A : Matrix n n ℝ) :
    supertrace sign A = ∑ i, sign i * A i i := by
  simp [supertrace, parityOperator, Matrix.trace]

@[simp] theorem supertrace_zero (sign : n → ℝ) :
    supertrace sign 0 = 0 := by
  rw [supertrace_eq_sum_sign_mul_diagonal]
  simp

theorem supertrace_add (sign : n → ℝ) (A B : Matrix n n ℝ) :
    supertrace sign (A + B) = supertrace sign A + supertrace sign B := by
  rw [supertrace_eq_sum_sign_mul_diagonal,
    supertrace_eq_sum_sign_mul_diagonal,
    supertrace_eq_sum_sign_mul_diagonal]
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem supertrace_smul (sign : n → ℝ) (c : ℝ) (A : Matrix n n ℝ) :
    supertrace sign (c • A) = c * supertrace sign A := by
  rw [supertrace_eq_sum_sign_mul_diagonal,
    supertrace_eq_sum_sign_mul_diagonal]
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    ∑ i, sign i * (c * A i i) = ∑ i, c * (sign i * A i i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * ∑ i, sign i * A i i := by
      rw [Finset.mul_sum]

theorem supertrace_neg (sign : n → ℝ) (A : Matrix n n ℝ) :
    supertrace sign (-A) = -supertrace sign A := by
  rw [supertrace_eq_sum_sign_mul_diagonal,
    supertrace_eq_sum_sign_mul_diagonal]
  simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem supertrace_sub (sign : n → ℝ) (A B : Matrix n n ℝ) :
    supertrace sign (A - B) = supertrace sign A - supertrace sign B := by
  rw [sub_eq_add_neg, supertrace_add, supertrace_neg]
  rfl

def IsOdd (sign : n → ℝ) (A : Matrix n n ℝ) : Prop :=
  parityOperator sign * A = -(A * parityOperator sign)

def IsEven (sign : n → ℝ) (A : Matrix n n ℝ) : Prop :=
  parityOperator sign * A = A * parityOperator sign

theorem isEven_iff_entries
    (sign : n → ℝ) (A : Matrix n n ℝ) :
    IsEven sign A ↔
      ∀ i j, sign i * A i j = A i j * sign j := by
  constructor
  · intro h i j
    have hij := congrArg (fun M : Matrix n n ℝ => M i j) h
    simpa [IsEven, parityOperator, Matrix.diagonal_mul,
      Matrix.mul_diagonal] using hij
  · intro h
    ext i j
    simpa [IsEven, parityOperator, Matrix.diagonal_mul,
      Matrix.mul_diagonal] using h i j

theorem isOdd_iff_entries
    (sign : n → ℝ) (A : Matrix n n ℝ) :
    IsOdd sign A ↔
      ∀ i j, sign i * A i j = -(A i j * sign j) := by
  constructor
  · intro h i j
    have hij := congrArg (fun M : Matrix n n ℝ => M i j) h
    simpa [IsOdd, parityOperator, Matrix.diagonal_mul,
      Matrix.mul_diagonal] using hij
  · intro h
    ext i j
    simpa [IsOdd, parityOperator, Matrix.diagonal_mul,
      Matrix.mul_diagonal] using h i j

theorem even_positive_negative_blocks_zero
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1)
    (A : Matrix n n ℝ)
    (hA : IsEven sign A) :
    positiveParityProjector sign * A * negativeParityProjector sign = 0 ∧
      negativeParityProjector sign * A * positiveParityProjector sign = 0 := by
  have hentries := (isEven_iff_entries sign A).mp hA
  constructor <;> ext i j
  · rw [positiveParityProjector, negativeParityProjector,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases sq_eq_one_iff.mp (hsign i) with hi | hi <;>
      rcases sq_eq_one_iff.mp (hsign j) with hj | hj
    · simp [positiveParityProjector, negativeParityProjector, hi, hj]
    · have hz : A i j = 0 := by
        have h := hentries i j
        rw [hi, hj] at h
        linarith
      simp [positiveParityProjector, negativeParityProjector, hi, hj, hz]
    · simp [positiveParityProjector, negativeParityProjector, hi, hj]
    · simp [positiveParityProjector, negativeParityProjector, hi, hj]
  · rw [negativeParityProjector, positiveParityProjector,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases sq_eq_one_iff.mp (hsign i) with hi | hi <;>
      rcases sq_eq_one_iff.mp (hsign j) with hj | hj
    · simp [positiveParityProjector, negativeParityProjector, hi, hj]
    · simp [positiveParityProjector, negativeParityProjector, hi, hj]
    · have hz : A i j = 0 := by
        have h := hentries i j
        rw [hi, hj] at h
        linarith
      simp [positiveParityProjector, negativeParityProjector, hi, hj, hz]
    · simp [positiveParityProjector, negativeParityProjector, hi, hj]

theorem odd_positive_negative_diagonal_blocks_zero
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1)
    (A : Matrix n n ℝ)
    (hA : IsOdd sign A) :
    positiveParityProjector sign * A * positiveParityProjector sign = 0 ∧
      negativeParityProjector sign * A * negativeParityProjector sign = 0 := by
  have hentries := (isOdd_iff_entries sign A).mp hA
  constructor <;> ext i j
  · rw [positiveParityProjector, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases sq_eq_one_iff.mp (hsign i) with hi | hi <;>
      rcases sq_eq_one_iff.mp (hsign j) with hj | hj
    · have hz : A i j = 0 := by
        have h := hentries i j
        rw [hi, hj] at h
        linarith
      simp [positiveParityProjector, hi, hj, hz]
    · simp [positiveParityProjector, hi, hj]
    · simp [positiveParityProjector, hi, hj]
    · simp [positiveParityProjector, hi, hj]
  · rw [negativeParityProjector, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases sq_eq_one_iff.mp (hsign i) with hi | hi <;>
      rcases sq_eq_one_iff.mp (hsign j) with hj | hj
    · simp [negativeParityProjector, hi, hj]
    · simp [negativeParityProjector, hi, hj]
    · simp [negativeParityProjector, hi, hj]
    · have hz : A i j = 0 := by
        have h := hentries i j
        rw [hi, hj] at h
        linarith
      simp [negativeParityProjector, hi, hj, hz]

theorem supertrace_eq_zero_of_odd
    (sign : n → ℝ) (A : Matrix n n ℝ)
    (hodd : IsOdd sign A) :
    supertrace sign A = 0 := by
  have htrace :=
    congrArg Matrix.trace hodd
  rw [Matrix.trace_neg, Matrix.trace_mul_comm A (parityOperator sign)] at htrace
  change supertrace sign A = 0
  rw [supertrace]
  linarith

theorem IsEven.add
    {sign : n → ℝ} {A B : Matrix n n ℝ}
    (hA : IsEven sign A)
    (hB : IsEven sign B) :
    IsEven sign (A + B) := by
  rw [IsEven, mul_add, add_mul, hA, hB]

theorem IsOdd.add
    {sign : n → ℝ} {A B : Matrix n n ℝ}
    (hA : IsOdd sign A)
    (hB : IsOdd sign B) :
    IsOdd sign (A + B) := by
  rw [IsOdd, mul_add, add_mul, hA, hB]
  abel

theorem IsOdd.mul
    {sign : n → ℝ} {A B : Matrix n n ℝ}
    (hA : IsOdd sign A)
    (hB : IsOdd sign B) :
    IsEven sign (A * B) := by
  rw [IsEven, ← Matrix.mul_assoc, hA, neg_mul, Matrix.mul_assoc, hB]
  simp [Matrix.mul_assoc]

theorem IsEven.mul
    {sign : n → ℝ} {A B : Matrix n n ℝ}
    (hA : IsEven sign A)
    (hB : IsEven sign B) :
    IsEven sign (A * B) := by
  rw [IsEven]
  calc
    parityOperator sign * (A * B) =
        (parityOperator sign * A) * B := by rw [Matrix.mul_assoc]
    _ = (A * parityOperator sign) * B := by rw [hA]
    _ = A * (parityOperator sign * B) := by rw [Matrix.mul_assoc]
    _ = A * (B * parityOperator sign) := by rw [hB]
    _ = (A * B) * parityOperator sign := by rw [Matrix.mul_assoc]

theorem IsEven.mul_odd
    {sign : n → ℝ} {A B : Matrix n n ℝ}
    (hA : IsEven sign A)
    (hB : IsOdd sign B) :
    IsOdd sign (A * B) := by
  rw [IsOdd]
  calc
    parityOperator sign * (A * B) =
        (parityOperator sign * A) * B := by rw [Matrix.mul_assoc]
    _ = (A * parityOperator sign) * B := by rw [hA]
    _ = A * (parityOperator sign * B) := by rw [Matrix.mul_assoc]
    _ = A * (-(B * parityOperator sign)) := by rw [hB]
    _ = -(A * (B * parityOperator sign)) := by rw [mul_neg]
    _ = -((A * B) * parityOperator sign) := by rw [Matrix.mul_assoc]

theorem IsOdd.mul_even
    {sign : n → ℝ} {A B : Matrix n n ℝ}
    (hA : IsOdd sign A)
    (hB : IsEven sign B) :
    IsOdd sign (A * B) := by
  rw [IsOdd]
  calc
    parityOperator sign * (A * B) =
        (parityOperator sign * A) * B := by rw [Matrix.mul_assoc]
    _ = (-(A * parityOperator sign)) * B := by rw [hA]
    _ = -((A * parityOperator sign) * B) := by rw [neg_mul]
    _ = -(A * (parityOperator sign * B)) := by rw [Matrix.mul_assoc]
    _ = -(A * (B * parityOperator sign)) := by rw [hB]
    _ = -((A * B) * parityOperator sign) := by rw [Matrix.mul_assoc]

theorem IsEven.neg
    {sign : n → ℝ} {A : Matrix n n ℝ}
    (hA : IsEven sign A) :
    IsEven sign (-A) := by
  rw [IsEven, mul_neg, neg_mul, hA]

theorem IsOdd.neg
    {sign : n → ℝ} {A : Matrix n n ℝ}
    (hA : IsOdd sign A) :
    IsOdd sign (-A) := by
  rw [IsOdd, mul_neg, neg_mul, hA]

theorem IsEven.smul
    {sign : n → ℝ} {c : ℝ} {A : Matrix n n ℝ}
    (hA : IsEven sign A) :
    IsEven sign (c • A) := by
  rw [IsEven, smul_mul_assoc, mul_smul_comm, hA]

theorem IsOdd.smul
    {sign : n → ℝ} {c : ℝ} {A : Matrix n n ℝ}
    (hA : IsOdd sign A) :
    IsOdd sign (c • A) := by
  rw [IsOdd, smul_mul_assoc, mul_smul_comm, hA]
  simp

theorem IsEven.zero (sign : n → ℝ) : IsEven sign 0 := by
  simp [IsEven]

theorem IsOdd.zero (sign : n → ℝ) : IsOdd sign 0 := by
  simp [IsOdd]

theorem IsEven.sub
    {sign : n → ℝ} {A B : Matrix n n ℝ}
    (hA : IsEven sign A)
    (hB : IsEven sign B) :
    IsEven sign (A - B) := by
  rw [sub_eq_add_neg]
  exact IsEven.add hA (IsEven.neg hB)

theorem IsOdd.sub
    {sign : n → ℝ} {A B : Matrix n n ℝ}
    (hA : IsOdd sign A)
    (hB : IsOdd sign B) :
    IsOdd sign (A - B) := by
  rw [sub_eq_add_neg]
  exact IsOdd.add hA (IsOdd.neg hB)

theorem odd_mul_positiveProjector_eq_negativeProjector_mul
    (sign : n → ℝ)
    (_hsign : ∀ i, sign i ^ 2 = 1)
    (Q : Matrix n n ℝ)
    (hQ : IsOdd sign Q) :
    Q * positiveParityProjector sign =
      negativeParityProjector sign * Q := by
  have hentries := (isOdd_iff_entries sign Q).mp hQ
  ext i j
  rw [positiveParityProjector, negativeParityProjector,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h := hentries i j
  nlinarith

theorem odd_mul_negativeProjector_eq_positiveProjector_mul
    (sign : n → ℝ)
    (_hsign : ∀ i, sign i ^ 2 = 1)
    (Q : Matrix n n ℝ)
    (hQ : IsOdd sign Q) :
    Q * negativeParityProjector sign =
      positiveParityProjector sign * Q := by
  have hentries := (isOdd_iff_entries sign Q).mp hQ
  ext i j
  rw [negativeParityProjector, positiveParityProjector,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h := hentries i j
  nlinarith

def positiveToNegativeDifferential
    (sign : n → ℝ) (Q : Matrix n n ℝ) : Matrix n n ℝ :=
  negativeParityProjector sign * Q * positiveParityProjector sign

def negativeToPositiveDifferential
    (sign : n → ℝ) (Q : Matrix n n ℝ) : Matrix n n ℝ :=
  positiveParityProjector sign * Q * negativeParityProjector sign

theorem positiveToNegativeDifferential_eq
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1)
    (Q : Matrix n n ℝ)
    (hQ : IsOdd sign Q) :
    positiveToNegativeDifferential sign Q =
      Q * positiveParityProjector sign := by
  rw [positiveToNegativeDifferential]
  rw [← odd_mul_positiveProjector_eq_negativeProjector_mul sign hsign Q hQ]
  rw [Matrix.mul_assoc, positiveParityProjector_idempotent sign hsign]

theorem negativeToPositiveDifferential_eq
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1)
    (Q : Matrix n n ℝ)
    (hQ : IsOdd sign Q) :
    negativeToPositiveDifferential sign Q =
      Q * negativeParityProjector sign := by
  rw [negativeToPositiveDifferential]
  rw [← odd_mul_negativeProjector_eq_positiveProjector_mul sign hsign Q hQ]
  rw [Matrix.mul_assoc, negativeParityProjector_idempotent sign hsign]

theorem restrictedDifferentials_comp_zero
    (sign : n → ℝ)
    (hsign : ∀ i, sign i ^ 2 = 1)
    (Q : Matrix n n ℝ)
    (hQodd : IsOdd sign Q)
    (hQsq : Q * Q = 0) :
    negativeToPositiveDifferential sign Q *
        positiveToNegativeDifferential sign Q = 0 ∧
      positiveToNegativeDifferential sign Q *
        negativeToPositiveDifferential sign Q = 0 := by
  rw [negativeToPositiveDifferential_eq sign hsign Q hQodd,
    positiveToNegativeDifferential_eq sign hsign Q hQodd]
  constructor
  · rw [odd_mul_negativeProjector_eq_positiveProjector_mul sign hsign Q hQodd,
      Matrix.mul_assoc (positiveParityProjector sign) Q,
      ← Matrix.mul_assoc Q Q, hQsq, zero_mul, mul_zero]
  · rw [odd_mul_positiveProjector_eq_negativeProjector_mul sign hsign Q hQodd,
      Matrix.mul_assoc (negativeParityProjector sign) Q,
      ← Matrix.mul_assoc Q Q, hQsq, zero_mul, mul_zero]

theorem supertrace_mul_comm_of_even_left
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hA : IsEven sign A) :
    supertrace sign (A * B) = supertrace sign (B * A) := by
  rw [supertrace, supertrace]
  have hEven : parityOperator sign * A = A * parityOperator sign := hA
  rw [← Matrix.mul_assoc, hEven, Matrix.mul_assoc]
  simpa [Matrix.mul_assoc] using
    Matrix.trace_mul_comm A (parityOperator sign * B)

theorem supertrace_mul_comm_of_odd_left
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hA : IsOdd sign A) :
    supertrace sign (A * B) = -supertrace sign (B * A) := by
  rw [supertrace, supertrace]
  rw [← Matrix.mul_assoc, hA, neg_mul, Matrix.trace_neg]
  rw [Matrix.mul_assoc]
  simpa [Matrix.mul_assoc] using
    congrArg Neg.neg (Matrix.trace_mul_comm A (parityOperator sign * B))

theorem supertrace_mul_comm_of_odd_odd
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hA : IsOdd sign A)
    (_hB : IsOdd sign B) :
    supertrace sign (A * B) = -supertrace sign (B * A) :=
  supertrace_mul_comm_of_odd_left sign A B hA

theorem supertrace_mul_comm_of_even_right
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hB : IsEven sign B) :
    supertrace sign (A * B) = supertrace sign (B * A) := by
  exact (supertrace_mul_comm_of_even_left sign B A hB).symm

theorem supertrace_mul_comm_of_odd_right
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hB : IsOdd sign B) :
    supertrace sign (A * B) = -supertrace sign (B * A) := by
  have h := supertrace_mul_comm_of_odd_left sign B A hB
  linarith

theorem supertrace_odd_square_zero
    (sign : n → ℝ)
    (A : Matrix n n ℝ)
    (hA : IsOdd sign A) :
    supertrace sign (A * A) = 0 := by
  have h := supertrace_mul_comm_of_odd_left sign A A hA
  linarith

theorem supertrace_anticommutator_zero_of_odd_left
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hA : IsOdd sign A) :
    supertrace sign (A * B + B * A) = 0 := by
  rw [supertrace_add, supertrace_mul_comm_of_odd_left sign A B hA]
  simp

theorem supertrace_commutator_zero_of_even_left
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hA : IsEven sign A) :
    supertrace sign (A * B - B * A) = 0 := by
  rw [supertrace_sub, supertrace_mul_comm_of_even_left sign A B hA]
  simp

theorem supertrace_anticommutator_zero_of_odd_right
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hB : IsOdd sign B) :
    supertrace sign (A * B + B * A) = 0 := by
  rw [supertrace_add, supertrace_mul_comm_of_odd_right sign A B hB]
  simp

theorem supertrace_commutator_zero_of_even_right
    (sign : n → ℝ)
    (A B : Matrix n n ℝ)
    (hB : IsEven sign B) :
    supertrace sign (A * B - B * A) = 0 := by
  rw [supertrace_sub, supertrace_mul_comm_of_even_right sign A B hB]
  simp

end InfoGeometry.OperatorAlgebra.FiniteParitySupertrace
