import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Drazin

/-!
# Campbell--Meyer 1978: weak Drazin inverses

Source digest:

Stephen L. Campbell and Carl D. Meyer, Jr., "Weak Drazin Inverses",
Linear Algebra and Its Applications 20, 167--178 (1978).

The paper defines a weak Drazin inverse, or `(d)`-inverse, for a square matrix
`A` of index `k` by the weakened relation

`B A^(k+1) = A^k`.

After similarity to `diag(C,N)`, with `C` invertible and `N^k = 0`, every weak
inverse has the fixed regular block `C^{-1}` and arbitrary nilpotent-lane data.
This file formalizes that finite algebraic spine in an exact rational packet:

* a rank-one regular lane plus a square-zero nilpotent lane;
* non-uniqueness of weak Drazin inverses;
* the Drazin inverse as a special weak inverse;
* the Campbell--Meyer polynomial/Souriau--Frame commuting weak inverse
  `1/2 I`;
* projective and commuting readouts on concrete witnesses; and
* stability under a strict finite `GL_3(Q)` permutation representative.

The file intentionally does not formalize numerical algorithms, rank
factorization over arbitrary fields, or Markov-chain/differential-equation
applications.
-/

noncomputable section

namespace InfoGeometry.Canonical.CampbellMeyerWeakDrazin

open InfoGeometry.Canonical

abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R

/-! ## Weak Drazin API -/

/-- Campbell--Meyer weak Drazin, or `(d)`-inverse, relation. -/
def IsWeakDrazin {R : Type*} [Ring R] (a b : R) (k : ℕ) : Prop :=
  b * a ^ (k + 1) = a ^ k

/-- A commuting weak Drazin inverse. -/
def IsCommutingWeakDrazin {R : Type*} [Ring R] (a b : R) (k : ℕ) : Prop :=
  IsWeakDrazin a b k ∧ a * b = b * a

/-- Every Drazin inverse is a weak Drazin inverse in the Campbell--Meyer sense. -/
theorem Drazin_isWeakDrazin {R : Type*} [Ring R] {a b : R} {k : ℕ}
    (h : Drazin.IsDrazinInverse a b k) :
    IsWeakDrazin a b k := by
  unfold IsWeakDrazin
  have hcomm : Commute b a := h.comm.symm
  calc
    b * a ^ (k + 1) = a ^ (k + 1) * b := (hcomm.pow_right (k + 1)).eq
    _ = a ^ k := h.2.2

/-! ## Exact `diag(2,N₂)` packet -/

/-- Regular eigenvalue `2` plus a square-zero nilpotent Jordan lane. -/
def weakA : Mat3 ℚ :=
  !![2, 0, 0;
     0, 0, 1;
     0, 0, 0]

/-- The square-zero nilpotent part of the packet. -/
def weakNilpotentLane : Mat3 ℚ :=
  !![0, 0, 0;
     0, 0, 1;
     0, 0, 0]

/-- The regular support projector for the nonzero spectral lane. -/
def weakRegularProjector : Mat3 ℚ :=
  !![1, 0, 0;
     0, 0, 0;
     0, 0, 0]

/-- The nilpotent lane is square-zero. -/
theorem weakNilpotentLane_sq_eq_zero :
    weakNilpotentLane ^ 2 = 0 := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, weakNilpotentLane]

/-- The packet index readout: `A²` is regular while the nilpotent lane has vanished. -/
theorem weakA_sq_readout :
    weakA ^ 2 =
      !![4, 0, 0;
         0, 0, 0;
         0, 0, 0] := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakA]; try norm_num)

lemma weakA_pow_three :
    weakA ^ 3 =
      !![8, 0, 0;
         0, 0, 0;
         0, 0, 0] := by
  change weakA ^ 2 * weakA = _
  rw [weakA_sq_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakA]; try norm_num)

/-- Characteristic/minimal-polynomial readout used in the paper's polynomial formula. -/
theorem weakA_cubic_eq_two_smul_square :
    weakA ^ 3 = (2 : ℚ) • weakA ^ 2 := by
  rw [weakA_pow_three, weakA_sq_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try norm_num)

/-! ## Drazin and weak inverses -/

/-- The ordinary Drazin inverse: inverse on the regular lane, zero on the nilpotent lane. -/
def weakDrazinInverse : Mat3 ℚ :=
  !![1 / 2, 0, 0;
     0, 0, 0;
     0, 0, 0]

/-- The Drazin witness satisfies the usual Drazin equations at index `2`. -/
theorem weakDrazinInverse_isDrazin :
    Drazin.IsDrazinInverse weakA weakDrazinInverse 2 := by
  refine Drazin.IsDrazinInverse.mk ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakA, weakDrazinInverse]; try norm_num)
  · ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakA, weakDrazinInverse]; try norm_num)
  · rw [weakA_pow_three, weakA_sq_readout]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakDrazinInverse]; try norm_num)

/-- The Drazin witness is therefore a weak Drazin inverse. -/
theorem weakDrazinInverse_isWeak :
    IsWeakDrazin weakA weakDrazinInverse 2 :=
  Drazin_isWeakDrazin weakDrazinInverse_isDrazin

/-- A wild weak inverse with arbitrary nilpotent-lane data. -/
def weakWildInverse : Mat3 ℚ :=
  !![1 / 2, 3, 5;
     0, 7, 11;
     0, 13, 17]

/-- The wild packet satisfies only the weak `(d)` relation. -/
theorem weakWildInverse_isWeak :
    IsWeakDrazin weakA weakWildInverse 2 := by
  unfold IsWeakDrazin
  rw [weakA_pow_three, weakA_sq_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakWildInverse]; try norm_num)

/-- The weak inverse is not unique. -/
theorem weakWildInverse_ne_Drazin :
    weakWildInverse ≠ weakDrazinInverse := by
  intro h
  have h0 := congr_fun (congr_fun h 0) 1
  revert h0
  decide

/-- The wild weak inverse is not a commuting weak inverse. -/
theorem weakWildInverse_not_commuting :
    weakA * weakWildInverse ≠ weakWildInverse * weakA := by
  intro h
  have h0 := congr_fun (congr_fun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, weakA, weakWildInverse] at h0

/-! ## Polynomial/Souriau--Frame weak inverse -/

/--
Campbell--Meyer Theorem 4 / Theorem 5 packet:
for the minimal polynomial `x² (x - 2)`, the polynomial/Souriau--Frame weak
inverse is `1/2 I`.
-/
def weakPolynomialInverse : Mat3 ℚ :=
  (1 / 2 : ℚ) • (1 : Mat3 ℚ)

/-- The polynomial/Souriau--Frame packet is a weak Drazin inverse. -/
theorem weakPolynomialInverse_isWeak :
    IsWeakDrazin weakA weakPolynomialInverse 2 := by
  unfold IsWeakDrazin
  rw [weakA_pow_three, weakA_sq_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakPolynomialInverse]; try norm_num)

/-- The polynomial/Souriau--Frame weak inverse commutes with `A`. -/
theorem weakPolynomialInverse_isCommuting :
    IsCommutingWeakDrazin weakA weakPolynomialInverse 2 := by
  constructor
  · exact weakPolynomialInverse_isWeak
  · simp [weakPolynomialInverse]

/-- The polynomial/Souriau--Frame weak inverse is invertible. -/
def weakPolynomialInverseUnit : (Mat3 ℚ)ˣ where
  val := weakPolynomialInverse
  inv := (2 : ℚ) • (1 : Mat3 ℚ)
  val_inv := by simp [weakPolynomialInverse, smul_smul]
  inv_val := by simp [weakPolynomialInverse, smul_smul]

/-- The polynomial/Souriau--Frame weak inverse is not the Drazin inverse. -/
theorem weakPolynomialInverse_ne_Drazin :
    weakPolynomialInverse ≠ weakDrazinInverse := by
  intro h
  have h0 := congr_fun (congr_fun h 1) 1
  simp [weakPolynomialInverse, weakDrazinInverse] at h0

/-- Souriau--Frame coefficient readout: `p₁ = trace(A) = 2`. -/
def weakSFp1 : ℚ :=
  Matrix.trace (weakA * (1 : Mat3 ℚ))

/-- Souriau--Frame `B₀ = I` gives `(1/p₁) B₀ = 1/2 I`. -/
theorem weakSouriauFrame_formula_eq_polynomial :
    weakSFp1⁻¹ • (1 : Mat3 ℚ) = weakPolynomialInverse := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weakSFp1, weakPolynomialInverse, weakA, Matrix.trace, Matrix.diag, Fin.sum_univ_three]

/-! ## Projective and commuting concrete readouts -/

/-- A projective-shaped weak inverse: arbitrary coupling, but range readout stays regular. -/
def weakProjectiveInverse : Mat3 ℚ :=
  !![1 / 2, 2, 3;
     0, 0, 5;
     0, 0, 7]

/-- The projective-shaped packet is weak. -/
theorem weakProjectiveInverse_isWeak :
    IsWeakDrazin weakA weakProjectiveInverse 2 := by
  unfold IsWeakDrazin
  rw [weakA_pow_three, weakA_sq_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakProjectiveInverse]; try norm_num)

/-- The `B A` readout is an idempotent with the same regular range lane. -/
theorem weakProjectiveInverse_BA_readout :
    weakProjectiveInverse * weakA =
      !![1, 0, 2;
         0, 0, 0;
         0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakProjectiveInverse, weakA]; try norm_num)

/-- The projective-shaped `B A` readout is idempotent. -/
theorem weakProjectiveInverse_BA_idempotent :
    (weakProjectiveInverse * weakA) * (weakProjectiveInverse * weakA) =
      weakProjectiveInverse * weakA := by
  rw [weakProjectiveInverse_BA_readout]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try norm_num)

/-- A commuting weak inverse with nonzero nilpotent-lane polynomial data. -/
def weakCommutingInverse : Mat3 ℚ :=
  !![1 / 2, 0, 0;
     0, 3, 4;
     0, 0, 3]

/-- The commuting packet satisfies the weak relation and commutes with `A`. -/
theorem weakCommutingInverse_isCommuting :
    IsCommutingWeakDrazin weakA weakCommutingInverse 2 := by
  constructor
  · unfold IsWeakDrazin
    rw [weakA_pow_three, weakA_sq_readout]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakCommutingInverse]; try norm_num)
  · ext i j
    fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakA, weakCommutingInverse]; try norm_num)

/-! ## Strict finite `GL₃(Q)` conjugation readout -/

/-- A permutation matrix used as a concrete `GL₃(Q)` representative. -/
def weakPermutation : Mat3 ℚ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

/-- The permutation representative is its own inverse. -/
theorem weakPermutation_sq_eq_one :
    weakPermutation * weakPermutation = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, weakPermutation]; try norm_num)

/-- The permutation as a strict unit of the matrix algebra. -/
def weakPermutationUnit : (Mat3 ℚ)ˣ where
  val := weakPermutation
  inv := weakPermutation
  val_inv := weakPermutation_sq_eq_one
  inv_val := weakPermutation_sq_eq_one

/-- Unit conjugation on the matrix algebra. -/
def unitConj (u : (Mat3 ℚ)ˣ) (A : Mat3 ℚ) : Mat3 ℚ :=
  (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)

lemma unitConj_mul (u : (Mat3 ℚ)ˣ) (A B : Mat3 ℚ) :
    unitConj u A * unitConj u B = unitConj u (A * B) := by
  unfold unitConj
  calc
    (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * ((u : Mat3 ℚ) * B * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
      = (u : Mat3 ℚ) * A * (((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * (u : Mat3 ℚ)) * B * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
      simp only [mul_assoc]
    _ = (u : Mat3 ℚ) * (A * B) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
      simp only [Units.inv_mul, mul_one, mul_assoc]

lemma unitConj_pow (u : (Mat3 ℚ)ˣ) (A : Mat3 ℚ) (n : ℕ) :
    (unitConj u A) ^ n = unitConj u (A ^ n) := by
  induction n with
  | zero =>
    unfold unitConj
    simp only [pow_zero]
    calc
      (1 : Mat3 ℚ) = (u : Mat3 ℚ) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := (Units.mul_inv (u : (Mat3 ℚ)ˣ)).symm
      _ = (u : Mat3 ℚ) * 1 * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by simp only [mul_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, unitConj_mul]

/-- The weak Drazin relation is preserved by invertible unit conjugation. -/
theorem unitConj_isWeakDrazin (u : (Mat3 ℚ)ˣ) (A B : Mat3 ℚ) (k : ℕ)
    (h : IsWeakDrazin A B k) :
    IsWeakDrazin (unitConj u A) (unitConj u B) k := by
  unfold IsWeakDrazin at h ⊢
  rw [unitConj_pow, unitConj_pow, unitConj_mul, h]

/-- The weak Drazin relation is preserved by the concrete `GL₃(Q)` conjugation. -/
theorem weak_conjugated_polynomial_inverse_isWeak :
    IsWeakDrazin
      (unitConj weakPermutationUnit weakA)
      (unitConj weakPermutationUnit weakPolynomialInverse)
      2 :=
  unitConj_isWeakDrazin weakPermutationUnit weakA weakPolynomialInverse 2 weakPolynomialInverse_isWeak

end InfoGeometry.Canonical.CampbellMeyerWeakDrazin
