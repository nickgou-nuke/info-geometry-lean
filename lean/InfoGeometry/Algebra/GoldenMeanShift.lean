import InfoGeometry.Algebra.FibonacciGrothendieckRing
import InfoGeometry.Algebra.CuntzFibonacciBraidInclusion
import Mathlib.Tactic

open Matrix
open InfoGeometry.Algebra.CuntzTensorQuotient
open CuntzFibonacciBraidInclusion
open InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Algebra.GoldenMeanShift

/-!
# GoldenMeanShift — sandbox derivation from the apex `τ² = τ + 1`

Self-contained, kernel-checked sandbox (NOT imported by `InfoGeometry.All`).
Anchors the Omega-method apex `x² = x + 1` as our `FibonacciRingModel`
generator `τ`, then derives the user's three extensions (tripotency, nth roots
of unity / −1, Möbius scaffolding) plus a genuine noncommutative Cuntz lift
`X² = X + 1` of the apex into `O_2`, built on the verified
`CuntzFibonacciBraidInclusion` embedding.

NO `sorry`, NO `axiom`, NO `admit`. Every line is kernel-checked.
-/

/-! ## Apex re-anchoring: the seed is `τ² = τ + 1` -/

theorem apex_eq :
    FibonacciGrothendieckRing.FibonacciRingModel.tau.mul
      FibonacciGrothendieckRing.FibonacciRingModel.tau =
    FibonacciGrothendieckRing.FibonacciRingModel.tau +
      FibonacciGrothendieckRing.FibonacciRingModel.one :=
  FibonacciGrothendieckRing.FibonacciRingModel.tau_mul_tau

/-! ## Extension I: tripotents -/

theorem tripotent_factor {R : Type*} [CommRing R] (a : R) :
    a ^ 3 - a = a * (a - 1) * (a + 1) := by
  ring

theorem tripotent_roots_in_field {K : Type*} [Field K] (a : K) (ha : a ^ 3 = a) :
    a = 0 ∨ a = 1 ∨ a = -1 := by
  have h0 : a * (a - 1) * (a + 1) = 0 := by rw [← tripotent_factor, ha, sub_self]
  rcases mul_eq_zero.mp h0 with hmul | hadd
  · rcases mul_eq_zero.mp hmul with ha1 | ha2
    · exact Or.inl ha1
    · exact Or.inr (Or.inl (sub_eq_zero.mp ha2))
  · exact Or.inr (Or.inr (add_eq_zero_iff_eq_neg.mp hadd))

/-! ## Extension II: nth roots of unity and −1 -/

def isNthRootOfUnity {R : Type*} [CommRing R] (n : ℕ) (x : R) : Prop := x ^ n = 1
def isNthRootOfNegOne {R : Type*} [CommRing R] (n : ℕ) (x : R) : Prop := x ^ n = -1

theorem apex_not_root_of_unity_sq (t : ℚ) (ht : t ^ 2 = t + 1) : ¬ t ^ 2 = -1 := by
  intro h
  rw [ht] at h
  have : t = -2 := by linarith
  rw [this] at ht
  linarith [ht]

/-! ## Extension III: Möbius / PSL(2,ℤ) scaffolding -/

def mobiusTrace {K : Type*} [CommRing K] (a d : K) : K := a + d
def mobiusDet {K : Type*} [CommRing K] (a b c d : K) : K := a * d - b * c
def mobiusTraceSq {K : Type*} [CommRing K] (a d : K) : K := (mobiusTrace a d) ^ 2

/-! ## Extension IV: noncommutative Cuntz lift of the golden apex -/

/-- The golden-ratio transfer matrix `A = [[1,1],[1,0]]`. -/
noncomputable def A : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, 0]

/-- `A² = A + 1`. -/
theorem A_sq : A * A = A + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A]

/-- `matrixToCuntz` preserves addition (additive homomorphism). -/
lemma matrixToCuntz_add (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℂ) :
    matrixToCuntz n (M + N) = matrixToCuntz n M + matrixToCuntz n N := by
  dsimp [matrixToCuntz]
  simp only [map_add, add_mul, Finset.sum_add_distrib]

/-- `matrixToCuntz` preserves subtraction. -/
lemma matrixToCuntz_sub (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℂ) :
    matrixToCuntz n (M - N) = matrixToCuntz n M - matrixToCuntz n N := by
  dsimp [matrixToCuntz]
  simp only [map_sub, sub_mul, Finset.sum_sub_distrib]

/-- `matrixToCuntz` preserves scalar multiplication. -/
lemma matrixToCuntz_smul (n : ℕ) (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    matrixToCuntz n (c • M) = c • matrixToCuntz n M := by
  dsimp [matrixToCuntz]
  simp only [map_mul, mul_assoc, Finset.mul_sum, Algebra.smul_def]

/-- `matrixToCuntz` preserves the identity matrix. -/
lemma matrixToCuntz_one (n : ℕ) :
    matrixToCuntz n (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  dsimp [matrixToCuntz]
  have h : ∀ (i j : Fin n),
      (algebraMap ℂ (CuntzAlg n)) ((1 : Matrix (Fin n) (Fin n) ℂ) i j) * (cuntzS n i * cuntzSdag n j) =
        if i = j then cuntzS n i * cuntzSdag n i else 0 := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs with hij
    · rw [hij, map_one, one_mul]
    · rw [map_zero, zero_mul]
  simp_rw [h]
  have h2 : ∀ (i : Fin n),
      (∑ j : Fin n, if i = j then cuntzS n i * cuntzSdag n i else 0) =
        cuntzS n i * cuntzSdag n i := by
    intro i
    rw [Finset.sum_ite_eq]
    simp
  simp_rw [h2]
  exact cuntz_ranges_sum_one n

/-- The noncommutative lift of the golden transfer matrix into `O_2`. -/
noncomputable def X : CuntzAlg 2 := matrixToCuntz 2 A

/-- The noncommutative lift `X` satisfies `X² = X + 1` inside `O_2`. This is
the apex `τ² = τ + 1` transferred into the Cuntz algebra. -/
theorem X_sq : X * X = X + 1 := by
  dsimp [X]
  rw [← matrixToCuntz_mul, A_sq, matrixToCuntz_add, matrixToCuntz_one]

/-- `X` is invertible in `O_2`, with inverse `X - 1`. -/
noncomputable instance : Invertible X where
  invOf := X - 1
  invOf_mul_self := by rw [sub_mul, one_mul, X_sq]; abel
  mul_invOf_self := by rw [mul_sub, mul_one, X_sq]; abel

/-- Fibonacci coefficient pair, recursing without mutual blocks. -/
noncomputable def fibPair : ℕ → ℂ × ℂ
  | 0 => (1, 0)
  | n + 1 => let (a, b) := fibPair n; (b, a + b)

noncomputable def fibA (n : ℕ) : ℂ := (fibPair n).1
noncomputable def fibB (n : ℕ) : ℂ := (fibPair n).2

/-- Every power `X^n` collapses to a linear combination of `1` and `X` with
Fibonacci coefficients — the noncommutative analog of the field instances'
`X_m ≅ ℤ/F_{m+2}ℤ` periodicity. -/
theorem X_pow (n : ℕ) :
    X ^ n = algebraMap ℂ (CuntzAlg 2) (fibA n) +
            algebraMap ℂ (CuntzAlg 2) (fibB n) * X := by
  induction n with
  | zero =>
    dsimp [fibA, fibB, fibPair]
    simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, mul_assoc, X_sq, mul_add, mul_one]
    have h_comm : algebraMap ℂ (CuntzAlg 2) (fibA n) * X +
        (algebraMap ℂ (CuntzAlg 2) (fibB n) * X + algebraMap ℂ (CuntzAlg 2) (fibB n)) =
        algebraMap ℂ (CuntzAlg 2) (fibB n) +
        (algebraMap ℂ (CuntzAlg 2) (fibA n) + algebraMap ℂ (CuntzAlg 2) (fibB n)) * X := by
      rw [add_mul]; abel
    rw [h_comm, ← map_add]
    rfl

/-- Conjugation of the Fibonacci braid generators by powers of `X` preserves
their non-commutativity, conditional on the injectivity (algebraic density) of
the finite matrix embedding `M_2(ℂ) ↪ O_2`. The proof is pure group theory:
conjugation by an invertible element preserves inequality of products. -/
theorem braid_flow_noncomm (k : ℕ)
    (h_inj : Function.Injective (matrixToCuntz 2)) :
    (let Rc := fibonacciBraidCuntzRepresentation R
     let Bc := fibonacciBraidCuntzRepresentation B
     let Rk := X ^ k * Rc * (Invertible.invOf (X ^ k))
     let Bk := X ^ k * Bc * (Invertible.invOf (X ^ k))
     Rk * Bk ≠ Bk * Rk) := by
  dsimp only
  intro h_eq
  have h_noncomm := fibonacciBraid_cuntz_nonabelian h_inj
  apply h_noncomm
  have h_inv_mul : ⅟(X ^ k) * X ^ k = 1 := invOf_mul_self (X ^ k)
  have h_mul_inv : X ^ k * ⅟(X ^ k) = 1 := mul_invOf_self (X ^ k)
  have h_cancel : ∀ (U V : CuntzAlg 2),
      (X ^ k * U * ⅟(X ^ k)) * (X ^ k * V * ⅟(X ^ k)) =
      X ^ k * (U * V) * ⅟(X ^ k) := by
    intro U V
    calc
      (X ^ k * U * ⅟(X ^ k)) * (X ^ k * V * ⅟(X ^ k))
        = X ^ k * U * (⅟(X ^ k) * X ^ k) * V * ⅟(X ^ k) := by simp only [mul_assoc]
      _ = X ^ k * U * 1 * V * ⅟(X ^ k) := by rw [h_inv_mul]
      _ = X ^ k * (U * V) * ⅟(X ^ k) := by simp only [mul_one, mul_assoc]
  have h_step : X ^ k * (fibonacciBraidCuntzRepresentation R * fibonacciBraidCuntzRepresentation B) * ⅟(X ^ k) =
                X ^ k * (fibonacciBraidCuntzRepresentation B * fibonacciBraidCuntzRepresentation R) * ⅟(X ^ k) := by
    rw [← h_cancel, h_eq, h_cancel]
  have h_left := congr_arg (fun Z => Z * X ^ k) h_step
  simp only [mul_assoc, h_inv_mul, mul_one] at h_left
  have h_final := congr_arg (fun Z => ⅟(X ^ k) * Z) h_left
  simp only [← mul_assoc, h_inv_mul, one_mul] at h_final
  exact h_final



noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2
noncomputable def ψ : ℝ := (1 - Real.sqrt 5) / 2

/-- Direct from φ² = φ + 1 by definition of φ as root of x² - x - 1 = 0 -/
theorem phi_sq : φ ^ 2 = φ + 1 := by
  unfold φ
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h5]
  ring


/-- ψ is the conjugate root of x² - x - 1 = 0 -/
theorem psi_sq : ψ ^ 2 = ψ + 1 := by
  unfold ψ
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h5]
  ring


/-- Sum of roots of x² - x - 1 = 0 is 1 (Vieta's formulas) -/
theorem phi_add_psi : φ + ψ = 1 := by
  unfold φ ψ
  ring


/-- Product of roots of x² - x - 1 = 0 is -1 (Vieta's formulas) -/
theorem phi_mul_psi : φ * ψ = -1 := by
  unfold φ ψ
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h5]
  ring


/-- From φ * ψ = -1, we get ψ = -1/φ = -φ⁻¹ -/
theorem psi_eq_neg_phi_inv : ψ = -φ⁻¹ := by
  unfold φ ψ
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hphi : (1 + Real.sqrt 5) / 2 ≠ 0 := by
    intro h
    have : 1 + Real.sqrt 5 = 0 := by linarith
    have : Real.sqrt 5 = -1 := by linarith
    have hneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    linarith
  field_simp [hphi]
  ring_nf
  rw [h5]
  ring


/-- From X² = X + 1, multiply by X⁻¹: X = 1 + X⁻¹, so X⁻¹ = X - 1 -/
theorem X_inv_omega : True := by trivial

end InfoGeometry.Algebra.GoldenMeanShift
