import Mathlib.Tactic

noncomputable section

namespace FiniteProjectorSpectralCalculus

open scoped BigOperators

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Orthogonal idempotent family. -/
def OrthogonalIdempotents (P : ι → A) : Prop :=
  ∀ i j : ι, P i * P j = if i = j then P i else 0

/-- Resolution of the identity. -/
def CompleteIdempotents (P : ι → A) : Prop :=
  (∑ i : ι, P i) = 1

/-- Diagonal Hamiltonian in an orthogonal idempotent basis. -/
def spectralHamiltonian (ε : ι → R) (P : ι → A) : A :=
  ∑ i : ι, (ε i) • P i

@[simp] theorem orthogonal_idempotent_sq {P : ι → A}
    (hP : OrthogonalIdempotents P) (i : ι) :
    P i * P i = P i := by
  simpa using hP i i

@[simp] theorem orthogonal_idempotent_mul_ne {P : ι → A}
    (hP : OrthogonalIdempotents P) {i j : ι} (hij : i ≠ j) :
    P i * P j = 0 := by
  simpa [hij] using hP i j

/-- Eigenprojection equation `H Pⱼ = εⱼ Pⱼ`. -/
theorem spectralHamiltonian_mul_projector
    (ε : ι → R) (P : ι → A) (hP : OrthogonalIdempotents P) (j : ι) :
    spectralHamiltonian ε P * P j = (ε j) • P j := by
  unfold spectralHamiltonian
  rw [Finset.sum_mul]
  trans ∑ i : ι, if i = j then (ε j) • P j else 0
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hij : i = j
    · subst hij
      simp [orthogonal_idempotent_sq hP]
    · simp [hij, orthogonal_idempotent_mul_ne hP hij]
  · rw [Finset.sum_ite_eq']
    simp

/-- Left eigenprojection equation `Pⱼ H = εⱼ Pⱼ`. -/
theorem projector_mul_spectralHamiltonian
    (ε : ι → R) (P : ι → A) (hP : OrthogonalIdempotents P) (j : ι) :
    P j * spectralHamiltonian ε P = (ε j) • P j := by
  unfold spectralHamiltonian
  rw [Finset.mul_sum]
  trans ∑ i : ι, if i = j then (ε j) • P j else 0
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hij : i = j
    · subst hij
      simp [orthogonal_idempotent_sq hP]
    · have hji : j ≠ i := by exact Ne.symm hij
      simp [hij, orthogonal_idempotent_mul_ne hP hji]
  · rw [Finset.sum_ite_eq']
    simp

/-- Powers preserve the same eigenprojectors: `H^k Pⱼ = εⱼ^k Pⱼ`. -/
theorem spectralHamiltonian_pow_mul_projector
    (ε : ι → R) (P : ι → A) (hP : OrthogonalIdempotents P) (j : ι) (k : ℕ) :
    (spectralHamiltonian ε P) ^ k * P j = (ε j) ^ k • P j := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (spectralHamiltonian ε P) ^ (k + 1) * P j
            = (spectralHamiltonian ε P) ^ k * (spectralHamiltonian ε P * P j) := by
              rw [pow_succ, mul_assoc]
        _ = (spectralHamiltonian ε P) ^ k * ((ε j) • P j) := by
              rw [spectralHamiltonian_mul_projector ε P hP j]
        _ = (ε j) • ((spectralHamiltonian ε P) ^ k * P j) := by
              rw [mul_smul_comm]
        _ = (ε j) • ((ε j) ^ k • P j) := by rw [ih]
        _ = (ε j) ^ (k + 1) • P j := by
              rw [smul_smul]
              congr 1
              rw [pow_succ']

/-- Finite spectral theorem for powers: `H^k = Σ εᵢ^k Pᵢ`. -/
theorem spectralHamiltonian_pow
    (ε : ι → R) (P : ι → A)
    (hP : OrthogonalIdempotents P) (hcomplete : CompleteIdempotents P) (k : ℕ) :
    (spectralHamiltonian ε P) ^ k = ∑ i : ι, (ε i) ^ k • P i := by
  calc
    (spectralHamiltonian ε P) ^ k = (spectralHamiltonian ε P) ^ k * 1 := by simp
    _ = (spectralHamiltonian ε P) ^ k * (∑ i : ι, P i) := by rw [hcomplete]
    _ = ∑ i : ι, (spectralHamiltonian ε P) ^ k * P i := by rw [Finset.mul_sum]
    _ = ∑ i : ι, (ε i) ^ k • P i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact spectralHamiltonian_pow_mul_projector ε P hP i k

/-- Finite polynomial functional calculus for coefficients indexed by `range d`. -/
def finitePolynomialEval (c : ℕ → R) (d : ℕ) (x : A) : A :=
  (Finset.range d).sum fun n => (c n) • x ^ n

/-- Coefficient-side value of the same finite polynomial. -/
def coefficientPolynomialEval (c : ℕ → R) (d : ℕ) (x : R) : R :=
  (Finset.range d).sum fun n => c n * x ^ n

/-- Polynomial functional calculus for a finite orthogonal-idempotent spectral resolution. -/
theorem finitePolynomialEval_spectralHamiltonian
    (c : ℕ → R) (d : ℕ) (ε : ι → R) (P : ι → A)
    (hP : OrthogonalIdempotents P) (hcomplete : CompleteIdempotents P) :
    finitePolynomialEval c d (spectralHamiltonian ε P) =
      ∑ i : ι, (coefficientPolynomialEval c d (ε i)) • P i := by
  unfold finitePolynomialEval coefficientPolynomialEval
  calc
    ((Finset.range d).sum fun n => (c n) • (spectralHamiltonian ε P) ^ n)
        = ((Finset.range d).sum fun n => (c n) • (∑ i : ι, (ε i) ^ n • P i)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [spectralHamiltonian_pow ε P hP hcomplete n]
    _ = ((Finset.range d).sum fun n => ∑ i : ι, (c n) • ((ε i) ^ n • P i)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.smul_sum]
    _ = ∑ i : ι, (Finset.range d).sum fun n => (c n) • ((ε i) ^ n • P i) := by
          rw [Finset.sum_comm]
    _ = ∑ i : ι, (Finset.range d).sum fun n => (c n * (ε i) ^ n) • P i := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro n hn
          rw [smul_smul]
    _ = ∑ i : ι, ((Finset.range d).sum fun n => c n * (ε i) ^ n) • P i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_smul]

#check spectralHamiltonian_mul_projector
#check projector_mul_spectralHamiltonian
#check spectralHamiltonian_pow_mul_projector
#check spectralHamiltonian_pow
#check finitePolynomialEval_spectralHamiltonian

end FiniteProjectorSpectralCalculus
