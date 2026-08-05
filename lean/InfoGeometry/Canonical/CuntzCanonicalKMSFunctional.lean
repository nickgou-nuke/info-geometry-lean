import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzKMSState

/-!
# Finite diagonal KMS functional

This owner stops at the native finite diagonal data.  The conditional
expectation in `CuntzConditionalExpectation` has codomain `CuntzAlg n`, not a
coefficient function, so it cannot be composed with a functional on
`Fin n → ℂ` without an additional diagonal-subalgebra construction.  We do
not introduce that missing identification here.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzKMSState

variable {n : ℕ}

/-- The finite diagonal KMS functional on diagonal coefficient functions. -/
noncomputable def diagonalKMSFunctional
    (primes : Fin n → ℕ) (β : ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  { toFun := fun c => ∑ i : Fin n, c i * kmsWeight n primes β i
    map_add' := by
      intro c d
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp [add_mul])
    map_smul' := by
      intro a c
      simp [Pi.smul_apply, Finset.mul_sum, mul_assoc] }

theorem diagonalKMSFunctional_apply
    (primes : Fin n → ℕ) (β : ℂ) (c : Fin n → ℂ) :
    diagonalKMSFunctional primes β c =
      ∑ i : Fin n, c i * kmsWeight n primes β i :=
  rfl

theorem diagonalKMSFunctional_matrix_unit_readout
    (primes : Fin n → ℕ) (β : ℂ) (i j : Fin n) :
    (if i = j then kmsWeight n primes β i else 0) =
      (if i = j then
        (primes i : ℂ) ^ (-β) / primonPartition n primes β
       else 0) := by
  by_cases hij : i = j
  · subst hij
    rfl
  · simp [hij]

theorem kmsWeight_eq_native
    (primes : Fin n → ℕ) (β : ℂ) (i : Fin n) :
    kmsWeight n primes β i =
      (primes i : ℂ) ^ (-β) / primonPartition n primes β :=
  kmsWeight_eq_boltzmann_div_partition n primes β i

end InfoGeometry.Canonical
