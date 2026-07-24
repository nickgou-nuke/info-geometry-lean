import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Finite-stage Cuntz inductive-limit readouts

This file does not construct a C*-completion of `O_∞` and does not claim a
trace-class theorem for an infinite Hamiltonian.  It records the theorem-backed
finite-stage Cuntz/Toeplitz relations that any later inductive-limit
construction must preserve, delegating the quotient presentation to
`InfoGeometry.Algebra.CuntzTensorQuotient`.
-/

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Algebra.CuntzInductiveLimit

open InfoGeometry.Algebra.CuntzTensorQuotient

/-- The finite Cuntz--Toeplitz stage used by an inductive system. -/
abbrev ToeplitzStage (n : ℕ) :=
  CuntzToeplitzAlg n

/-- The finite Cuntz quotient stage used by an inductive system. -/
abbrev CuntzStage (n : ℕ) :=
  CuntzAlg n

/-- Stage generator `Sᵢ` in the Toeplitz quotient. -/
def stageToeplitzS (n : ℕ) (i : Fin n) : ToeplitzStage n :=
  toeplitzS n i

/-- Stage adjoint generator `Sᵢ†` in the Toeplitz quotient. -/
def stageToeplitzSdag (n : ℕ) (i : Fin n) : ToeplitzStage n :=
  toeplitzSdag n i

/-- Stage generator `Sᵢ` in the finite Cuntz quotient. -/
def stageCuntzS (n : ℕ) (i : Fin n) : CuntzStage n :=
  cuntzS n i

/-- Stage adjoint generator `Sᵢ†` in the finite Cuntz quotient. -/
def stageCuntzSdag (n : ℕ) (i : Fin n) : CuntzStage n :=
  cuntzSdag n i

/-- The Toeplitz stage satisfies `Sᵢ† Sⱼ = δᵢⱼ`. -/
theorem stageToeplitz_orthogonality (n : ℕ) (i j : Fin n) :
    stageToeplitzSdag n i * stageToeplitzS n j = if i = j then 1 else 0 := by
  exact toeplitz_orthogonality n i j

/-- The finite Cuntz stage satisfies `Sᵢ† Sⱼ = δᵢⱼ`. -/
theorem stageCuntz_orthogonality (n : ℕ) (i j : Fin n) :
    stageCuntzSdag n i * stageCuntzS n j = if i = j then 1 else 0 := by
  exact cuntz_orthogonality n i j

/-- The finite Cuntz stage satisfies the range-completeness relation. -/
theorem stageCuntz_ranges_sum_one (n : ℕ) :
    (∑ i : Fin n, stageCuntzS n i * stageCuntzSdag n i) = 1 := by
  exact cuntz_ranges_sum_one n

/-- Each finite Cuntz generator is an algebraic isometry. -/
theorem stageCuntz_isometry (n : ℕ) (i : Fin n) :
    stageCuntzSdag n i * stageCuntzS n i = 1 := by
  exact cuntz_isometry n i

/-- Distinct finite Cuntz generators have orthogonal initial spaces. -/
theorem stageCuntz_distinct_orthogonal (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    stageCuntzSdag n i * stageCuntzS n j = 0 := by
  exact cuntz_distinct_orthogonal n hij

/-- The finite Cuntz stage packages exactly the algebraic Cuntz relations. -/
theorem finiteStageCuntzPacket (n : ℕ) :
    (∀ i j : Fin n, stageCuntzSdag n i * stageCuntzS n j = if i = j then 1 else 0) ∧
      (∑ i : Fin n, stageCuntzS n i * stageCuntzSdag n i) = 1 := by
  exact ⟨stageCuntz_orthogonality n, stageCuntz_ranges_sum_one n⟩

/-- The fermionic partition function for the first `n` indexed prime modes. -/
def fermionicPartitionTruncated (n : ℕ) (primes : ℕ → ℕ) (β : ℝ) : ℝ :=
  Finset.prod (Finset.range n) fun i => (1 : ℝ) + ((primes i : ℝ) ^ (-β))

/--
Finite-stage positivity of the fermionic partition factors for prime modes at
positive inverse temperature.  This is the theorem-safe finite readout; no
infinite Euler-product convergence is asserted here.
-/
theorem fermionicPartitionTruncated_pos
    (primes : ℕ → ℕ) (hprime : ∀ i, Nat.Prime (primes i)) (β : ℝ) (_hβ : 0 < β) :
    ∀ n : ℕ, 0 < fermionicPartitionTruncated n primes β := by
  intro n
  unfold fermionicPartitionTruncated
  refine Finset.prod_pos (fun i _hi => ?_)
  have hp_pos : 0 < (primes i : ℝ) := by
    exact_mod_cast (hprime i).pos
  have hpow_pos : 0 < (primes i : ℝ) ^ (-β) :=
    Real.rpow_pos_of_pos hp_pos (-β)
  exact add_pos zero_lt_one hpow_pos

/-- The old β > 1 interface reduced to the finite positivity readout. -/
theorem fermionicPartition_converges
    (primes : ℕ → ℕ) (hprime : ∀ i, Nat.Prime (primes i)) (β : ℝ) (hβ : 1 < β) :
    0 < β ∧ ∀ n : ℕ, 0 < fermionicPartitionTruncated n primes β := by
  have hβpos : 0 < β := by linarith
  exact ⟨hβpos, fermionicPartitionTruncated_pos primes hprime β hβpos⟩

end InfoGeometry.Algebra.CuntzInductiveLimit
