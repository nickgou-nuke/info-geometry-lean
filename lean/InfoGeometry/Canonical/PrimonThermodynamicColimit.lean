import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.External.Auto.FermionicPrimonPartition

/-!
# Primon Thermodynamic Colimit

This module constructs the finite-to-infinite categorical limit of the fermionic
Primon gas thermodynamics, satisfying the strict Colimit Continuum Mandate.

We use the audited diagonal successor embeddings from `UHFInductiveColimitBoundary`
to construct the exact algebraic skeleton:
1. The inductive limit (colimit) of the diagonal observables `DiagAlg n`.
2. The projective limit (inverse limit) of the finite Gibbs states `expectedValue`.

No classical analysis, measure theory, or analytic continuation is used. The
thermodynamic limit is structurally defined by the compatibility of the finite
expectation values under the algebraic stage maps.
-/

noncomputable section

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

namespace InfoGeometry.Canonical.PrimonThermodynamicColimit

variable (primes : ℕ → ℕ) (β : ℝ)

/-- Unnormalized Boltzmann weight of a configuration `w : BitWord n` evaluated over the first `n` prime modes. -/
def finiteBoltzmannWeight (n : ℕ) (w : BitWord n) : ℝ :=
  (Finset.univ : Finset (Fin n)).prod fun i => fermionOccupationWeight (primes i) β (w i)

/-- The partition function is the strictly finite sum of unnormalized weights. -/
def finitePartitionFunction (n : ℕ) : ℝ :=
  (Finset.univ : Finset (BitWord n)).sum (finiteBoltzmannWeight primes β n)

/-- The normalized thermodynamic Gibbs state (probability measure on `BitWord n`). -/
def finiteGibbsState (n : ℕ) (w : BitWord n) : ℝ :=
  finiteBoltzmannWeight primes β n w / finitePartitionFunction primes β n

/-- The expected value of a diagonal observable `f : DiagAlg n` at stage `n`. -/
def expectedValue (n : ℕ) (f : DiagAlg n) : ℂ :=
  (Finset.univ : Finset (BitWord n)).sum fun w => f w * (finiteGibbsState primes β n w : ℂ)

/-- The single-prime partition factor at stage `n`. -/
def singlePrimeFactor (n : ℕ) : ℝ :=
  singlePrimeFermionPartition (primes n) β

theorem singlePrimeFactor_pos (n : ℕ) : 0 < singlePrimeFactor primes β n := by
  dsimp [singlePrimeFactor]
  rw [singlePrimeFermionPartition_eq]
  dsimp [fermionPrimeBoltzmannWeight]
  have h1 : (0 : ℝ) ≤ (primes n : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (primes n : ℝ) ^ (-β) := Real.rpow_nonneg h1 _
  linarith

theorem singlePrimeFactor_ne_zero (n : ℕ) : (singlePrimeFactor primes β n : ℂ) ≠ 0 := by
  have hpos := singlePrimeFactor_pos primes β n
  have hne : singlePrimeFactor primes β n ≠ 0 := ne_of_gt hpos
  exact_mod_cast hne

/-- The unnormalized Boltzmann weight factorizes when adding the `n`-th prime mode. -/
theorem finiteBoltzmannWeight_succ (n : ℕ) (w : BitWord (n + 1)) :
    finiteBoltzmannWeight primes β (n + 1) w =
      finiteBoltzmannWeight primes β n (prefixSucc n w) *
        fermionOccupationWeight (primes n) β (w ⟨n, Nat.lt_succ_self n⟩) := by
  dsimp [finiteBoltzmannWeight, prefixSucc]
  rw [Fin.prod_univ_castSucc]
  rfl

variable (n : ℕ)

def bitWordEquiv (n : ℕ) : BitWord (n + 1) ≃ (BitWord n × Bool) where
  toFun w := (prefixSucc n w, w ⟨n, Nat.lt_succ_self n⟩)
  invFun p := extendSucc n p.1 p.2
  left_inv w := by
    ext i
    dsimp [prefixSucc, extendSucc]
    split_ifs with h
    · rfl
    · have hi : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (Nat.le_antisymm (Nat.le_of_lt_succ i.2) (Nat.le_of_not_lt h))
      subst hi
      rfl
  right_inv p := by
    rcases p with ⟨w, b⟩
    ext
    · dsimp; rw [prefixSucc_extendSucc]
    · dsimp [extendSucc]; rw [dif_neg (lt_irrefl n)]

/-- The finite partition function factorizes exactly. -/
theorem finitePartitionFunction_succ :
    finitePartitionFunction primes β (n + 1) =
      finitePartitionFunction primes β n * singlePrimeFactor primes β n := by
  dsimp [finitePartitionFunction, singlePrimeFactor, singlePrimeFermionPartition]
  rw [← Equiv.sum_comp (bitWordEquiv n).symm]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hw : (bitWordEquiv n).symm (w, b) = extendSucc n w b := rfl
  rw [hw]
  have hb : (extendSucc n w b) ⟨n, Nat.lt_succ_self n⟩ = b := by
    dsimp [extendSucc]
    rw [dif_neg (lt_irrefl n)]
  rw [finiteBoltzmannWeight_succ, prefixSucc_extendSucc, hb]

/-- 
**Zero Defect Projective Compatibility**:
The expected value is strictly invariant under the diagonal successor embedding. 
This establishes the consistent projective limit of states over the inductive limit 
of observables, serving as the algebraic thermodynamic limit.
-/
theorem expectedValue_compatible_succ (f : DiagAlg n) :
    expectedValue primes β (n + 1) (diagEmbedSucc n f) = expectedValue primes β n f := by
  dsimp [expectedValue, finiteGibbsState]
  rw [← Equiv.sum_comp (bitWordEquiv n).symm]
  rw [Fintype.sum_prod_type]
  rw [finitePartitionFunction_succ primes β n]
  push_cast
  have h_pull_f : ∀ w b, diagEmbedSucc n f ((bitWordEquiv n).symm (w, b)) = f w := by
    intro w b
    dsimp [diagEmbedSucc, bitWordEquiv]
    rw [prefixSucc_extendSucc]
  simp_rw [h_pull_f]
  apply Finset.sum_congr rfl
  intro w _
  have hw_weight : ∀ b, finiteBoltzmannWeight primes β (n + 1) ((bitWordEquiv n).symm (w, b)) =
      finiteBoltzmannWeight primes β n w * fermionOccupationWeight (primes n) β b := by
    intro b
    have h1 : (bitWordEquiv n).symm (w, b) = extendSucc n w b := rfl
    rw [h1, finiteBoltzmannWeight_succ, prefixSucc_extendSucc]
    have hb : (extendSucc n w b) ⟨n, Nat.lt_succ_self n⟩ = b := by dsimp [extendSucc]; rw [dif_neg (lt_irrefl n)]
    rw [hb]
  simp_rw [hw_weight]
  have h_frac_eq : (fun b => f w * (↑(finiteBoltzmannWeight primes β n w * fermionOccupationWeight (primes n) β b) / (↑(finitePartitionFunction primes β n) * ↑(singlePrimeFactor primes β n)))) =
      fun b => (f w * ↑(finiteBoltzmannWeight primes β n w) / ↑(finitePartitionFunction primes β n)) * ((fermionOccupationWeight (primes n) β b : ℂ) / (singlePrimeFactor primes β n : ℂ)) := by
    ext b
    push_cast
    ring
  rw [h_frac_eq, ← Finset.mul_sum]
  have h_sum_b : (Finset.univ : Finset Bool).sum (fun b => (fermionOccupationWeight (primes n) β b : ℂ) / (singlePrimeFactor primes β n : ℂ)) = 1 := by
    rw [← Finset.sum_div]
    have h_single : (Finset.univ : Finset Bool).sum (fun b => (fermionOccupationWeight (primes n) β b : ℂ)) = (singlePrimeFactor primes β n : ℂ) := by
      dsimp [singlePrimeFactor, singlePrimeFermionPartition]
      push_cast
      rfl
    rw [h_single]
    exact div_self (singlePrimeFactor_ne_zero primes β n)
  rw [h_sum_b]
  ring

end InfoGeometry.Canonical.PrimonThermodynamicColimit
end noncomputable section
