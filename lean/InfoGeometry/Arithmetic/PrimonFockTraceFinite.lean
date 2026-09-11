import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite primon Fock trace

This file proves the finite Fock-space trace identity for a diagonal primon
Hamiltonian.  It is the finite CAR/Fock representation layer: occupation
profiles are Boolean basis states, number projectors are diagonal idempotents,
and the finite Gibbs trace factors into local two-state contributions.

No infinite Euler product, analytic continuation, or RH claim is made here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimonFockTraceFinite

/-- Finite fermionic Fock basis: a Boolean occupation bit at each mode. -/
abbrev FockState (n : ℕ) := Fin n → Bool

/-- Complex-valued finite Fock vectors. -/
abbrev FockVec (n : ℕ) := FockState n → ℂ

/-- Diagonal finite primon energy of an occupation profile. -/
def fockEnergy (n : ℕ) (ε : Fin n → ℝ) (occ : FockState n) : ℝ :=
  ∑ i : Fin n, if occ i then ε i else 0

lemma fockEnergy_nonneg {n : ℕ} {ε : Fin n → ℝ}
    (hε : ∀ i, 0 ≤ ε i) (occ : FockState n) :
    0 ≤ fockEnergy n ε occ := by
  unfold fockEnergy
  exact Finset.sum_nonneg (fun i _hi => by
    by_cases h : occ i
    · simp [h, hε i]
    · simp [h])

/-- The diagonal number projector `Nᵢ` on finite Fock space. -/
def numberProjector (n : ℕ) (i : Fin n) (ψ : FockVec n) : FockVec n :=
  fun occ => (if occ i then (1 : ℂ) else 0) * ψ occ

/-- The diagonal finite primon Hamiltonian `H = Σ εᵢ Nᵢ`. -/
def fockHamiltonian (n : ℕ) (ε : Fin n → ℝ) (ψ : FockVec n) : FockVec n :=
  fun occ => (fockEnergy n ε occ : ℂ) * ψ occ

/-- Basis vector for an occupation profile. -/
def basisVector {n : ℕ} (occ0 : FockState n) : FockVec n :=
  fun occ => if occ = occ0 then 1 else 0

/-- Number projectors are idempotent. -/
theorem numberProjector_idempotent (n : ℕ) (i : Fin n) (ψ : FockVec n) :
    numberProjector n i (numberProjector n i ψ) = numberProjector n i ψ := by
  funext occ
  unfold numberProjector
  by_cases h : occ i <;> simp [h]

/-- Number projectors commute. -/
theorem numberProjector_commute (n : ℕ) (i j : Fin n) (ψ : FockVec n) :
    numberProjector n i (numberProjector n j ψ) =
      numberProjector n j (numberProjector n i ψ) := by
  funext occ
  unfold numberProjector
  by_cases hi : occ i <;> by_cases hj : occ j <;> simp [hi, hj, mul_comm]

/-- Occupation basis vectors are eigenvectors of the diagonal Hamiltonian. -/
theorem fockHamiltonian_on_basis (n : ℕ) (ε : Fin n → ℝ) (occ0 : FockState n) :
    fockHamiltonian n ε (basisVector occ0) =
      (fockEnergy n ε occ0 : ℂ) • basisVector occ0 := by
  funext occ
  unfold fockHamiltonian basisVector
  by_cases h : occ = occ0
  · subst occ
    simp
  · simp [h]

/-- Local Boltzmann factor for one fermionic mode. -/
def localBoltzmann (εi β : ℝ) : ℝ :=
  Real.exp (-β * εi)

lemma localBoltzmann_pos (εi β : ℝ) :
    0 < localBoltzmann εi β := by
  unfold localBoltzmann
  exact Real.exp_pos _

lemma localBoltzmann_ne_zero (εi β : ℝ) :
    localBoltzmann εi β ≠ 0 :=
  (localBoltzmann_pos εi β).ne'

/-- Finite Fock trace of `exp(-βH)` for the diagonal Hamiltonian. -/
def fockTraceExp (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) : ℝ :=
  ∑ occ : FockState n, Real.exp (-β * fockEnergy n ε occ)

lemma fockTraceExp_nonneg (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    0 ≤ fockTraceExp n ε β := by
  unfold fockTraceExp
  exact Finset.sum_nonneg (fun occ _hocc => le_of_lt (Real.exp_pos _))

/-- The Gibbs weight of a profile factors into local occupation weights. -/
theorem exp_neg_mul_fockEnergy_eq_prod (n : ℕ) (ε : Fin n → ℝ) (β : ℝ)
    (occ : FockState n) :
    Real.exp (-β * fockEnergy n ε occ) =
      ∏ i : Fin n, if occ i then localBoltzmann (ε i) β else 1 := by
  unfold fockEnergy localBoltzmann
  rw [show -β * (∑ i : Fin n, if occ i then ε i else 0) =
      ∑ i : Fin n, (-β) * (if occ i then ε i else 0) by rw [Finset.mul_sum]]
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  by_cases h : occ i <;> simp [h]

/-- Finite fermionic primon trace factors into the product of local two-state traces. -/
theorem fockTraceExp_eq_product (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    fockTraceExp n ε β = ∏ i : Fin n, (1 + localBoltzmann (ε i) β) := by
  classical
  unfold fockTraceExp
  simp_rw [exp_neg_mul_fockEnergy_eq_prod]
  have hlocal : ∀ i : Fin n,
      ((∑ b : Bool, if b then localBoltzmann (ε i) β else 1) : ℝ) =
        1 + localBoltzmann (ε i) β := by
    intro i
    simp
    ring
  rw [← Finset.prod_congr rfl (fun i _hi => hlocal i)]
  rw [← Finset.sum_prod_piFinset]
  rw [Fintype.piFinset_univ]

lemma fockTraceExp_pos (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    0 < fockTraceExp n ε β := by
  rw [fockTraceExp_eq_product]
  exact Finset.prod_pos (fun i _hi =>
    add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt (localBoltzmann_pos (ε i) β)))

lemma fockTraceExp_ne_zero (n : ℕ) (ε : Fin n → ℝ) (β : ℝ) :
    fockTraceExp n ε β ≠ 0 :=
  (fockTraceExp_pos n ε β).ne'

/-- Primon specialization `εᵢ = log pᵢ`: finite trace as a prime Euler factor product. -/
theorem primonFockTrace_eq_primeProduct (n : ℕ) (p : Fin n → ℕ) (β : ℝ) :
    fockTraceExp n (fun i => Real.log (p i : ℝ)) β =
      ∏ i : Fin n, (1 + Real.exp (-β * Real.log (p i : ℝ))) := by
  simpa [localBoltzmann] using
    fockTraceExp_eq_product n (fun i => Real.log (p i : ℝ)) β

end InfoGeometry.Arithmetic.PrimonFockTraceFinite
