import Mathlib
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-!
# InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

Finite ferromagnetic prime-chain data for the Lee--Yang route.

This module records the concrete interaction matrix suggested by the
prime-chain picture:

`Jᵢⱼ = κ log(pᵢ) log(pⱼ)`.

For a finite list of prime-labelled sites and `κ ≥ 0`, it proves the basic
ferromagnetic facts:

* `Jᵢⱼ ≥ 0`;
* `Jᵢⱼ = Jⱼᵢ`;
* if `κ > 0`, then `Jᵢⱼ > 0`.

It also defines a finite Ising Hamiltonian with external field/fugacity
readout. The actual Lee--Yang circle theorem for the resulting partition
polynomial is deliberately a witness socket; this file does not prove
Lee--Yang stability, analytic continuation of `xi`, or RH.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-! ## Spins -/

/-- Two Ising spin states. -/
inductive IsingSpin where
  | up
  | down
deriving DecidableEq, Fintype, Repr

namespace IsingSpin

/-- Real sign readout for an Ising spin. -/
def sign : IsingSpin → ℝ
  | up => 1
  | down => -1

@[simp]
theorem sign_up :
    sign up = 1 := rfl

@[simp]
theorem sign_down :
    sign down = -1 := rfl

@[simp]
theorem sign_sq
    (σ : IsingSpin) :
    sign σ * sign σ = 1 := by
  cases σ <;> norm_num [sign]

end IsingSpin

/-! ## Prime ferromagnetic chain -/

/--
A finite prime-labelled ferromagnetic chain.

`prime i` is the arithmetic label at site `i`.
`κ` is the global ferromagnetic coupling scale.
-/
structure PrimeFerromagneticChain
    (n : ℕ) where
  prime : Fin n → ℕ
  prime_law : ∀ i : Fin n, Nat.Prime (prime i)
  kappa : ℝ
  kappa_nonneg : 0 ≤ kappa

namespace PrimeFerromagneticChain

variable {n : ℕ}
variable (C : PrimeFerromagneticChain n)

/-- Site energy `log pᵢ`. -/
def siteEnergy
    (i : Fin n) : ℝ :=
  Real.log (C.prime i : ℝ)

/-- Prime-chain ferromagnetic interaction matrix `Jᵢⱼ = κ log(pᵢ) log(pⱼ)`. -/
def coupling
    (i j : Fin n) : ℝ :=
  C.kappa * C.siteEnergy i * C.siteEnergy j

/-- The interaction matrix as a finite real matrix. -/
def couplingMatrix : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => C.coupling i j

/-- Prime-site logarithmic energy is nonnegative. -/
theorem siteEnergy_nonneg
    (i : Fin n) :
    0 ≤ C.siteEnergy i := by
  unfold siteEnergy
  exact Real.log_nonneg (by
    exact_mod_cast (Nat.Prime.one_lt (C.prime_law i)).le)

/-- Prime-site logarithmic energy is positive. -/
theorem siteEnergy_pos
    (i : Fin n) :
    0 < C.siteEnergy i := by
  unfold siteEnergy
  exact Real.log_pos (by
    exact_mod_cast Nat.Prime.one_lt (C.prime_law i))

/-- The prime-chain interaction is ferromagnetic: `Jᵢⱼ ≥ 0`. -/
theorem coupling_nonneg
    (i j : Fin n) :
    0 ≤ C.coupling i j := by
  unfold coupling
  exact mul_nonneg (mul_nonneg C.kappa_nonneg (C.siteEnergy_nonneg i))
    (C.siteEnergy_nonneg j)

/-- The interaction matrix is symmetric. -/
theorem coupling_symm
    (i j : Fin n) :
    C.coupling i j = C.coupling j i := by
  unfold coupling
  ring

/-- Strictly positive coupling scale gives strictly positive pair couplings. -/
theorem coupling_pos
    (hκ : 0 < C.kappa)
    (i j : Fin n) :
    0 < C.coupling i j := by
  unfold coupling
  exact mul_pos (mul_pos hκ (C.siteEnergy_pos i)) (C.siteEnergy_pos j)

/-- Matrix readout of the coupling entry. -/
@[simp]
theorem couplingMatrix_apply
    (i j : Fin n) :
    C.couplingMatrix i j = C.coupling i j := rfl

/-- The coupling matrix has nonnegative entries. -/
theorem couplingMatrix_entry_nonneg
    (i j : Fin n) :
    0 ≤ C.couplingMatrix i j :=
  C.coupling_nonneg i j

/-- The coupling matrix is symmetric entrywise. -/
theorem couplingMatrix_symm
    (i j : Fin n) :
    C.couplingMatrix i j = C.couplingMatrix j i :=
  C.coupling_symm i j

/-! ## Hamiltonian and fugacity readout -/

/-- A spin configuration on the finite chain. -/
abbrev SpinConfiguration :=
  Fin n → IsingSpin

/-- Pair interaction energy `-Σᵢⱼ Jᵢⱼ σᵢ σⱼ`. -/
def pairEnergy
    (σ : SpinConfiguration (n := n)) : ℝ :=
  -∑ i : Fin n, ∑ j : Fin n,
    C.coupling i j * IsingSpin.sign (σ i) * IsingSpin.sign (σ j)

/-- External-field energy `-Σᵢ hᵢ σᵢ`. -/
def fieldEnergy
    (h : Fin n → ℝ)
    (σ : SpinConfiguration (n := n)) : ℝ :=
  -∑ i : Fin n, h i * IsingSpin.sign (σ i)

/-- Finite Ising Hamiltonian for the prime ferromagnetic chain. -/
def isingHamiltonian
    (h : Fin n → ℝ)
    (σ : SpinConfiguration (n := n)) : ℝ :=
  C.pairEnergy σ + fieldEnergy h σ

/-- The pair-energy definition unfolded. -/
theorem pairEnergy_eq
    (σ : SpinConfiguration (n := n)) :
    C.pairEnergy σ =
      -∑ i : Fin n, ∑ j : Fin n,
        C.coupling i j * IsingSpin.sign (σ i) * IsingSpin.sign (σ j) := rfl

/-- The field-energy definition unfolded. -/
theorem fieldEnergy_eq
    (h : Fin n → ℝ)
    (σ : SpinConfiguration (n := n)) :
    fieldEnergy h σ =
      -∑ i : Fin n, h i * IsingSpin.sign (σ i) := rfl

/-- The Hamiltonian definition unfolded. -/
theorem isingHamiltonian_eq_pair_add_field
    (h : Fin n → ℝ)
    (σ : SpinConfiguration (n := n)) :
    C.isingHamiltonian h σ = C.pairEnergy σ + fieldEnergy h σ := rfl

/--
Field/fugacity dictionary for one site:

`zᵢ = exp(-2 hᵢ)`.

The Cayley map in `CayleyCriticalLineCircleBridge` then supplies the global
Riemann-temperature/fugacity chart.
-/
def localFugacity
    (h : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  Real.exp (-2 * h i)

/-- Local fugacity is positive. -/
theorem localFugacity_pos
    (h : Fin n → ℝ)
    (i : Fin n) :
    0 < localFugacity h i := by
  unfold localFugacity
  exact Real.exp_pos _

/--
Lee--Yang stability socket for a concrete finite prime chain.

The finite Ising Hamiltonian and ferromagnetic matrix are defined above.  A
real Lee--Yang theorem still requires a concrete partition polynomial and the
usual positivity/stability hypotheses. Those are supplied here as certificates,
not inferred from the existence of nonnegative `Jᵢⱼ` alone.
-/
structure LeeYangStabilityWitness where
  /-- The finite chain whose partition polynomial is being certified. -/
  chain : PrimeFerromagneticChain n
  partitionPolynomial : Polynomial ℂ
  fieldToFugacity : (Fin n → ℝ) → ℂ
  finitePartitionLaw : Prop
  finitePartitionCertificate :
    finitePartitionLaw
  leeYangStabilityLaw :
    ∀ z : ℂ, partitionPolynomial.IsRoot z → OnLeeYangCircle z
  noRiemannHypothesisClaimGuard : Type*

namespace LeeYangStabilityWitness

variable (W : LeeYangStabilityWitness (n := n))

/-- Re-export of the supplied finite partition law. -/
theorem finitePartition_valid :
    W.finitePartitionLaw :=
  W.finitePartitionCertificate

/-- Re-export of the supplied Lee--Yang circle law. -/
theorem leeYang_valid
    (z : ℂ)
    (hz : W.partitionPolynomial.IsRoot z) :
    OnLeeYangCircle z :=
  W.leeYangStabilityLaw z hz

end LeeYangStabilityWitness

end PrimeFerromagneticChain

/-! ## Owner target -/

/--
Owner target for the exact finite prime-chain interaction matrix:
the entries are nonnegative and symmetric.
-/
def PrimeLeeYangFerromagneticChainOwnerTarget : Prop :=
  ∀ {n : ℕ} (C : PrimeFerromagneticChain n) (i j : Fin n),
    0 ≤ C.coupling i j ∧ C.coupling i j = C.coupling j i

/-- The owner target follows from the explicit matrix elements. -/
theorem primeLeeYangFerromagneticChainOwnerTarget :
    PrimeLeeYangFerromagneticChainOwnerTarget := by
  intro n C i j
  exact ⟨C.coupling_nonneg i j, C.coupling_symm i j⟩

end InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
