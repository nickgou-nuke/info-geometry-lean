/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Prime Heisenberg Oscillators

This module defines the prime annihilation mode `primeAnnihilation H p = H.J (p : Int)`
and creation mode `primeCreation H p = H.J (-(p : Int))` associated with any
`CurrentHeisenbergRep 𝕜 V`, together with their charged-Fock specializations
`chargedFockPrimeAnnihilation` and `chargedFockPrimeCreation`, and proves off-diagonal
commutator vanishing `[J_p, J_{-q}] = 0` for `p ≠ q` and diagonal central-extension
resonance `[J_p, J_{-p}] = p • 1`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.CurrentSugawaraBridge`: `CurrentHeisenbergRep`,
    `chargedFockSpaceCurrentHeisenbergRep`.
- BUCKET 2 (Deconfabulation):
  * All commutator identities are derived directly from `H.comm` and integer mode
    arithmetic.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `primeAnnihilation`, `primeCreation`, `PrimeChargedFockSpace`,
    `chargedFockPrimeAnnihilation`, `chargedFockPrimeCreation`.
  * `prime_annihilation_creation_commutator_ne`: `[J_p, J_{-q}] = 0` for `p ≠ q`.
  * `prime_annihilation_creation_commutator_diag`: `[J_p, J_{-p}] = (p : 𝕜) • 1`.
  * `chargedFock_prime_annihilation_creation_commutator_ne`: charged-Fock specialization.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeHeisenbergOscillators

open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

set_option synthInstance.maxHeartbeats 200000

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-! ## 1. Prime oscillator modes from a Heisenberg current -/

/-- Prime annihilation/current mode `J_p = H.J (p : Int)`. -/
def primeAnnihilation (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) : V →ₗ[𝕜] V :=
  H.J (p : Int)

/-- Creation mode `a†_p = H.J (-(p : Int))`. -/
def primeCreation (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) : V →ₗ[𝕜] V :=
  H.J (-(p : Int))

/-- Off-diagonal prime oscillator commutator: `[J_p, J_{-q}] = 0` when `p ≠ q`. -/
theorem prime_annihilation_creation_commutator_ne
    (H : CurrentHeisenbergRep 𝕜 V)
    {p q : ℕ} (hpq : p ≠ q) :
    (primeAnnihilation H p).commutator (primeCreation H q) = 0 := by
  rw [primeAnnihilation, primeCreation]
  rw [H.comm (p : Int) (-(q : Int))]
  have hsum : ¬ (p : Int) + -(q : Int) = 0 := by
    intro h
    apply hpq
    omega
  simp only [hsum, ↓reduceIte]

/-- Diagonal prime oscillator commutator: `[J_p, J_{-p}] = (p : 𝕜) • 1`. -/
theorem prime_annihilation_creation_commutator_diag
    (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) :
    (primeAnnihilation H p).commutator (primeCreation H p) =
      ((p : Int) : 𝕜) • (1 : V →ₗ[𝕜] V) := by
  rw [primeAnnihilation, primeCreation]
  rw [H.comm (p : Int) (-(p : Int))]
  have hsum : (p : Int) + -(p : Int) = 0 := add_neg_cancel (p : Int)
  simp only [hsum, ↓reduceIte]

/-! ## 2. Charged Fock specialization -/

/-- The external charged Fock space used as the Heisenberg boundary module. -/
abbrev PrimeChargedFockSpace (α : 𝕜) :=
  VirasoroProject.ChargedFockSpace 𝕜 α

/-- Prime annihilation mode on the external charged Fock space. -/
def chargedFockPrimeAnnihilation (α : 𝕜) (p : ℕ) :
    PrimeChargedFockSpace (𝕜 := 𝕜) α →ₗ[𝕜]
      PrimeChargedFockSpace (𝕜 := 𝕜) α :=
  primeAnnihilation (chargedFockSpaceCurrentHeisenbergRep 𝕜 α) p

/-- Prime creation mode on the external charged Fock space. -/
def chargedFockPrimeCreation (α : 𝕜) (p : ℕ) :
    PrimeChargedFockSpace (𝕜 := 𝕜) α →ₗ[𝕜]
      PrimeChargedFockSpace (𝕜 := 𝕜) α :=
  primeCreation (chargedFockSpaceCurrentHeisenbergRep 𝕜 α) p

/-- Off-diagonal charged-Fock prime oscillator independence. -/
theorem chargedFock_prime_annihilation_creation_commutator_ne
    (α : 𝕜) {p q : ℕ} (hpq : p ≠ q) :
    (chargedFockPrimeAnnihilation (𝕜 := 𝕜) α p).commutator
        (chargedFockPrimeCreation (𝕜 := 𝕜) α q) = 0 := by
  unfold chargedFockPrimeAnnihilation chargedFockPrimeCreation
  exact prime_annihilation_creation_commutator_ne
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α) hpq

end InfoGeometry.Canonical.PrimeHeisenbergOscillators
