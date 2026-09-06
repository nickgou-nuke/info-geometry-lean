import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# Prime Heisenberg Oscillators

This module adds the algebraic oscillator readout for the Bost--Connes/CFT
boundary.

The construction is intentionally modest.  It does not define a completed
VOA, a topological tensor product over all primes, or a graded trace.  It
extracts the prime oscillator relations from the already-owned
`CurrentHeisenbergRep` surface:

* the current modes satisfy `[J_m,J_n] = m δ_{m+n,0} · 1`;
* the positive prime current is `J_p`;
* the creation operator is `a†_q = J_{-q}`;
* therefore distinct prime modes are independent in the
  annihilation/creation channel.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `prime_annihilation_creation_commutator_ne` proves off-diagonal
  independence.
* `chargedFock_prime_annihilation_creation_commutator_ne` specializes the
  result to the external charged Fock space.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

* The generic oscillator statements are conditional on an explicit
  `CurrentHeisenbergRep`.

#### BUCKET 3: OPEN CLOSURE DEBT

* Construct the graded symmetric/Fock algebra over the prime mode basis.
* Prove the graded trace/character identity that identifies the Fock trace
  with the Bost--Connes partition readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeHeisenbergOscillators

open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

set_option synthInstance.maxHeartbeats 200000

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-! ## 1. Prime oscillator modes from a Heisenberg current -/

/-- Prime annihilation/current mode `J_p`. -/
def primeAnnihilation (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) : V →ₗ[𝕜] V :=
  H.J (p : Int)

/-- Creation mode `a†_p = J_{-p}`. -/
def primeCreation (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) : V →ₗ[𝕜] V :=
  H.J (-(p : Int))

/--
Off-diagonal prime oscillator commutator:

`[J_p,J_{-q}] = 0` when `p ≠ q`.
-/
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
  simp [hsum]

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
  exact prime_annihilation_creation_commutator_ne
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α) hpq

end InfoGeometry.Canonical.PrimeHeisenbergOscillators
