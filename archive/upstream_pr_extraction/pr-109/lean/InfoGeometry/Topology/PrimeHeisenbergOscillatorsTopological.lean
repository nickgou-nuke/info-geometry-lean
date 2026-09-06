import Mathlib
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.PrimeHeisenbergOscillators

/-!
# Topological readout for prime Heisenberg oscillators

This file packages the prime annihilation and creation modes as discrete
topological maps.  It does not add any new algebraic content to the
Heisenberg current theory; it only records continuity and local constancy of
the already proved operator readouts.
-/

namespace InfoGeometry.Topology.PrimeHeisenbergOscillatorsTopological

open InfoGeometry.Canonical
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.PrimeHeisenbergOscillators

noncomputable section

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

instance endomorphismTopologicalSpace :
    TopologicalSpace (V →ₗ[𝕜] V) := ⊥

instance endomorphismDiscreteTopology :
    DiscreteTopology (V →ₗ[𝕜] V) := ⟨rfl⟩

/-- The prime annihilation operator, viewed as a discrete topological readout. -/
def topologicalPrimeAnnihilation
    (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) :
    V →ₗ[𝕜] V :=
  primeAnnihilation H p

@[simp] theorem topologicalPrimeAnnihilation_eq
    (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) :
    topologicalPrimeAnnihilation (𝕜 := 𝕜) (V := V) H p =
      primeAnnihilation H p := by
  rfl

theorem continuous_topologicalPrimeAnnihilation
    (H : CurrentHeisenbergRep 𝕜 V) :
    Continuous (fun p : ℕ =>
      topologicalPrimeAnnihilation (𝕜 := 𝕜) (V := V) H p) := by
  simpa [topologicalPrimeAnnihilation] using
    (continuous_of_discreteTopology :
      Continuous (fun p : ℕ =>
        topologicalPrimeAnnihilation (𝕜 := 𝕜) (V := V) H p))

theorem isLocallyConstant_topologicalPrimeAnnihilation
    (H : CurrentHeisenbergRep 𝕜 V) :
    IsLocallyConstant (fun p : ℕ =>
      topologicalPrimeAnnihilation (𝕜 := 𝕜) (V := V) H p) := by
  simpa [topologicalPrimeAnnihilation] using
    (IsLocallyConstant.of_discrete
      (f := fun p : ℕ =>
        topologicalPrimeAnnihilation (𝕜 := 𝕜) (V := V) H p))

/-- The prime creation operator, viewed as a discrete topological readout. -/
def topologicalPrimeCreation
    (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) :
    V →ₗ[𝕜] V :=
  primeCreation H p

@[simp] theorem topologicalPrimeCreation_eq
    (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) :
    topologicalPrimeCreation (𝕜 := 𝕜) (V := V) H p =
      primeCreation H p := by
  rfl

theorem continuous_topologicalPrimeCreation
    (H : CurrentHeisenbergRep 𝕜 V) :
    Continuous (fun p : ℕ =>
      topologicalPrimeCreation (𝕜 := 𝕜) (V := V) H p) := by
  simpa [topologicalPrimeCreation] using
    (continuous_of_discreteTopology :
      Continuous (fun p : ℕ =>
        topologicalPrimeCreation (𝕜 := 𝕜) (V := V) H p))

theorem isLocallyConstant_topologicalPrimeCreation
    (H : CurrentHeisenbergRep 𝕜 V) :
    IsLocallyConstant (fun p : ℕ =>
      topologicalPrimeCreation (𝕜 := 𝕜) (V := V) H p) := by
  simpa [topologicalPrimeCreation] using
    (IsLocallyConstant.of_discrete
      (f := fun p : ℕ =>
        topologicalPrimeCreation (𝕜 := 𝕜) (V := V) H p))

/-- The prime annihilation operator on the charged Fock space, topologically read. -/
def topologicalChargedFockPrimeAnnihilation
    (α : 𝕜) (p : ℕ) :
    PrimeChargedFockSpace (𝕜 := 𝕜) α →ₗ[𝕜]
      PrimeChargedFockSpace (𝕜 := 𝕜) α :=
  chargedFockPrimeAnnihilation (𝕜 := 𝕜) α p

@[simp] theorem topologicalChargedFockPrimeAnnihilation_eq
    (α : 𝕜) (p : ℕ) :
    topologicalChargedFockPrimeAnnihilation (𝕜 := 𝕜) α p =
      chargedFockPrimeAnnihilation (𝕜 := 𝕜) α p := by
  rfl

theorem continuous_topologicalChargedFockPrimeAnnihilation
    (α : 𝕜) :
    Continuous (fun p : ℕ =>
      topologicalChargedFockPrimeAnnihilation (𝕜 := 𝕜) α p) := by
  simpa [topologicalChargedFockPrimeAnnihilation] using
    (continuous_of_discreteTopology :
      Continuous (fun p : ℕ =>
        topologicalChargedFockPrimeAnnihilation (𝕜 := 𝕜) α p))

/-- The prime creation operator on the charged Fock space, topologically read. -/
def topologicalChargedFockPrimeCreation
    (α : 𝕜) (p : ℕ) :
    PrimeChargedFockSpace (𝕜 := 𝕜) α →ₗ[𝕜]
      PrimeChargedFockSpace (𝕜 := 𝕜) α :=
  chargedFockPrimeCreation (𝕜 := 𝕜) α p

@[simp] theorem topologicalChargedFockPrimeCreation_eq
    (α : 𝕜) (p : ℕ) :
    topologicalChargedFockPrimeCreation (𝕜 := 𝕜) α p =
      chargedFockPrimeCreation (𝕜 := 𝕜) α p := by
  rfl

theorem continuous_topologicalChargedFockPrimeCreation
    (α : 𝕜) :
    Continuous (fun p : ℕ =>
      topologicalChargedFockPrimeCreation (𝕜 := 𝕜) α p) := by
  simpa [topologicalChargedFockPrimeCreation] using
    (continuous_of_discreteTopology :
      Continuous (fun p : ℕ =>
        topologicalChargedFockPrimeCreation (𝕜 := 𝕜) α p))

end
end InfoGeometry.Topology.PrimeHeisenbergOscillatorsTopological
