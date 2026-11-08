/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.PrimeHeisenbergOscillators

/-!
# Topological Readout for Prime Heisenberg Oscillators

This module equips `V →ₗ[𝕜] V` with the discrete topology and packages
`primeAnnihilation`, `primeCreation`, `chargedFockPrimeAnnihilation`, and
`chargedFockPrimeCreation` as continuous, locally constant maps on the discrete
natural-number mode index `ℕ`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.PrimeHeisenbergOscillators`:
    `primeAnnihilation`, `primeCreation`, `chargedFockPrimeAnnihilation`,
    `chargedFockPrimeCreation`.
- BUCKET 2 (Deconfabulation):
  * All evaluation, continuity, and local constancy theorems are proved via explicit
    definitional unfolding and discrete-topology lemmas.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `topologicalPrimeAnnihilation`, `topologicalPrimeCreation`,
    `topologicalChargedFockPrimeAnnihilation`, `topologicalChargedFockPrimeCreation`.
  * `topologicalPrimeAnnihilation_eq`, `topologicalPrimeCreation_eq`,
    `topologicalChargedFockPrimeAnnihilation_eq`,
    `topologicalChargedFockPrimeCreation_eq`.
  * `continuous_topologicalPrimeAnnihilation`,
    `isLocallyConstant_topologicalPrimeAnnihilation`,
    `continuous_topologicalPrimeCreation`,
    `isLocallyConstant_topologicalPrimeCreation`,
    `continuous_topologicalChargedFockPrimeAnnihilation`,
    `continuous_topologicalChargedFockPrimeCreation`.
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
    DiscreteTopology (V →ₗ[𝕜] V) := DiscreteTopology.mk (Eq.refl _)

/-- The prime annihilation operator viewed as a discrete topological readout. -/
def topologicalPrimeAnnihilation
    (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) :
    V →ₗ[𝕜] V :=
  primeAnnihilation H p

/-- Explicit identification of `topologicalPrimeAnnihilation H p` with `primeAnnihilation H p`. -/
@[simp] theorem topologicalPrimeAnnihilation_eq
    (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) :
    topologicalPrimeAnnihilation (𝕜 := 𝕜) (V := V) H p =
      primeAnnihilation H p := by
  unfold topologicalPrimeAnnihilation
  exact Eq.refl _

/-- Continuity of `topologicalPrimeAnnihilation H` on the discrete mode index `ℕ`. -/
theorem continuous_topologicalPrimeAnnihilation
    (H : CurrentHeisenbergRep 𝕜 V) :
    Continuous (fun p : ℕ =>
      topologicalPrimeAnnihilation (𝕜 := 𝕜) (V := V) H p) := by
  unfold topologicalPrimeAnnihilation
  exact continuous_of_discreteTopology

/-- Local constancy of `topologicalPrimeAnnihilation H` on the discrete mode index `ℕ`. -/
theorem isLocallyConstant_topologicalPrimeAnnihilation
    (H : CurrentHeisenbergRep 𝕜 V) :
    IsLocallyConstant (fun p : ℕ =>
      topologicalPrimeAnnihilation (𝕜 := 𝕜) (V := V) H p) := by
  unfold topologicalPrimeAnnihilation
  exact IsLocallyConstant.of_discrete

/-- The prime creation operator viewed as a discrete topological readout. -/
def topologicalPrimeCreation
    (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) :
    V →ₗ[𝕜] V :=
  primeCreation H p

/-- Explicit identification of `topologicalPrimeCreation H p` with `primeCreation H p`. -/
@[simp] theorem topologicalPrimeCreation_eq
    (H : CurrentHeisenbergRep 𝕜 V) (p : ℕ) :
    topologicalPrimeCreation (𝕜 := 𝕜) (V := V) H p =
      primeCreation H p := by
  unfold topologicalPrimeCreation
  exact Eq.refl _

/-- Continuity of `topologicalPrimeCreation H` on the discrete mode index `ℕ`. -/
theorem continuous_topologicalPrimeCreation
    (H : CurrentHeisenbergRep 𝕜 V) :
    Continuous (fun p : ℕ =>
      topologicalPrimeCreation (𝕜 := 𝕜) (V := V) H p) := by
  unfold topologicalPrimeCreation
  exact continuous_of_discreteTopology

/-- Local constancy of `topologicalPrimeCreation H` on the discrete mode index `ℕ`. -/
theorem isLocallyConstant_topologicalPrimeCreation
    (H : CurrentHeisenbergRep 𝕜 V) :
    IsLocallyConstant (fun p : ℕ =>
      topologicalPrimeCreation (𝕜 := 𝕜) (V := V) H p) := by
  unfold topologicalPrimeCreation
  exact IsLocallyConstant.of_discrete

/-- The prime annihilation operator on the charged Fock space, topologically read. -/
def topologicalChargedFockPrimeAnnihilation
    (α : 𝕜) (p : ℕ) :
    PrimeChargedFockSpace (𝕜 := 𝕜) α →ₗ[𝕜]
      PrimeChargedFockSpace (𝕜 := 𝕜) α :=
  chargedFockPrimeAnnihilation (𝕜 := 𝕜) α p

/-- Explicit identification of `topologicalChargedFockPrimeAnnihilation α p`. -/
@[simp] theorem topologicalChargedFockPrimeAnnihilation_eq
    (α : 𝕜) (p : ℕ) :
    topologicalChargedFockPrimeAnnihilation (𝕜 := 𝕜) α p =
      chargedFockPrimeAnnihilation (𝕜 := 𝕜) α p := by
  unfold topologicalChargedFockPrimeAnnihilation
  exact Eq.refl _

/-- Continuity of `topologicalChargedFockPrimeAnnihilation α` on `ℕ`. -/
theorem continuous_topologicalChargedFockPrimeAnnihilation
    (α : 𝕜) :
    Continuous (fun p : ℕ =>
      topologicalChargedFockPrimeAnnihilation (𝕜 := 𝕜) α p) := by
  unfold topologicalChargedFockPrimeAnnihilation
  exact continuous_of_discreteTopology

/-- The prime creation operator on the charged Fock space, topologically read. -/
def topologicalChargedFockPrimeCreation
    (α : 𝕜) (p : ℕ) :
    PrimeChargedFockSpace (𝕜 := 𝕜) α →ₗ[𝕜]
      PrimeChargedFockSpace (𝕜 := 𝕜) α :=
  chargedFockPrimeCreation (𝕜 := 𝕜) α p

/-- Explicit identification of `topologicalChargedFockPrimeCreation α p`. -/
@[simp] theorem topologicalChargedFockPrimeCreation_eq
    (α : 𝕜) (p : ℕ) :
    topologicalChargedFockPrimeCreation (𝕜 := 𝕜) α p =
      chargedFockPrimeCreation (𝕜 := 𝕜) α p := by
  unfold topologicalChargedFockPrimeCreation
  exact Eq.refl _

/-- Continuity of `topologicalChargedFockPrimeCreation α` on `ℕ`. -/
theorem continuous_topologicalChargedFockPrimeCreation
    (α : 𝕜) :
    Continuous (fun p : ℕ =>
      topologicalChargedFockPrimeCreation (𝕜 := 𝕜) α p) := by
  unfold topologicalChargedFockPrimeCreation
  exact continuous_of_discreteTopology

end
end InfoGeometry.Topology.PrimeHeisenbergOscillatorsTopological
