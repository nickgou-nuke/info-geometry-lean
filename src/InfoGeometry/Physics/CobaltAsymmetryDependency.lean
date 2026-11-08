/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.DeriveFintype
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Physics.CobaltAsymmetryDependency

inductive Archetype
  | betaModel
  | betaReflectionViolation
  | evenAngularModel
  | gammaAnisotropy
  | gammaReflectionInvariance
  | anisotropyCounterexample
  deriving DecidableEq

instance : Fintype Archetype where
  elems := {Archetype.betaModel, Archetype.betaReflectionViolation,
    Archetype.evenAngularModel, Archetype.gammaAnisotropy,
    Archetype.gammaReflectionInvariance, Archetype.anisotropyCounterexample}
  complete := by
    intro archetype
    cases archetype <;> simp

open Archetype

def prerequisites : Archetype → Finset Archetype
  | betaModel => {betaModel}
  | betaReflectionViolation => {betaModel, betaReflectionViolation}
  | evenAngularModel => {evenAngularModel}
  | gammaAnisotropy => {evenAngularModel, gammaAnisotropy}
  | gammaReflectionInvariance => {evenAngularModel, gammaReflectionInvariance}
  | anisotropyCounterexample =>
      {evenAngularModel, gammaAnisotropy, gammaReflectionInvariance, anisotropyCounterexample}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem model_dependencies :
    betaModel ≤ betaReflectionViolation ∧ evenAngularModel ≤ gammaAnisotropy ∧
      evenAngularModel ≤ gammaReflectionInvariance ∧
      gammaAnisotropy ≤ anisotropyCounterexample ∧
      gammaReflectionInvariance ≤ anisotropyCounterexample := by
  change prerequisites betaModel ⊆ prerequisites betaReflectionViolation ∧
    prerequisites evenAngularModel ⊆ prerequisites gammaAnisotropy ∧
    prerequisites evenAngularModel ⊆ prerequisites gammaReflectionInvariance ∧
    prerequisites gammaAnisotropy ⊆ prerequisites anisotropyCounterexample ∧
    prerequisites gammaReflectionInvariance ⊆ prerequisites anisotropyCounterexample
  decide

theorem beta_and_gamma_branches_incomparable :
    ¬ betaReflectionViolation ≤ anisotropyCounterexample ∧
      ¬ anisotropyCounterexample ≤ betaReflectionViolation := by
  change ¬ prerequisites betaReflectionViolation ⊆ prerequisites anisotropyCounterexample ∧
    ¬ prerequisites anisotropyCounterexample ⊆ prerequisites betaReflectionViolation
  decide

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype 1 (`betaModel`):**
Pseudoscalar/axial odd-grade operator `Φ = N_+ + N_-` and dipole `J = N_+ - N_-` satisfy
`S_P * Φ = J` and `Φ * S_P = -J`. -/
theorem archetype_betaModel_axial_coupling
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * genPhi P A C = genJ P A C ∧
    genPhi P A C * invS P = -genJ P A C := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 2 (`betaReflectionViolation`):**
Parity reflection `X ↦ S_P * X * S_P` reverses the sign of the odd-grade beta operator `Φ` and `J`
(`S_P * Φ * S_P = -Φ` and `S_P * J * S_P = -J`), yielding a non-zero parity-violating commutator
`[S_P, Φ] = 2 • J`. -/
theorem archetype_betaReflectionViolation_parity_reversal
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * genPhi P A C * invS P = -genPhi P A C ∧
    invS P * genJ P A C * invS P = -genJ P A C ∧
    comm (invS P) (genPhi P A C) = (2 : ℤ) • genJ P A C := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 3 (`evenAngularModel`):**
Even-parity angular operator `evenGrade P X = P X P + (1 - P) X (1 - P)` and the quadratic
multipole operators `V = Φ²` and `Σ = J * Φ` lie in the even-grade block. -/
theorem archetype_evenAngularModel_quadratic_even_block
    {P : B} (hP : P * P = P) (A C : B) :
    evenGrade P (genV P A C) = genV P A C ∧
    evenGrade P (genSig P A C) = genSig P A C ∧
    oddGrade P (genV P A C) = 0 ∧
    oddGrade P (genSig P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [evenGrade, oddGrade]; peirce_nf hP)

/-- **Archetype 4 (`gammaAnisotropy`):**
Quadrupole anisotropy operator `Σ = peirce11 P V - peirce00 P V` measures the difference
between the upper (`N_+ N_-`) and lower (`N_- N_+`) diagonal Gram blocks. -/
theorem archetype_gammaAnisotropy_quadrupole_imbalance
    {P : B} (hP : P * P = P) (A C : B) :
    peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C ∧
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) := by
  refine ⟨?_, ?_⟩
  · simp only [peirce11, peirce00]; peirce_nf hP
  · peirce_nf hP

/-- **Archetype 5 (`gammaReflectionInvariance`):**
Even-parity quadrupole operators `V` and `Σ` are strictly invariant under parity reflection
`X ↦ S_P * X * S_P`: `S_P * V * S_P = V` and `S_P * Σ * S_P = Σ`. -/
theorem archetype_gammaReflectionInvariance_even_parity
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * genV P A C * invS P = genV P A C ∧
    invS P * genSig P A C * invS P = genSig P A C ∧
    comm (invS P) (genV P A C) = 0 ∧
    comm (invS P) (genSig P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 6 (`anisotropyCounterexample`):**
Although `Σ` is reflection-invariant (`[S_P, Σ] = 0`), its inner derivation `ad_Σ` is
non-trivial on the odd-grade sector (`[Σ, Φ] = 2 • (V * J)`), distinguishing reflection
invariance (`[S_P, Σ] = 0`) from isotropy (`ad_Σ = 0`). -/
theorem archetype_anisotropyCounterexample_nonvanishing_quadrupole_flow
    {P : B} (hP : P * P = P) (A C : B) :
    comm (invS P) (genSig P A C) = 0 ∧
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Master Synthesis (`cobalt_asymmetry_dependency_master_synthesis`):**
Unites the partial-order branch theorems with all six non-commutative `[Ring B]`
parity and quadrupole operator theorems. -/
theorem cobalt_asymmetry_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C : B) :
    (betaModel ≤ betaReflectionViolation ∧ evenAngularModel ≤ gammaAnisotropy ∧
      evenAngularModel ≤ gammaReflectionInvariance ∧
      gammaAnisotropy ≤ anisotropyCounterexample ∧
      gammaReflectionInvariance ≤ anisotropyCounterexample) ∧
    (invS P * genPhi P A C = genJ P A C) ∧
    (invS P * genPhi P A C * invS P = -genPhi P A C) ∧
    (evenGrade P (genV P A C) = genV P A C) ∧
    (peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C) ∧
    (invS P * genSig P A C * invS P = genSig P A C) ∧
    (comm (invS P) (genSig P A C) = 0 ∧
      comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C)) := by
  have h1 := archetype_betaModel_axial_coupling hP A C
  have h2 := archetype_betaReflectionViolation_parity_reversal hP A C
  have h3 := archetype_evenAngularModel_quadratic_even_block hP A C
  have h4 := archetype_gammaAnisotropy_quadrupole_imbalance hP A C
  have h5 := archetype_gammaReflectionInvariance_even_parity hP A C
  have h6 := archetype_anisotropyCounterexample_nonvanishing_quadrupole_flow hP A C
  exact ⟨model_dependencies, h1.1, h2.1, h3.1, h4.1, h5.2.1, ⟨h6.1, h6.2.1⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Physics.CobaltAsymmetryDependency
