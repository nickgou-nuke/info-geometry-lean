/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Algebra.MadelungProofDependency

inductive Archetype
  | logDensity
  | osmoticScore
  | curvatureIdentity
  | commutingDerivations
  | hamiltonJacobi
  | eulerEquation
  deriving DecidableEq

instance : Fintype Archetype :=
  Fintype.ofList [.logDensity, .osmoticScore, .curvatureIdentity,
    .commutingDerivations, .hamiltonJacobi, .eulerEquation] (by
      intro x
      cases x <;> simp)

open Archetype

def prerequisites : Archetype → Finset Archetype
  | logDensity => {logDensity}
  | osmoticScore => {logDensity, osmoticScore}
  | curvatureIdentity => {logDensity, osmoticScore, curvatureIdentity}
  | commutingDerivations => {commutingDerivations}
  | hamiltonJacobi => {logDensity, osmoticScore, curvatureIdentity, hamiltonJacobi}
  | eulerEquation =>
      {logDensity, osmoticScore, curvatureIdentity, commutingDerivations,
        hamiltonJacobi, eulerEquation}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem curvature_branch :
    logDensity ≤ osmoticScore ∧ osmoticScore ≤ curvatureIdentity := by
  change prerequisites logDensity ⊆ prerequisites osmoticScore ∧
    prerequisites osmoticScore ⊆ prerequisites curvatureIdentity
  decide

theorem euler_prerequisites :
    curvatureIdentity ≤ hamiltonJacobi ∧ hamiltonJacobi ≤ eulerEquation ∧
      commutingDerivations ≤ eulerEquation := by
  change prerequisites curvatureIdentity ⊆ prerequisites hamiltonJacobi ∧
    prerequisites hamiltonJacobi ⊆ prerequisites eulerEquation ∧
    prerequisites commutingDerivations ⊆ prerequisites eulerEquation
  decide

theorem commutation_not_implied_by_curvature :
    ¬ commutingDerivations ≤ curvatureIdentity ∧
      ¬ curvatureIdentity ≤ commutingDerivations := by
  change ¬ prerequisites commutingDerivations ⊆ prerequisites curvatureIdentity ∧
    ¬ prerequisites curvatureIdentity ⊆ prerequisites commutingDerivations
  decide

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype 1 (`logDensity`):**
The modular surprisal / log-density generator `Σ = [N_+, N_-]` factors as `Σ = S_P * V = V * S_P`
and satisfies `Σ² = V²`. -/
theorem archetype_logDensity_modular_surprisal
    {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C = invS P * genV P A C ∧
    genSig P A C = genV P A C * invS P ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 2 (`osmoticScore`):**
The osmotic dipole operator `J = N_+ - N_-` and irrotational velocity operator `Φ = N_+ + N_-`
are linked by grading multiplication `J = S_P * Φ` and `Φ = S_P * J` with `J² = -V` and `Φ² = V`. -/
theorem archetype_osmoticScore_chiral_dipole
    {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C = invS P * genPhi P A C ∧
    genPhi P A C = invS P * genJ P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genPhi P A C * genPhi P A C = genV P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 3 (`curvatureIdentity`):**
Madelung–Bohm quantum curvature identity: the commutator of the light-cone derivations
`ad_{N_+}` and `ad_{N_-}` equals `ad_Σ`, while the commutator of `ad_Φ` and `ad_J` equals
`-2 • ad_Σ`. -/
theorem archetype_curvatureIdentity_vorticity_commutator
    {P : B} (hP : P * P = P) (A C X : B) :
    comm (conePlus P A) (comm (coneMinus P C) X) -
        comm (coneMinus P C) (comm (conePlus P A) X) =
      comm (genSig P A C) X ∧
    comm (genPhi P A C) (comm (genJ P A C) X) -
        comm (genJ P A C) (comm (genPhi P A C) X) =
      -((2 : ℤ) • comm (genSig P A C) X) := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 4 (`commutingDerivations`):**
The centralizer generators `V = {N_+, N_-}` and `Σ = [N_+, N_-]` commute (`[V, Σ] = 0`) and
generate commuting inner derivations (`[V, [Σ, X]] = [Σ, [V, X]]`). -/
theorem archetype_commutingDerivations_centralizer_pair
    {P : B} (hP : P * P = P) (A C X : B) :
    comm (genV P A C) (genSig P A C) = 0 ∧
    comm (genV P A C) (comm (genSig P A C) X) =
      comm (genSig P A C) (comm (genV P A C) X) := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 5 (`hamiltonJacobi`):**
Non-commutative Hamilton–Jacobi eikonal dispersion relation:
`Φ * Φ + J * J = 0`, `(Φ + J) * (Φ - J) = 2 • (V + Σ)`, and
`(Φ - J) * (Φ + J) = 2 • (V - Σ)`. -/
theorem archetype_hamiltonJacobi_operator_eikonal
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
    (genPhi P A C + genJ P A C) * (genPhi P A C - genJ P A C) =
      (2 : ℤ) • (genV P A C + genSig P A C) ∧
    (genPhi P A C - genJ P A C) * (genPhi P A C + genJ P A C) =
      (2 : ℤ) • (genV P A C - genSig P A C) := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 6 (`eulerEquation`):**
Non-commutative Euler convective Hessian splitting:
`2 • ([N_+, [N_-, X]] + [N_-, [N_+, X]]) = -(derivSqPhi P A C X + derivSqJ P A C X)` and
`derivSqPhi P A C X - derivSqJ P A C X = 4 • sandwichSame P A C X`. -/
theorem archetype_eulerEquation_convective_hessian
    {P : B} (hP : P * P = P) (A C X : B) :
    (2 : ℤ) • (comm (conePlus P A) (comm (coneMinus P C) X) +
        comm (coneMinus P C) (comm (conePlus P A) X)) =
      -(derivSqPhi P A C X + derivSqJ P A C X) ∧
    derivSqPhi P A C X - derivSqJ P A C X = (4 : ℤ) • sandwichSame P A C X := by
  refine ⟨?_, ?_⟩
  · simp only [derivSqPhi, derivSqJ]; peirce_nf hP
  · simp only [derivSqPhi, derivSqJ, sandwichSame]; peirce_nf hP

/-- **Master Synthesis (`madelung_proof_dependency_master_synthesis`):**
Unites the partial-order branch theorems with all six non-commutative `[Ring B]`
Madelung operator theorems. -/
theorem madelung_proof_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C X : B) :
    (logDensity ≤ osmoticScore ∧ osmoticScore ≤ curvatureIdentity ∧
      curvatureIdentity ≤ hamiltonJacobi ∧ hamiltonJacobi ≤ eulerEquation ∧
      commutingDerivations ≤ eulerEquation) ∧
    (genSig P A C = invS P * genV P A C) ∧
    (genJ P A C = invS P * genPhi P A C) ∧
    (comm (genPhi P A C) (comm (genJ P A C) X) -
        comm (genJ P A C) (comm (genPhi P A C) X) =
      -((2 : ℤ) • comm (genSig P A C) X)) ∧
    (comm (genV P A C) (comm (genSig P A C) X) =
      comm (genSig P A C) (comm (genV P A C) X)) ∧
    (genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0) ∧
    (derivSqPhi P A C X - derivSqJ P A C X = (4 : ℤ) • sandwichSame P A C X) := by
  have h1 := archetype_logDensity_modular_surprisal hP A C
  have h2 := archetype_osmoticScore_chiral_dipole hP A C
  have h3 := archetype_curvatureIdentity_vorticity_commutator hP A C X
  have h4 := archetype_commutingDerivations_centralizer_pair hP A C X
  have h5 := archetype_hamiltonJacobi_operator_eikonal hP A C
  have h6 := archetype_eulerEquation_convective_hessian hP A C X
  exact ⟨⟨curvature_branch.1, curvature_branch.2, euler_prerequisites⟩,
    h1.1, h2.1, h3.2, h4.2, h5.1, h6.2⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Algebra.MadelungProofDependency
