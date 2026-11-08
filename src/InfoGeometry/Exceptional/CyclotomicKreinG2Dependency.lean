/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicBridge

namespace InfoGeometry.Exceptional.CyclotomicKreinG2.ProofDependency

inductive Archetype
  | cyclotomicPolynomial
  | unitArithmetic
  | galoisGroup
  | integerClock
  | exactPeriod
  | rootDecomposition
  | neutralPairing
  | paraAntiIsometry
  | traceDiscriminant
  | ellipticCounterexample
  | primitiveRoot
  | rotationRepresentation
  | rotationPeriod
  | ellipticRotation
  | rotationQuartic
  | rotationHalfPeriod
  deriving DecidableEq

instance : Fintype Archetype := derive_fintype% Archetype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | cyclotomicPolynomial => {cyclotomicPolynomial}
  | unitArithmetic => {unitArithmetic}
  | galoisGroup => {unitArithmetic, galoisGroup}
  | integerClock => {cyclotomicPolynomial, integerClock}
  | exactPeriod => {cyclotomicPolynomial, integerClock, exactPeriod}
  | rootDecomposition => {rootDecomposition}
  | neutralPairing => {neutralPairing}
  | paraAntiIsometry => {neutralPairing, paraAntiIsometry}
  | traceDiscriminant => {traceDiscriminant}
  | ellipticCounterexample => {traceDiscriminant, ellipticCounterexample}
  | primitiveRoot => {primitiveRoot}
  | rotationRepresentation => {primitiveRoot, rotationRepresentation}
  | rotationPeriod => {primitiveRoot, rotationRepresentation, rotationPeriod}
  | ellipticRotation =>
      {primitiveRoot, rotationRepresentation, traceDiscriminant, ellipticRotation}
  | rotationQuartic =>
      {cyclotomicPolynomial, primitiveRoot, rotationRepresentation, rotationQuartic}
  | rotationHalfPeriod =>
      {cyclotomicPolynomial, primitiveRoot, rotationRepresentation,
        rotationQuartic, rotationHalfPeriod}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem dependency_branches :
    cyclotomicPolynomial < integerClock ∧ integerClock < exactPeriod ∧
    unitArithmetic < galoisGroup ∧ neutralPairing < paraAntiIsometry ∧
    traceDiscriminant < ellipticCounterexample := by
  simp only [lt_iff_le_not_ge]
  decide

theorem arithmetic_and_roots_incomparable :
    ¬ galoisGroup ≤ rootDecomposition ∧ ¬ rootDecomposition ≤ galoisGroup ∧
    ¬ exactPeriod ≤ rootDecomposition ∧ ¬ rootDecomposition ≤ exactPeriod := by
  decide

theorem neutral_and_spectral_branches_incomparable :
    ¬ paraAntiIsometry ≤ traceDiscriminant ∧
    ¬ traceDiscriminant ≤ paraAntiIsometry := by
  decide

theorem no_cycle {earlier later : Archetype} (forward : earlier < later) :
    ¬ later < earlier := lt_asymm forward

theorem rotation_dependencies :
    primitiveRoot < rotationRepresentation ∧ rotationRepresentation < rotationPeriod ∧
    rotationRepresentation < ellipticRotation ∧ traceDiscriminant < ellipticRotation ∧
    cyclotomicPolynomial < rotationQuartic ∧ rotationRepresentation < rotationQuartic ∧
    rotationQuartic < rotationHalfPeriod := by
  simp only [lt_iff_le_not_ge]
  decide

theorem periodicity_and_ellipticity_incomparable :
    ¬ rotationPeriod ≤ ellipticRotation ∧ ¬ ellipticRotation ≤ rotationPeriod := by
  decide

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetypes 1–5 (`cyclotomicPolynomial`, `unitArithmetic`, `galoisGroup`, `integerClock`, `exactPeriod`):**
Universal non-commutative 6th-cyclotomic factorization `(U + 1) * (U^2 - U + 1) = U^3 + 1`,
`(U - 1) * (U^2 + U + 1) = U^3 - 1`, and 6-step clock identity
`(U^3 - 1) * (U^3 + 1) = U^6 - 1` over any `[Ring B]`. -/
theorem archetype_cyclotomic_clock_and_period_identities (U : B) :
    (U + 1) * (U * U - U + 1) = U * U * U + 1 ∧
    (U - 1) * (U * U + U + 1) = U * U * U - 1 ∧
    (U * U * U - 1) * (U * U * U + 1) = U * U * U * U * U * U - 1 ∧
    (U * U - U + 1 = 0 → U * U * U = -1 ∧ U * U * U * U * U * U = 1) := by
  have h1 : (U + 1) * (U * U - U + 1) = U * U * U + 1 := by noncomm_ring
  have h2 : (U - 1) * (U * U + U + 1) = U * U * U - 1 := by noncomm_ring
  have h3 : (U * U * U - 1) * (U * U * U + 1) = U * U * U * U * U * U - 1 := by noncomm_ring
  refine ⟨h1, h2, h3, fun h0 => ?_⟩
  have hU3 : U * U * U = -1 := by
    calc
      U * U * U = (U + 1) * (U * U - U + 1) - 1 := by noncomm_ring
      _ = (U + 1) * 0 - 1 := by rw [h0]
      _ = -1 := by noncomm_ring
  refine ⟨hU3, ?_⟩
  calc
    U * U * U * U * U * U = (U * U * U) * (U * U * U) := by noncomm_ring
    _ = (-1) * (-1) := by rw [hU3]
    _ = 1 := by noncomm_ring

/-- **Archetypes 6–10 (`rootDecomposition`, `neutralPairing`, `paraAntiIsometry`, `traceDiscriminant`, `ellipticCounterexample`):**
Split-signature Krein decomposition over an idempotent `P * P = P`:
`Φ² = V` (para-complex branch), `J² = -V` (elliptic branch), `Φ² + J² = 0` (neutral pairing),
`S_P * Φ * S_P = -Φ` (para-anti-isometry), and `peirce11 P V - peirce00 P V = Σ` (discriminant). -/
theorem archetype_krein_neutral_pairing_and_para_vs_elliptic
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
    invS P * genPhi P A C * invS P = -genPhi P A C ∧
    invS P * genJ P A C * invS P = -genJ P A C ∧
    peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · simp only [peirce11, peirce00]; peirce_nf hP

/-- **Archetypes 11–16 (`primitiveRoot`, `rotationRepresentation`, `rotationPeriod`, `ellipticRotation`, `rotationQuartic`, `rotationHalfPeriod`):**
Operator rotation and quartic identities on the Tetraktys `(Φ, J, V, Σ)`:
`[Σ, Φ] = 2 • (V * J)`, `[Σ, J] = 2 • (V * Φ)`, `Φ⁴ = V²`, `J⁴ = V²`, and `Σ² = V²`. -/
theorem archetype_rotation_representation_and_quartic_period
    {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    (genPhi P A C * genPhi P A C) * (genPhi P A C * genPhi P A C) = genV P A C * genV P A C ∧
    (genJ P A C * genJ P A C) * (genJ P A C * genJ P A C) = genV P A C * genV P A C ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Master Synthesis (`cyclotomic_krein_g2_dependency_master_synthesis`):**
Unites the 16-stage partial-order branch theorems with all non-commutative `[Ring B]`
cyclotomic and Krein operator identities. -/
theorem cyclotomic_krein_g2_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C U : B) :
    (cyclotomicPolynomial < integerClock ∧ integerClock < exactPeriod ∧
      neutralPairing < paraAntiIsometry ∧ rotationQuartic < rotationHalfPeriod) ∧
    ((U + 1) * (U * U - U + 1) = U * U * U + 1) ∧
    (genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
      peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C) ∧
    (comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
      (genJ P A C * genJ P A C) * (genJ P A C * genJ P A C) = genV P A C * genV P A C) := by
  have h1 := archetype_cyclotomic_clock_and_period_identities U
  have h2 := archetype_krein_neutral_pairing_and_para_vs_elliptic hP A C
  have h3 := archetype_rotation_representation_and_quartic_period hP A C
  exact ⟨⟨dependency_branches.1, dependency_branches.2.1,
      dependency_branches.2.2.2.1, rotation_dependencies.2.2.2.2.2.2⟩,
    h1.1, ⟨h2.2.2.1, h2.2.2.2.2.2⟩, ⟨h3.1, h3.2.2.2.1⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Exceptional.CyclotomicKreinG2.ProofDependency
