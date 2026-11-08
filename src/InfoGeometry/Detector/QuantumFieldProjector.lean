/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace DetectorGeometry.QuantumFieldProjector

section FieldFluxConservation

def idealFieldFlux (ε : ℝ) : ℝ := ε

def observedSingles (K ε : ℝ) : ℝ := ε * (1 - K * ε)

def observedCoincidence (K ε : ℝ) : ℝ := K * ε ^ 2

theorem field_flux_conservation (K ε : ℝ) :
    observedSingles K ε + observedCoincidence K ε = idealFieldFlux ε := by
  simp [observedSingles, observedCoincidence, idealFieldFlux]
  ring

end FieldFluxConservation

section ProjectorInversion

def reconstructedFlux (single coincidence : ℝ) : ℝ := single + coincidence

noncomputable def sqrtCoincidenceCoordinate (K ε : ℝ) : ℝ :=
  Real.sqrt (observedCoincidence K ε)

theorem perfect_flux_reconstruction (K ε : ℝ) :
    reconstructedFlux (observedSingles K ε) (observedCoincidence K ε) =
      idealFieldFlux ε := by
  exact field_flux_conservation K ε

theorem sqrt_inverts_projection (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    sqrtCoincidenceCoordinate K ε = Real.sqrt K *
      reconstructedFlux (observedSingles K ε) (observedCoincidence K ε) := by
  rw [perfect_flux_reconstruction K ε]
  simp only [sqrtCoincidenceCoordinate, observedCoincidence, idealFieldFlux]
  rw [Real.sqrt_mul hK, Real.sqrt_sq hε]

end ProjectorInversion

section UnbrokenLinearRay

theorem invariant_scale_modulus (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    reconstructedFlux (observedSingles K ε) (observedCoincidence K ε) /
        sqrtCoincidenceCoordinate K ε = (Real.sqrt K)⁻¹ := by
  rw [perfect_flux_reconstruction K ε]
  simp only [idealFieldFlux, sqrtCoincidenceCoordinate, observedCoincidence]
  have hK₀ : 0 ≤ K := le_of_lt hK
  have hε₀ : 0 ≤ ε := le_of_lt hε
  have hεne : ε ≠ 0 := ne_of_gt hε
  rw [Real.sqrt_mul hK₀, Real.sqrt_sq hε₀]
  have hsqrt : Real.sqrt K ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hK)
  field_simp [hεne, hsqrt]

theorem vacuum_forces_zero_intercept (K : ℝ) (hK : 0 < K) {a b : ℝ}
    (h_ray : ∀ ε : ℝ, 0 ≤ ε →
      reconstructedFlux (observedSingles K ε) (observedCoincidence K ε) =
        a * sqrtCoincidenceCoordinate K ε + b) : b = 0 := by
  have h0 := h_ray 0 (le_refl 0)
  rw [perfect_flux_reconstruction K 0] at h0
  simp [idealFieldFlux, sqrtCoincidenceCoordinate, observedCoincidence] at h0
  exact h0.symm

end UnbrokenLinearRay

section CausalPoset

inductive Archetype
  | fluxConservation
  | depletion
  | projectorInversion
  | reconstruction
  | unbrokenRay
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .fluxConservation => 185
  | .depletion => 186
  | .projectorInversion => 187
  | .reconstruction => 188
  | .unbrokenRay => 189

def causallyPrecedes (a b : Archetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := by
  exact Nat.le_trans

theorem causal_antisymm {a b : Archetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢

theorem canonical_chain :
    causallyPrecedes .fluxConservation .depletion ∧
    causallyPrecedes .depletion .projectorInversion ∧
    causallyPrecedes .projectorInversion .reconstruction ∧
    causallyPrecedes .reconstruction .unbrokenRay := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `QuantumFieldProjector.Archetype`
node to its canonical Peirce operator in `[Ring B]`. -/
def quantumFieldProjectorOperator (P A C X : B) : Archetype → B
  | .fluxConservation => evenGrade P X + oddGrade P X
  | .depletion => peirce11 P X * peirce00 P X
  | .projectorInversion => invS P * invS P
  | .reconstruction => evenGrade P (evenGrade P X) + oddGrade P (oddGrade P X)
  | .unbrokenRay => conePlus P A

/-- **Theorem (Non-Commutative Quantum Field Projector Identities over `[Ring B]`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the even and odd
Peirce grades conserve the total operator `evenGrade P X + oddGrade P X = X`, cross-block
depletion `peirce11 P X * peirce00 P X = 0` vanishes, reflection inversion satisfies
`S² = 1`, and idempotent grade projections reconstruct `X`. -/
theorem quantumFieldProjector_operator_identities {P : B} (hP : P * P = P) (A C X : B) :
    quantumFieldProjectorOperator P A C X .fluxConservation = X ∧
    quantumFieldProjectorOperator P A C X .depletion = 0 ∧
    quantumFieldProjectorOperator P A C X .projectorInversion = 1 ∧
    quantumFieldProjectorOperator P A C X .reconstruction = X ∧
    quantumFieldProjectorOperator P A C X .unbrokenRay *
      quantumFieldProjectorOperator P A C X .unbrokenRay = 0 := by
  dsimp only [quantumFieldProjectorOperator]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

end NonCommutativeOperatorRealization

end DetectorGeometry.QuantumFieldProjector
