import Mathlib.Analysis.Normed.Algebra.Exponential
import InfoGeometry.Krein.Thermal
import InfoGeometry.OperatorAlgebra.VerifiedCasimir
import InfoGeometry.OperatorAlgebra.SymmetryInvariants

/-!
# Individuated Modular Thermal States

EN: This module formalizes the emergence of KMS thermal states and their 
    anchoring to the macroscopic Casimir invariants of the operator algebra.
BG: Този модул формализира появата на KMS топлинни състояния и тяхното 
    закотвяне към макроскопичните Казимирови инварианти на операторната алгебра.

Redline: Real Hestenes-Krein modular flow (Language B).
Mathlib: Complex KMS boundary conditions via Rosetta transport (Language A).
Comparison: `InfoGeometry.Krein.satisfies_kms_like`
Upstairs: Algebraic modular automorphism group (ℝ).

References:
- Tomita-Takesaki Theory
- Goutev's Principle of Macroscopic Individuation
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ModularThermalState

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra
open IndividuatedCasimir

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndK" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndK := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndK := inferInstance
local instance : IsTopologicalRing EndK := inferInstance
local instance : CompleteSpace EndK := inferInstance

/-! ## 1. The Individuated KMS State -/

/-- 
A constructively verified KMS Thermal State.
This replaces the `kms_boundary : Prop` shadow by binding the 
expectation value functional `ω` to the generator `K`.
-/
structure VerifiedKMSState (K : EndK) where
  /-- The expectation value functional (State) -/
  ω : EndK →L[ℝ] ℝ
  
  /-- Inverse Temperature (β = 1 / T = 2π / a) -/
  β : ℝ
  
  /-- 
  The Constructive KMS Identity:
  ω(A * σ_β(B)) = ω(B * A)
  This realizes imaginary time iβ as a real shift β in the K-axis.
  -/
  kms_boundary_condition : satisfies_kms_like K ω β

variable {K : EndK}

/-! ## 2. The Casimir-Thermal Anchor -/

/--
A Thermodynamic Anchor binds the microscopic KMS state to the 
macroscopic geometry (the Casimir invariant).
-/
structure IndividuatedThermodynamicAnchor
    {G : Type*} [Group G] 
    (α : SymmetryAction G EndK)
    (K : EndK) where
  /-- The verified thermal state -/
  state : VerifiedKMSState K
  
  /-- The macroscopic observer (Casimir) -/
  casimir : VerifiedCasimir α
  
  /-- 
  The Macroscopic Readout:
  The value of the state on the Casimir element is the Macroscopic Entropy.
  -/
  entropy : ℝ
  entropy_match : state.ω casimir.C = entropy

/-! ## 3. Constructive Invariance (Rubedo) -/

set_option linter.unusedSectionVars false in
/--
Every verified Casimir commutes with the real modular exponential.

This is not a separate hypothesis: it follows from centrality of the Casimir.
-/
theorem casimir_commutes_with_modular_exp
    {G : Type*} [Group G]
    (K : EndK)
    (α : SymmetryAction G EndK)
    (V : VerifiedCasimir α)
    (β : ℝ) :
    Commute (NormedSpace.exp (β • K)) V.C := by
  exact (V.is_central (NormedSpace.exp (β • K))).symm

/-- 
CONSTRUCTIVE THEOREM: Casimir Stationarity.
A Casimir invariant is necessarily stationary under the modular flow 
it generates, as it belongs to the center of the algebra.
-/
theorem casimir_is_stationary
    {G : Type*} [Group G] 
    (K : EndK)
    (α : SymmetryAction G EndK)
    (V : VerifiedCasimir α) :
    ∀ β : ℝ, modular_shift K β V.C = V.C := by
  intro β
  let ePos : EndK := NormedSpace.exp (β • K)
  let eNeg : EndK := NormedSpace.exp (-(β • K))
  have hComm : Commute ePos V.C := by
    simpa [ePos] using casimir_commutes_with_modular_exp K α V β
  have hExpComm : Commute (β • K) (-(β • K)) := by
    exact (Commute.refl (β • K)).neg_right
  have hCancel : ePos * eNeg = (1 : EndK) := by
    calc
      ePos * eNeg
        = NormedSpace.exp (β • K + -(β • K)) := by
            symm
            simpa [ePos, eNeg] using NormedSpace.exp_add_of_commute hExpComm
      _ = (1 : EndK) := by
            simp
  calc
    modular_shift K β V.C
      = ePos * V.C * eNeg := by
          simp [modular_shift, InfoGeometry.Krein.krein_modular_shift, ePos, eNeg]
    _ = (V.C * ePos) * eNeg := by
          rw [hComm.eq]
    _ = V.C * (ePos * eNeg) := by
          simp [mul_assoc]
    _ = V.C := by
          simp [hCancel]

end InfoGeometry.OperatorAlgebra.ModularThermalState
