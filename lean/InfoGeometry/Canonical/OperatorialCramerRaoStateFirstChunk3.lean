import InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.Fock
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3

Chunk-3 translation of the state-first/type-III doctrine into repo-native Lean.

This file adds a conservative admissibility gate layered above existing owners:

1. a Fierz-admissible state predicate,
2. an admissible operator predicate = (projector commutation + Fierz state),
3. stability under modular-flow state transport,
4. stability under projector-compressed operator transport,
5. a wedge-calibrated package theorem tying admissibility to the operatorial
   Cramér-Rao lower bound.
-/

namespace InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.OperatorialCramerRao
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/-- Fierz-admissible states on the doubled carrier. -/
@[rep_depth transport]
def FierzAdmissibleState (ψ : H₂) : Prop :=
  InfoGeometry.Quantum.inducedSymplecticForm (E := E) ψ ψ
    =
  hessian_indefinite_form (E := E) ψ (complex_i (E := E) ψ)

/-- Fierz admissibility holds on every doubled state (owner theorem lift). -/
@[rep_depth transport]
theorem fierzAdmissibleState_true (ψ : H₂) :
    FierzAdmissibleState (E := E) ψ := by
  simpa [FierzAdmissibleState] using
    InfoGeometry.Quantum.inducedSymplecticForm_eq_complex_pairing (E := E) ψ ψ

/--
Conservative state-first admissibility gate:
an operator is admissible at state `ψ` if it commutes with the certified
spectral projector and `ψ` is Fierz-admissible.
-/
@[rep_depth transport]
def StateFirstAdmissibleOperator
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (ψ : H₂) : Prop :=
  Commute CIK.spectralProjector R ∧ FierzAdmissibleState (E := E) ψ

/-- Projector-compressed transport representative used by the CP-002/CP-003 bridge. -/
@[rep_depth transport]
noncomputable def projectorCompressed
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH) : EndH :=
  CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
    + CIK.spectralProjector * R * CIK.spectralProjector

/--
Wedge-calibrated canonical bounded relative modular representatives satisfy the
state-first admissibility gate at any comparison state.
-/
@[rep_depth transport]
theorem stateFirstAdmissibleOperator_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ)
    (ψ : H₂) :
    StateFirstAdmissibleOperator
      (E := E)
      CIK
      (InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
        (E := E) CIK τ)
      ψ := by
  refine ⟨?_, fierzAdmissibleState_true (E := E) ψ⟩
  exact
    (stateFirstCommutationInterface_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ).commutes_with_spectralProjector

/--
State-first admissibility is stable under modular-flow transport of the state.
-/
@[rep_depth transport]
theorem stateFirstAdmissibleOperator_modularFlow_state_stable
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (ψ : H₂)
    (hA : StateFirstAdmissibleOperator (E := E) CIK R ψ)
    (T : InfoGeometry.Canonical.RealTomitaCore.RealModularLogData (E := E))
    (t : ℝ) :
    StateFirstAdmissibleOperator (E := E) CIK R ((T.flow t) ψ) := by
  refine ⟨hA.1, ?_⟩
  exact fierzAdmissibleState_true (E := E) ((T.flow t) ψ)

/--
State-first admissibility is stable under projector-compressed operator
transport on the same certified lane.
-/
@[rep_depth transport]
theorem stateFirstAdmissibleOperator_projectorCompressed_stable
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (ψ : H₂)
    (hA : StateFirstAdmissibleOperator (E := E) CIK R ψ) :
    StateFirstAdmissibleOperator (E := E) CIK (projectorCompressed (E := E) CIK R) ψ := by
  refine ⟨?_, hA.2⟩
  have hCompressedEq :
      projectorCompressed (E := E) CIK R = R := by
    exact
      (InfoGeometry.Canonical.RelativeModularScaleShapeSplit.cp002_cp003_bridge_of_commute
        (E := E) (CIK := CIK) (R := R) hA.1).2.symm
  simpa [hCompressedEq] using hA.1

/--
Chunk-3 capstone package:
on the wedge-calibrated lane, admissibility at the comparison state is stable
under modular-flow state transport and projector-compressed operator transport,
and the operatorial Cramér-Rao lower bound remains available.
-/
@[rep_depth transport, capstone]
theorem stateFirst_admissibleGate_transport_and_operatorialCramerRao
    (CIK : CertifiedInverseKernel H₂)
    (S : StateFirstCRWitness (E := E) CIK)
    (τ t : ℝ) :
    let R :=
      InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
        (E := E) CIK τ
    StateFirstAdmissibleOperator (E := E) CIK R S.comparison
      ∧
    StateFirstAdmissibleOperator
      (E := E)
      CIK
      (projectorCompressed (E := E) CIK R)
      ((InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK).flow t
        S.comparison)
      ∧
    (1 /
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.Y S.Y
      ≤
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.X S.X) := by
  intro R
  have hBase :
      StateFirstAdmissibleOperator (E := E) CIK R S.comparison := by
    exact
      stateFirstAdmissibleOperator_of_wedgeCalibrated
        (E := E) (CIK := CIK) (W := S.W) S.calibrated τ S.comparison
  have hFlow :
      StateFirstAdmissibleOperator
        (E := E)
        CIK
        R
        ((InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK).flow t
          S.comparison) := by
    exact
      stateFirstAdmissibleOperator_modularFlow_state_stable
        (E := E)
        (CIK := CIK)
        (R := R)
        (ψ := S.comparison)
        hBase
        (InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK)
        t
  have hCompressed :
      StateFirstAdmissibleOperator
        (E := E)
        CIK
        (projectorCompressed (E := E) CIK R)
        ((InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK).flow t
          S.comparison) := by
    exact
      stateFirstAdmissibleOperator_projectorCompressed_stable
        (E := E)
        (CIK := CIK)
        (R := R)
        (ψ := (InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK).flow t
          S.comparison)
        hFlow
  refine ⟨hBase, hCompressed, ?_⟩
  exact
    (stateFirst_modularSplit_singularClosure_operatorialCramerRao
      (E := E) (CIK := CIK) (S := S) τ).2

end Core

end InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3
