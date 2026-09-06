import InfoGeometry.Canonical.TypeIIIContinuousCoreReal
import InfoGeometry.Canonical.RNDeterminantConnesChainBridge
import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PedersenTakesakiRNInterface

Conservative interface lane for Pedersen-Takesaki / Vaes-style operator
Radon-Nikodym data on the repo's Type-III carrier.

This file does not claim the full affiliated-operator theorem stack. It fixes a
compiled interface with:

- Type-III modular owner data,
- a candidate density operator `delta`,
- a Connes cocycle witness,
- a scalar-id reduction witness used as current finite/surrogate readout,
- finite operator shadows attached to existing `relativeModularOperator` owners.
-/

namespace InfoGeometry.Canonical.PedersenTakesakiRNInterface

open InfoGeometry.Canonical.TypeIIIContinuousCoreReal
open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.RNDeterminantConnesChainBridge
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Volume.ConnesCocycle

section TypeIIIInterface

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => YangMillsContinuum.EndH E

/--
Interface package for the missing Pedersen-Takesaki/Vaes operator-RN lane.

`delta` is the candidate density operator; in this conservative surface we keep
an explicit scalar-id witness (`delta_eq_densityReadout_smul_id`) so downstream
modules can use it without over-claiming full affiliated-operator machinery.
-/
@[rep_depth transport]
structure AffiliatedOperatorRNInterface where
  base : RealTypeIIIModularData (E := E)
  delta : EndH
  cocycle : ℝ → EndH
  isCocycle : IsConnesCocycle base.additiveFlow cocycle
  modularFixed : ∀ t : ℝ, base.modularFlow t delta = delta
  densityReadout : ℝ
  densityReadout_pos : 0 < densityReadout
  delta_eq_densityReadout_smul_id :
    delta = densityReadout • YangMillsContinuum.idEndH E

namespace AffiliatedOperatorRNInterface

variable (R : AffiliatedOperatorRNInterface (E := E))

/-- Connes cocycle chain law carried by the interface witness. -/
@[rep_depth transport]
theorem cocycle_chain (s t : ℝ) :
    R.cocycle (s + t) = R.cocycle s * R.base.additiveFlow s (R.cocycle t) :=
  connesCocycle_state_chain
    (E := E) (σ := R.base.additiveFlow) (u := R.cocycle) R.isCocycle s t

/-- `delta` lies in the modular-fixed sector by interface contract. -/
@[rep_depth transport]
theorem delta_modularFixed (t : ℝ) :
    R.base.modularFlow t R.delta = R.delta :=
  R.modularFixed t

/-- The interface `delta` commutes with the modular operator readout. -/
@[rep_depth transport]
theorem delta_commutes_modularOperator :
    Commute R.delta R.base.rn.modularOperator := by
  rw [R.delta_eq_densityReadout_smul_id]
  simpa [YangMillsContinuum.idEndH] using
    (Commute.one_left R.base.rn.modularOperator).smul_left R.densityReadout

/--
Packaged interface law:
Connes chain + modular fixed-point + commutation with modular operator.
-/
@[rep_depth transport, capstone]
theorem typeIII_affiliatedRN_interface_package (s t : ℝ) :
    (R.cocycle (s + t) = R.cocycle s * R.base.additiveFlow s (R.cocycle t))
      ∧ (R.base.modularFlow t R.delta = R.delta)
      ∧ Commute R.delta R.base.rn.modularOperator := by
  refine ⟨?_, ?_, ?_⟩
  · exact R.cocycle_chain s t
  · exact R.delta_modularFixed t
  · exact R.delta_commutes_modularOperator

end AffiliatedOperatorRNInterface

end TypeIIIInterface

section FiniteShadow

variable {n : ℕ} [Nonempty (Fin n)]

/--
Finite operator shadow for the affiliated-density lane:
reuse the existing finite owner `relativeModularOperator`.
-/
@[rep_depth operator]
noncomputable def finiteAffiliatedDensity
    (q q0 : PositiveRay (Fin n)) :=
  relativeModularOperator (n := n) q q0

@[rep_depth operator]
theorem finiteAffiliatedDensity_diag_pos
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    0 < finiteAffiliatedDensity (n := n) q q0 i i := by
  rw [finiteAffiliatedDensity, relativeModularOperator_diag_eq_exp_relativeLogDensity]
  exact Real.exp_pos _

@[rep_depth operator]
theorem finiteAffiliatedDensity_chain
    (q q0 q1 : PositiveRay (Fin n)) :
    finiteAffiliatedDensity (n := n) q q1
      = finiteAffiliatedDensity (n := n) q q0
          * finiteAffiliatedDensity (n := n) q0 q1 := by
  simpa [finiteAffiliatedDensity] using
    relativeModularOperator_state_chain (n := n) q q0 q1

/--
Finite package for the first operator-RN lane:
strict positivity of diagonal entries and cocycle composition.
-/
@[rep_depth operator, capstone]
theorem finite_affiliatedRN_shadow_package
    (q q0 q1 : PositiveRay (Fin n)) (i : Fin n) :
    (0 < finiteAffiliatedDensity (n := n) q q0 i i)
      ∧ (finiteAffiliatedDensity (n := n) q q1
          = finiteAffiliatedDensity (n := n) q q0
              * finiteAffiliatedDensity (n := n) q0 q1) := by
  refine ⟨?_, ?_⟩
  · exact finiteAffiliatedDensity_diag_pos (n := n) q q0 i
  · exact finiteAffiliatedDensity_chain (n := n) q q0 q1

end FiniteShadow

end InfoGeometry.Canonical.PedersenTakesakiRNInterface
