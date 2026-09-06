import InfoGeometry.Canonical.DIIIDrazinEntropyBridge

/-!
# InfoGeometry.Canonical.DIIIModularEntropyFlowBridge

Dynamic modular/decoherence extension of the finite DIII/Z₂ entropy bridge.

This file stays in the associative, theorem-safe lane:

* the static DIII bridge supplies boundary zero-mode and MP/Drazin entropy
  nonnegativity;
* a model supplies a modular/decoherence flow on entropy states;
* the model also supplies preservation of validity and nonnegative entropy
  along that flow.

No Tomita-Takesaki theorem, Lindblad theorem, decoherence monotonicity theorem,
or entropy production theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.DIIIDrazinEntropyBridge
open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Quantum.BulkBoundary

/--
State-level modular/decoherence flow for a fixed Drazin entropy functional.

The preservation law is deliberately supplied as data.  This structure says:
if a state is valid and starts with nonnegative Drazin entropy, then the
modular/decoherence evolution keeps that entropy nonnegative.
-/
structure ModularDrazinEntropyFlow
    {Op State : Type*}
    (entropyFunctional : InfoGeometry.OperatorAlgebra.DrazinEntropyFunctional Op State)
    (Time : Type*) where
  /-- Modular/decoherence flow on entropy states. -/
  flow : Time → State → State

  /-- Valid states remain valid along the flow. -/
  valid_preserved :
    ∀ t s,
      entropyFunctional.readout.valid s →
        entropyFunctional.readout.valid (flow t s)

  /-- Model-specific entropy transport law. -/
  entropyTransportLaw : Prop

  /-- Certificate for the entropy transport law. -/
  entropyTransport_valid :
    entropyTransportLaw

  /-- Nonnegative entropy is preserved along valid flow lines. -/
  entropy_nonneg_preserved :
    ∀ t s,
      entropyFunctional.readout.valid s →
      0 ≤ entropyFunctional.entropy s →
        0 ≤ entropyFunctional.entropy (flow t s)

namespace ModularDrazinEntropyFlow

variable {Op State Time : Type*}
variable {F : InfoGeometry.OperatorAlgebra.DrazinEntropyFunctional Op State}
variable (M : ModularDrazinEntropyFlow F Time)

/-- Validity is preserved along the modular/decoherence flow. -/
theorem valid_along
    (t : Time) (s : State)
    (hs : F.readout.valid s) :
    F.readout.valid (M.flow t s) :=
  M.valid_preserved t s hs

/-- The supplied entropy transport law is available. -/
theorem entropyTransport_holds :
    M.entropyTransportLaw :=
  M.entropyTransport_valid

/-- Nonnegative entropy is preserved along valid flow lines. -/
theorem entropy_nonneg_along
    (t : Time) (s : State)
    (hs : F.readout.valid s)
    (hS : 0 ≤ F.entropy s) :
    0 ≤ F.entropy (M.flow t s) :=
  M.entropy_nonneg_preserved t s hs hS

end ModularDrazinEntropyFlow

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable [FiniteDimensional ℝ S]

/--
DIII modular entropy-flow bridge.

This consumes the static DIII/Z₂ entropy bridge and adds a supplied
modular/decoherence flow on the same entropy state space.
-/
structure DIIIModularEntropyFlowBridge
    (M : RealMajoranaDatum (S := S))
    (P0 : KPolarization (S := S) M)
    (Op State Time : Type*) where
  /-- Static DIII/Z₂ boundary entropy bridge. -/
  base :
    DIIIZ2DivisionEntropyBridge (S := S) M P0 Op State

  /-- Modular/decoherence flow for the base bridge's entropy functional. -/
  modularEntropyFlow :
    ModularDrazinEntropyFlow
      base.divisionEntropy.calibration.functional
      Time

namespace DIIIModularEntropyFlowBridge

variable {M : RealMajoranaDatum (S := S)}
variable {P0 : KPolarization (S := S) M}
variable {Op State Time : Type*}
variable (B : DIIIModularEntropyFlowBridge (S := S) M P0 Op State Time)

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
/-- The DIII sector state remains valid under modular/decoherence flow. -/
theorem state_valid_along_DIII_modular_flow
    (t : Time) :
    B.base.divisionEntropy.calibration.functional.readout.valid
      (B.modularEntropyFlow.flow t B.base.stateOfChain) :=
  B.modularEntropyFlow.valid_along t B.base.stateOfChain B.base.state_valid

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
/--
The static DIII entropy nonnegativity result is preserved along the supplied
modular/decoherence flow.
-/
theorem entropy_nonneg_along_DIII_modular_flow
    (t : Time) :
    0 ≤
      B.base.divisionEntropy.calibration.functional.entropy
        (B.modularEntropyFlow.flow t B.base.stateOfChain) :=
  B.modularEntropyFlow.entropy_nonneg_along
    t
    B.base.stateOfChain
    B.base.state_valid
    B.base.entropy_nonneg_of_DIII_Z2_sector

/--
Dynamic capstone: the DIII/Z₂ sector supplies a boundary zero mode, and the
supplied modular/decoherence flow preserves nonnegative MP/Drazin entropy.
-/
theorem DIII_Z2_boundary_zero_mode_and_entropy_nonneg_along_flow
    (t : Time) :
    HasZeroMode
      (S := S)
      (globalChainOperatorFromOpenChain
        (S := S) B.base.localOp B.base.chain)
      ∧
    0 ≤
      B.base.divisionEntropy.calibration.functional.entropy
        (B.modularEntropyFlow.flow t B.base.stateOfChain) :=
  ⟨B.base.hasSurfaceZeroMode,
    B.entropy_nonneg_along_DIII_modular_flow t⟩

end DIIIModularEntropyFlowBridge

end InfoGeometry.Canonical
