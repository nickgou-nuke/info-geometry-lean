import InfoGeometry.Canonical.RealTomitaCore
import InfoGeometry.Canonical.TomitaTakesakiRealStandardForm
import InfoGeometry.Canonical.WedgeBoostModularBridge
import InfoGeometry.Canonical.ChiralOperatorConeClosure
import InfoGeometry.Canonical.ChiralCartanCore
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.RindlerWedgeCartanBridge

Owner-facing bridge for the self-dual Rindler wedge and the chiral Cartan
sector.  The wedge side packages the existing real standard-form `R ↔ L`
exchange and the wedge/boost calibration; the chiral side packages the
operator Cartan split already owned by the chiral cone closure lemmas.

This file does not introduce a new operator model.  It re-exports the existing
owner surfaces in a wedge-oriented package so the `R/L` commutant language and
the chiral Cartan closure language can be cited from a single bridge.
-/

namespace InfoGeometry.Canonical.RindlerWedgeCartanBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealTomitaCore
open InfoGeometry.Canonical.TomitaTakesakiRealStandardForm
open InfoGeometry.Canonical.WedgeBoostModularBridge
open InfoGeometry.Canonical.ChiralOperatorConeClosure
open InfoGeometry.Canonical.ChiralCartanCore

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Self-dual Rindler wedge package in the real standard-form lane.

This collects the existing `R ↔ L` exchange witness together with the
wedge/boost calibration packet.  It does not assert any extra analytic
hypotheses beyond the owner surfaces already present in the repo.
-/
@[rep_depth transport]
structure SelfDualRindlerWedge
    (E : Type 0)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  standardForm : RealStandardForm (E := E)
  calibration : WedgeBoostModularCompatibility (E := E)

namespace SelfDualRindlerWedge

variable (W : SelfDualRindlerWedge E)

/-- Left wedge membership is the right wedge membership of the original form. -/
@[rep_depth transport]
theorem left_wedge_mem_iff_right_wedge (A : EndH) :
    A ∈ W.standardForm.swapLeftRight.leftAlgebra ↔ A ∈ W.standardForm.rightAlgebra := by
  simpa using W.standardForm.mem_leftAlgebra_swapLeftRight_iff A

/-- Right wedge membership is the left wedge membership of the original form. -/
@[rep_depth transport]
theorem right_wedge_mem_iff_left_wedge (A : EndH) :
    A ∈ W.standardForm.swapLeftRight.rightAlgebra ↔ A ∈ W.standardForm.leftAlgebra := by
  simpa using W.standardForm.mem_rightAlgebra_swapLeftRight_iff A

/-- Left/right exchange is involutive on the real standard-form package. -/
@[rep_depth transport]
theorem swapLeftRight_involutive :
    (W.standardForm.swapLeftRight).swapLeftRight = W.standardForm := by
  simpa using W.standardForm.swapLeftRight_involutive

/-- The wedge boost calibration identifies modular flow with the Unruh flow. -/
@[rep_depth transport]
theorem modular_flow_at_wedgeParameter (τ : ℝ) :
    InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow
      W.calibration.modularSeed (RealTomitaCore.modularTimeOfWedgeBoost τ)
      = InfoGeometry.Dynamics.unruhFlow (E := E) τ := by
  simpa using
    InfoGeometry.Canonical.WedgeBoostModularBridge.WedgeBoostModularCompatibility.flow_at_wedgeParameter
      (W := W.calibration) τ

end SelfDualRindlerWedge

/--
Chiral Cartan package on the certified inverse-kernel lane.

This does not create a new Cartan decomposition; it exposes the existing
compact/noncompact closure laws under a chiral-oriented name.
-/
@[rep_depth transport]
structure ChiralCartanSplit
    (E : Type 0)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  CIK : CertifiedInverseKernel E

namespace ChiralCartanSplit

local notation "OpE" => E →L[ℝ] E

variable (C : ChiralCartanSplit (E := E))

/-- Two chiral operators multiply into the compact Cartan sector. -/
@[rep_depth krein]
theorem chiral_mul_mem_spectralCompact
    {X Y : OpE}
    (hX : IsInChiralOperatorCone C.CIK X)
    (hY : IsInChiralOperatorCone C.CIK Y) :
    C.CIK.IsSpectralCompact (X * Y) := by
  simpa using
    (mul_mem_spectralCompact_of_chiralOperatorCone (CIK := C.CIK) (X := X) (Y := Y) hX hY)

/-- The Lie commutator of two chiral operators lands in the compact sector. -/
@[rep_depth krein]
theorem chiral_commutator_mem_spectralCompact
    {X Y : OpE}
    (hX : IsInChiralOperatorCone C.CIK X)
    (hY : IsInChiralOperatorCone C.CIK Y) :
    C.CIK.IsSpectralCompact (CertifiedInverseKernel.spectralCommutator X Y) := by
  simpa using
    (spectralCommutator_chiral_chiral_mem_spectralCompact
      (CIK := C.CIK) (X := X) (Y := Y) hX hY)

/-- A compact operator commuted against a chiral operator stays chiral. -/
@[rep_depth krein]
theorem compact_commutator_with_chiral_mem_chiral
    {X Y : OpE}
    (hX : C.CIK.IsSpectralCompact X)
    (hY : IsInChiralOperatorCone C.CIK Y) :
    IsInChiralOperatorCone C.CIK (CertifiedInverseKernel.spectralCommutator X Y) := by
  simpa using
    (spectralCommutator_compact_mem_chiralOperatorCone
      (CIK := C.CIK) (X := X) (Y := Y) hX hY)

/--
Chiral Cartan split package: the operator cone, its compact closure, and the
Cartan commutator rules are all owned by the certified inverse-kernel lane.
-/
@[rep_depth transport, capstone]
theorem cartan_split_packet
    {X Y : OpE}
    (hX : IsInChiralOperatorCone C.CIK X)
    (hY : IsInChiralOperatorCone C.CIK Y) :
    C.CIK.IsSpectralCompact (X * Y)
      ∧ C.CIK.IsSpectralCompact (CertifiedInverseKernel.spectralCommutator X Y) := by
  refine ⟨?_, ?_⟩
  · exact C.chiral_mul_mem_spectralCompact hX hY
  · exact C.chiral_commutator_mem_spectralCompact hX hY

end ChiralCartanSplit

end Core

end InfoGeometry.Canonical.RindlerWedgeCartanBridge
