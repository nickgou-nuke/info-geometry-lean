import InfoGeometry.Canonical.RealHomologyCohomologyDictionary
import InfoGeometry.Canonical.HestenesCohomology
import InfoGeometry.Canonical.DrazinHodgeResidueBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Canonical.BogoliubovHomologyFrameEquiv

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealHomologyCohomologyDictionary
open InfoGeometry.Canonical.HestenesCohomology

/-!
# Bogoliubov homology frame equivalence

This file packages the real homology/cohomology frame-change interface.

A frame equivalence is not just an invertible operator.  It carries explicit
transport laws for the boundary, Drazin defect projector, harmonic projector,
Krein pairing, and internal phase axis.  The theorems here prove only the
readbacks forced by those fields.
-/

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Structure-preserving frame equivalence for real homology/cohomology readouts on
a fixed doubled carrier.
-/
@[rep_depth krein]
structure HomologyFrameEquiv where
  /-- Forward frame map. -/
  U : EndH

  /-- Inverse frame map. -/
  Uinv : EndH

  /-- Left inverse law. -/
  inverse_left : Uinv.comp U = ContinuousLinearMap.id ℝ H₂

  /-- Right inverse law. -/
  inverse_right : U.comp Uinv = ContinuousLinearMap.id ℝ H₂

  /-- Source boundary/differential. -/
  Dsrc : EndH

  /-- Target boundary/differential. -/
  Dtgt : EndH

  /-- Boundary transport law: `U ∂₁ = ∂₂ U`. -/
  preserves_boundary : U.comp Dsrc = Dtgt.comp U

  /-- Source Drazin defect/complement projector. -/
  Qsrc : EndH

  /-- Target Drazin defect/complement projector. -/
  Qtgt : EndH

  /-- Drazin defect transport law. -/
  preserves_drazinDefect : U.comp Qsrc = Qtgt.comp U

  /-- Source harmonic projector. -/
  Hsrc : EndH

  /-- Target harmonic projector. -/
  Htgt : EndH

  /-- Harmonic projector transport law. -/
  preserves_harmonicProjector : U.comp Hsrc = Htgt.comp U

  /-- Real Krein-pairing preservation. -/
  preserves_krein : KreinSpace.IsKreinIsometry (H := H₂) U

  /-- Internal Hestenes phase-axis preservation. -/
  preserves_phaseAxis :
    U.comp (InfoGeometry.Krein.clockAxis (E := E)) =
      (InfoGeometry.Krein.clockAxis (E := E)).comp U

namespace HomologyFrameEquiv

variable (F : HomologyFrameEquiv (E := E))

/-- The inverse-frame pullback of a scalar real property. -/
@[rep_depth transport]
noncomputable def transportScalarWitness
    (φ : H₂ →L[ℝ] ℝ) : H₂ →L[ℝ] ℝ :=
  φ.comp F.Uinv

/-- Frame maps transport source cycles to target cycles. -/
@[rep_depth transport]
theorem maps_cycle
    {x : H₂}
    (hx : IsRealCycle (E := E) F.Dsrc x) :
    IsRealCycle (E := E) F.Dtgt (F.U x) := by
  unfold IsRealCycle at hx ⊢
  have h := congrArg (fun T : EndH => T x) F.preserves_boundary
  simpa [ContinuousLinearMap.comp_apply, hx] using h.symm

/-- Frame maps transport source boundaries to target boundaries. -/
@[rep_depth transport]
theorem maps_boundary
    {x : H₂}
    (hx : IsRealBoundary (E := E) F.Dsrc x) :
    IsRealBoundary (E := E) F.Dtgt (F.U x) := by
  unfold IsRealBoundary at hx ⊢
  rcases hx with ⟨y, hy⟩
  refine ⟨F.U y, ?_⟩
  have h := congrArg (fun T : EndH => T y) F.preserves_boundary
  calc
    F.Dtgt (F.U y) = F.U (F.Dsrc y) := by
      simpa [ContinuousLinearMap.comp_apply] using h.symm
    _ = F.U x := by rw [hy]

/-- Frame maps preserve homology equivalence. -/
@[rep_depth transport]
theorem maps_homologyEquivalent
    {x y : H₂}
    (hxy : HomologyEquivalent (E := E) F.Dsrc x y) :
    HomologyEquivalent (E := E) F.Dtgt (F.U x) (F.U y) := by
  unfold HomologyEquivalent IsRealBoundary at hxy ⊢
  rcases hxy with ⟨z, hz⟩
  refine ⟨F.U z, ?_⟩
  have h := congrArg (fun T : EndH => T z) F.preserves_boundary
  calc
    F.Dtgt (F.U z) = F.U (F.Dsrc z) := by
      simpa [ContinuousLinearMap.comp_apply] using h.symm
    _ = F.U (x - y) := by rw [hz]
    _ = F.U x - F.U y := by simp

/-- Transported scalar witnesses have the same readout on transported states. -/
@[rep_depth transport]
theorem transportedScalarWitness_readout_eq
    (φ : H₂ →L[ℝ] ℝ)
    (x : H₂) :
    F.transportScalarWitness φ (F.U x) = φ x := by
  unfold transportScalarWitness
  have hx : F.Uinv (F.U x) = x := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : EndH => T x) F.inverse_left
  simp [hx]

/-- Krein-pairing readouts are frame-invariant. -/
@[rep_depth krein]
theorem preserves_kreinPairing_readout
    (x y : H₂) :
    KreinSpace.kreinInner (H := H₂) (F.U x) (F.U y) =
      KreinSpace.kreinInner (H := H₂) x y :=
  F.preserves_krein x y

/-- The frame is K-linear in the Hestenes sense. -/
@[rep_depth krein]
theorem isHestenesCochainOperator_U :
    IsHestenesCochainOperator (E := E) F.U :=
  F.preserves_phaseAxis

/-- Frame maps transport Drazin-defect representatives. -/
@[rep_depth operator]
theorem maps_drazinDefectState
    {x : H₂}
    (hx : IsDrazinDefectState (E := E) F.Qsrc x) :
    IsDrazinDefectState (E := E) F.Qtgt (F.U x) := by
  unfold IsDrazinDefectState at hx ⊢
  have h := congrArg (fun T : EndH => T x) F.preserves_drazinDefect
  calc
    F.Qtgt (F.U x) = F.U (F.Qsrc x) := by
      simpa [ContinuousLinearMap.comp_apply] using h.symm
    _ = F.U x := by rw [hx]

/-- Frame maps transport harmonic-projector fixed representatives. -/
@[rep_depth operator]
theorem maps_harmonicProjectorFixed
    {x : H₂}
    (hx : F.Hsrc x = x) :
    F.Htgt (F.U x) = F.U x := by
  have h := congrArg (fun T : EndH => T x) F.preserves_harmonicProjector
  calc
    F.Htgt (F.U x) = F.U (F.Hsrc x) := by
      simpa [ContinuousLinearMap.comp_apply] using h.symm
    _ = F.U x := by rw [hx]

/-- Transported witnesses that kill target boundaries descend on transported source classes. -/
@[rep_depth transport]
theorem transportedWitness_descends_on_source_homology
    {φ : H₂ →L[ℝ] ℝ}
    (hφ : PairsTriviallyOnBoundaries (E := E) F.Dtgt φ)
    {x y : H₂}
    (hxy : HomologyEquivalent (E := E) F.Dsrc x y) :
    φ (F.U x) = φ (F.U y) := by
  exact property_descends_to_homologyEquivalent (E := E) hφ
    (F.maps_homologyEquivalent hxy)

end HomologyFrameEquiv

end Core

end InfoGeometry.Canonical.BogoliubovHomologyFrameEquiv
