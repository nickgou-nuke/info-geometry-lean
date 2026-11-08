import InfoGeometry.Canonical.ProjectiveCountsModularBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CauchyResidueReadback
import InfoGeometry.Canonical.BogoliubovHomologyFrameEquiv
import InfoGeometry.Canonical.BottStabilizedFrameEquiv
import InfoGeometry.Meta.Architecture

/-!
# Real Hestenes-Krein Pipeline Capstone

This file is a thin capstone over the real Hestenes-Krein homology stack.

It does not introduce a new owner theorem. It records the final composition
surface:

* projective count ratios give a modular scalar seed;
* boundary-vanishing witnesses descend to real homology classes;
* Bogoliubov/Hestenes/Krein frame equivalences preserve readouts by supplied
  transport laws;
* calibrated Drazin/Hodge residue readouts agree;
* Bott-stabilized frame readouts are invariant only through explicit
  stabilization witnesses.

No full Bott periodicity theorem, trace/density-matrix semantics, complex
contour integral, or automatic harmonic = Drazin-null identification is
asserted here.
-/

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Canonical.RealHestenesKreinPipelineCapstone

open InfoGeometry.Krein
open InfoGeometry.Canonical.ProjectiveCountsModularBridge
open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.RealHomologyCohomologyDictionary
open InfoGeometry.Canonical.DrazinHodgeResidueBridge
open InfoGeometry.Canonical.CauchyResidueReadback
open InfoGeometry.Canonical.BogoliubovHomologyFrameEquiv
open InfoGeometry.Canonical.BottStabilizedFrameEquiv

/-! ## Projective count modular seed readbacks -/

section CountSeed

variable (n : ℕ)

/-- Capstone alias for the projective-count modular scalar seed. -/
@[rep_depth projective]
noncomputable def pipelineCountModularSeed
    (counts ref : RelativeCounts n) : ℝ :=
  countModularScalar n counts ref

/-- Common nonzero count rescaling does not change the modular scalar seed. -/
@[rep_depth projective]
theorem pipelineCountModularSeed_common_smul
    (c : ℝ)
    (hc : c ≠ 0)
    (counts ref : RelativeCounts n) :
    pipelineCountModularSeed n (c • counts) (c • ref)
      =
    pipelineCountModularSeed n counts ref := by
  exact countModularScalar_common_smul (n := n) c hc counts ref

end CountSeed

/-! ## Real doubled Hestenes-Krein pipeline packet -/

section DoubledPipeline

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/--
A theorem-safe real Hestenes-Krein pipeline packet.

The fields are exactly the calibrated data used by the already-owned layers:
frame equivalence, Drazin/Hodge residue calibration, and a scalar witness that
vanishes on source boundaries.
-/
@[rep_depth krein]
structure RealHestenesKreinPipeline where
  frame : HomologyFrameEquiv (E := E)
  residue : DrazinHodgeResidueCalibration (E := H₂)
  witness : H₂ →L[ℝ] ℝ
  witness_vanishes :
    PairsTriviallyOnBoundaries (E := E) frame.Dsrc witness

namespace RealHestenesKreinPipeline

variable (P : RealHestenesKreinPipeline (E := E))

/-- The supplied boundary-vanishing witness descends to source homology classes. -/
@[rep_depth krein]
theorem witness_descends
    {x y : H₂}
    (hxy : HomologyEquivalent (E := E) P.frame.Dsrc x y) :
    P.witness x = P.witness y :=
  witness_descends_to_homologyEquivalent (E := E) P.witness_vanishes hxy

/-- The supplied frame preserves source homology equivalence in the target frame. -/
@[rep_depth transport]
theorem frame_maps_homologyEquivalent
    {x y : H₂}
    (hxy : HomologyEquivalent (E := E) P.frame.Dsrc x y) :
    HomologyEquivalent (E := E) P.frame.Dtgt (P.frame.U x) (P.frame.U y) :=
  P.frame.maps_homologyEquivalent hxy

/-- The supplied frame preserves the real Krein pairing readout. -/
@[rep_depth krein]
theorem frame_preserves_kreinPairing
    (x y : H₂) :
    KreinSpace.kreinInner (H := H₂) (P.frame.U x) (P.frame.U y)
      =
    KreinSpace.kreinInner (H := H₂) x y :=
  P.frame.preserves_kreinPairing_readout x y

/-- The supplied frame transports Drazin-defect representatives. -/
@[rep_depth operator]
theorem frame_maps_drazinDefect
    {x : H₂}
    (hx : IsDrazinDefectState (E := E) P.frame.Qsrc x) :
    IsDrazinDefectState (E := E) P.frame.Qtgt (P.frame.U x) :=
  P.frame.maps_drazinDefectState hx

/-- Calibrated harmonic and Drazin residue readouts agree. -/
@[rep_depth krein]
theorem harmonicResidueReadout_eq_drazinResidueReadout
    (φ : H₂ →L[ℝ] ℝ)
    (x : H₂) :
    harmonicResidueReadout P.residue φ x =
      drazinResidueReadout P.residue φ x :=
  CauchyResidueReadback.harmonicResidueReadout_eq_drazinResidueReadout
    P.residue φ x

/-- On calibrated `Delta`-zero representatives, the residue readout is ordinary evaluation. -/
@[rep_depth krein]
theorem drazinResidueReadout_of_deltaZero
    (φ : H₂ →L[ℝ] ℝ)
    {x : H₂}
    (hx : P.residue.IsDeltaZero x) :
    drazinResidueReadout P.residue φ x = φ x :=
  CauchyResidueReadback.drazinResidueReadout_of_deltaZero P.residue φ hx

end RealHestenesKreinPipeline

end DoubledPipeline

/-! ## Bott-stabilized capstone readbacks -/

section BottPipeline

variable {E F : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "H₂E" => DoubledSpace E
local notation "H₂F" => DoubledSpace F

/--
A Bott-stabilized pipeline packet.

The stabilization itself is supplied as a witness. This packet only exposes
the readbacks forced by that witness.
-/
@[rep_depth krein]
structure BottStabilizedPipeline where
  stabilization : BottStabilizedHomologyFrame (E := E) (F := F)

namespace BottStabilizedPipeline

variable (P : BottStabilizedPipeline (E := E) (F := F))

/-- Bott stabilization preserves source homology equivalence by the supplied witness. -/
@[rep_depth transport]
theorem maps_source_homologyEquivalent
    {x y : H₂E}
    (hxy :
      HomologyEquivalent (E := E) P.stabilization.base.Dsrc x y) :
    HomologyEquivalent (E := F) P.stabilization.stabilized.Dsrc
      (P.stabilization.embed x) (P.stabilization.embed y) :=
  P.stabilization.maps_source_homologyEquivalent hxy

/-- Base scalar witnesses read back unchanged after stabilization and projection. -/
@[rep_depth transport]
theorem stabilizedWitnessOfBase_readout
    (φ : H₂E →L[ℝ] ℝ)
    (x : H₂E) :
    P.stabilization.stabilizedWitnessOfBase φ (P.stabilization.embed x) = φ x :=
  P.stabilization.stabilizedWitnessOfBase_readout φ x

/--
Boundary-vanishing stabilized witnesses descend on base source homology classes
after pullback through stabilization.
-/
@[rep_depth transport]
theorem pullbackStabilizedWitness_descends_on_base
    {φ : H₂F →L[ℝ] ℝ}
    (hφ :
      PairsTriviallyOnBoundaries (E := F) P.stabilization.stabilized.Dsrc φ)
    {x y : H₂E}
    (hxy :
      HomologyEquivalent (E := E) P.stabilization.base.Dsrc x y) :
    φ (P.stabilization.embed x) = φ (P.stabilization.embed y) :=
  P.stabilization.pullbackStabilizedWitness_descends_on_base hφ hxy

/-- Bott stabilization transports Drazin-defect representatives by explicit witness. -/
@[rep_depth operator]
theorem maps_drazinDefectState
    {x : H₂E}
    (hx : IsDrazinDefectState (E := E) P.stabilization.base.Qsrc x) :
    IsDrazinDefectState (E := F) P.stabilization.stabilized.Qsrc
      (P.stabilization.embed x) :=
  P.stabilization.maps_drazinDefectState hx

/-- Bott stabilization transports harmonic-projector fixed representatives by witness. -/
@[rep_depth operator]
theorem maps_harmonicProjectorFixed
    {x : H₂E}
    (hx : P.stabilization.base.Hsrc x = x) :
    P.stabilization.stabilized.Hsrc (P.stabilization.embed x) =
      P.stabilization.embed x :=
  P.stabilization.maps_harmonicProjectorFixed hx

end BottStabilizedPipeline

end BottPipeline

end InfoGeometry.Canonical.RealHestenesKreinPipelineCapstone

