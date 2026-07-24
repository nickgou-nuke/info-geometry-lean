import InfoGeometry.Canonical.BogoliubovHomologyFrameEquiv
import InfoGeometry.Canonical.BogoliubovCartanEigenOperator
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Canonical.BottStabilizedFrameEquiv

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealHomologyCohomologyDictionary
open InfoGeometry.Canonical.BogoliubovHomologyFrameEquiv
open InfoGeometry.Canonical.BogoliubovCartanEigenOperator

/-!
# Bott-stabilized frame equivalence

This file is a theorem-safe socket for Bott/Clifford stabilization of the real
Hestenes--Krein homology frame language.

It does not construct a universal Clifford tensor product equivalence.  Instead
it records the exact data needed to say that a stabilized frame preserves the
same readouts as the base frame:

* an embedding/projection between doubled carriers;
* boundary transport;
* Drazin-defect and harmonic-projector transport;
* compatibility with frame action;
* preservation of the internal Hestenes phase axis;
* optional readout equality through the projection;
* Cartan weight preservation as an explicitly supplied operator transport law.
-/

section StabilizationSocket

variable {E F : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "H₂E" => DoubledSpace E
local notation "H₂F" => DoubledSpace F
local notation "EndE" => H₂E →L[ℝ] H₂E
local notation "EndF" => H₂F →L[ℝ] H₂F

/--
Witness-gated Bott stabilization data for two homology frame equivalences.

`embed` is the stabilized inclusion and `project` is the readback projection.
The left inverse law says that the base carrier is recovered after stabilizing
and reading back.
-/
@[rep_depth krein]
structure BottStabilizedHomologyFrame where
  /-- Base frame equivalence. -/
  base : HomologyFrameEquiv (E := E)

  /-- Stabilized frame equivalence. -/
  stabilized : HomologyFrameEquiv (E := F)

  /-- Stabilization/inclusion map. -/
  embed : H₂E →L[ℝ] H₂F

  /-- Readback/projection map. -/
  project : H₂F →L[ℝ] H₂E

  /-- Readback after stabilization recovers the base representative. -/
  left_inv : project.comp embed = ContinuousLinearMap.id ℝ H₂E

  /-- Source boundary is transported into the stabilized source boundary. -/
  source_boundary :
    embed.comp base.Dsrc = stabilized.Dsrc.comp embed

  /-- Target boundary is transported into the stabilized target boundary. -/
  target_boundary :
    embed.comp base.Dtgt = stabilized.Dtgt.comp embed

  /-- Drazin defect projector is transported by stabilization. -/
  drazin_defect :
    embed.comp base.Qsrc = stabilized.Qsrc.comp embed

  /-- Harmonic projector is transported by stabilization. -/
  harmonic_projector :
    embed.comp base.Hsrc = stabilized.Hsrc.comp embed

  /-- Stabilization commutes with the frame map. -/
  frame_action :
    embed.comp base.U = stabilized.U.comp embed

  /-- Stabilization preserves the internal Hestenes phase axis. -/
  phase_axis :
    embed.comp (InfoGeometry.Krein.clockAxis (E := E))
      =
    (InfoGeometry.Krein.clockAxis (E := F)).comp embed

namespace BottStabilizedHomologyFrame

variable (S : BottStabilizedHomologyFrame (E := E) (F := F))

/-- Pointwise readback of the left inverse law. -/
@[rep_depth transport]
theorem project_embed
    (x : H₂E) :
    S.project (S.embed x) = x := by
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun T : H₂E →L[ℝ] H₂E => T x) S.left_inv

/-- Stabilization maps source cycles to source cycles. -/
@[rep_depth transport]
theorem maps_source_cycle
    {x : H₂E}
    (hx : IsRealCycle (E := E) S.base.Dsrc x) :
    IsRealCycle (E := F) S.stabilized.Dsrc (S.embed x) := by
  unfold IsRealCycle at hx ⊢
  have h := congrArg (fun T : H₂E →L[ℝ] H₂F => T x) S.source_boundary
  simpa [ContinuousLinearMap.comp_apply, hx] using h.symm

/-- Stabilization maps source boundaries to source boundaries. -/
@[rep_depth transport]
theorem maps_source_boundary
    {x : H₂E}
    (hx : IsRealBoundary (E := E) S.base.Dsrc x) :
    IsRealBoundary (E := F) S.stabilized.Dsrc (S.embed x) := by
  unfold IsRealBoundary at hx ⊢
  rcases hx with ⟨y, hy⟩
  refine ⟨S.embed y, ?_⟩
  have h := congrArg (fun T : H₂E →L[ℝ] H₂F => T y) S.source_boundary
  calc
    S.stabilized.Dsrc (S.embed y) = S.embed (S.base.Dsrc y) := by
      simpa [ContinuousLinearMap.comp_apply] using h.symm
    _ = S.embed x := by rw [hy]

/-- Stabilization preserves source homology equivalence. -/
@[rep_depth transport]
theorem maps_source_homologyEquivalent
    {x y : H₂E}
    (hxy : HomologyEquivalent (E := E) S.base.Dsrc x y) :
    HomologyEquivalent (E := F) S.stabilized.Dsrc (S.embed x) (S.embed y) := by
  unfold HomologyEquivalent IsRealBoundary at hxy ⊢
  rcases hxy with ⟨z, hz⟩
  refine ⟨S.embed z, ?_⟩
  have h := congrArg (fun T : H₂E →L[ℝ] H₂F => T z) S.source_boundary
  calc
    S.stabilized.Dsrc (S.embed z) = S.embed (S.base.Dsrc z) := by
      simpa [ContinuousLinearMap.comp_apply] using h.symm
    _ = S.embed (x - y) := by rw [hz]
    _ = S.embed x - S.embed y := by simp

/-- Stabilization maps Drazin-defect representatives to Drazin-defect representatives. -/
@[rep_depth operator]
theorem maps_drazinDefectState
    {x : H₂E}
    (hx : IsDrazinDefectState (E := E) S.base.Qsrc x) :
    IsDrazinDefectState (E := F) S.stabilized.Qsrc (S.embed x) := by
  unfold IsDrazinDefectState at hx ⊢
  have h := congrArg (fun T : H₂E →L[ℝ] H₂F => T x) S.drazin_defect
  calc
    S.stabilized.Qsrc (S.embed x) = S.embed (S.base.Qsrc x) := by
      simpa [ContinuousLinearMap.comp_apply] using h.symm
    _ = S.embed x := by rw [hx]

/-- Stabilization maps harmonic-projector fixed representatives to fixed representatives. -/
@[rep_depth operator]
theorem maps_harmonicProjectorFixed
    {x : H₂E}
    (hx : S.base.Hsrc x = x) :
    S.stabilized.Hsrc (S.embed x) = S.embed x := by
  have h := congrArg (fun T : H₂E →L[ℝ] H₂F => T x) S.harmonic_projector
  calc
    S.stabilized.Hsrc (S.embed x) = S.embed (S.base.Hsrc x) := by
      simpa [ContinuousLinearMap.comp_apply] using h.symm
    _ = S.embed x := by rw [hx]

/-- Stabilization commutes with frame action on representatives. -/
@[rep_depth transport]
theorem frame_action_apply
    (x : H₂E) :
    S.stabilized.U (S.embed x) = S.embed (S.base.U x) := by
  have h := congrArg (fun T : H₂E →L[ℝ] H₂F => T x) S.frame_action
  simpa [ContinuousLinearMap.comp_apply] using h.symm

/-- Stabilization preserves the internal Hestenes phase-axis relation pointwise. -/
@[rep_depth krein]
theorem phase_axis_apply
    (x : H₂E) :
    S.embed (InfoGeometry.Krein.clockAxis (E := E) x)
      =
    InfoGeometry.Krein.clockAxis (E := F) (S.embed x) := by
  have h := congrArg (fun T : H₂E →L[ℝ] H₂F => T x) S.phase_axis
  simpa [ContinuousLinearMap.comp_apply] using h

/-- Pull a stabilized scalar witness back to the base carrier. -/
@[rep_depth transport]
noncomputable def pullbackStabilizedWitness
    (φ : H₂F →L[ℝ] ℝ) : H₂E →L[ℝ] ℝ :=
  φ.comp S.embed

/-- Push a base scalar witness to the stabilized carrier through the readback projection. -/
@[rep_depth transport]
noncomputable def stabilizedWitnessOfBase
    (φ : H₂E →L[ℝ] ℝ) : H₂F →L[ℝ] ℝ :=
  φ.comp S.project

/-- Readout through a pushed-forward base witness agrees after stabilization. -/
@[rep_depth transport]
theorem stabilizedWitnessOfBase_readout
    (φ : H₂E →L[ℝ] ℝ)
    (x : H₂E) :
    S.stabilizedWitnessOfBase φ (S.embed x) = φ x := by
  unfold stabilizedWitnessOfBase
  simp [S.project_embed x]

/--
If the stabilized witness vanishes on stabilized source boundaries, its pullback
vanishes on base source boundaries.
-/
@[rep_depth transport]
theorem pullbackStabilizedWitness_vanishesOnBoundaries
    {φ : H₂F →L[ℝ] ℝ}
    (hφ : PairsTriviallyOnBoundaries (E := F) S.stabilized.Dsrc φ) :
    PairsTriviallyOnBoundaries (E := E) S.base.Dsrc (S.pullbackStabilizedWitness φ) := by
  intro y
  unfold pullbackStabilizedWitness
  change φ (S.embed (S.base.Dsrc y)) = 0
  have h := congrArg (fun T : H₂E →L[ℝ] H₂F => T y) S.source_boundary
  rw [show S.embed (S.base.Dsrc y) = S.stabilized.Dsrc (S.embed y) by
    simpa [ContinuousLinearMap.comp_apply] using h]
  exact hφ (S.embed y)

/--
Stabilized boundary-vanishing witnesses descend to base homology classes after
pullback.
-/
@[rep_depth transport]
theorem pullbackStabilizedWitness_descends_on_base
    {φ : H₂F →L[ℝ] ℝ}
    (hφ : PairsTriviallyOnBoundaries (E := F) S.stabilized.Dsrc φ)
    {x y : H₂E}
    (hxy : HomologyEquivalent (E := E) S.base.Dsrc x y) :
    φ (S.embed x) = φ (S.embed y) := by
  exact witness_descends_to_homologyEquivalent (E := F) hφ
    (S.maps_source_homologyEquivalent hxy)

end BottStabilizedHomologyFrame

end StabilizationSocket

/-! ## Cartan-weight stabilization socket -/

section CartanWeight

variable {E F : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "H₂E" => DoubledSpace E
local notation "H₂F" => DoubledSpace F
local notation "EndE" => H₂E →L[ℝ] H₂E
local notation "EndF" => H₂F →L[ℝ] H₂F

/--
Witness that Bott stabilization preserves a Cartan eigen-operator weight.

The operator transport law itself is supplied as data; this file does not
construct a universal Clifford tensor functor on bounded operators.
-/
@[rep_depth krein]
structure BottCartanWeightStabilization where
  Hbase : EndE
  Abase : EndE
  Hstab : EndF
  Astab : EndF
  weight : ℝ
  base_weight :
    IsCartanEigenOperator (E := E) Hbase Abase weight
  stabilized_weight :
    IsCartanEigenOperator (E := F) Hstab Astab weight

namespace BottCartanWeightStabilization

variable (C : BottCartanWeightStabilization (E := E) (F := F))

/-- Readback: the base operator has the supplied Cartan weight. -/
@[rep_depth krein]
theorem base_weight_readback :
    IsCartanEigenOperator (E := E) C.Hbase C.Abase C.weight :=
  C.base_weight

/-- Readback: the stabilized operator has the same supplied Cartan weight. -/
@[rep_depth krein]
theorem stabilized_weight_readback :
    IsCartanEigenOperator (E := F) C.Hstab C.Astab C.weight :=
  C.stabilized_weight

end BottCartanWeightStabilization

end CartanWeight

end InfoGeometry.Canonical.BottStabilizedFrameEquiv
