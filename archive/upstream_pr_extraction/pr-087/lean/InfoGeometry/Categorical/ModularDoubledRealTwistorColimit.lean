import InfoGeometry.Categorical.ModularDoubledRealHopfFibration

/-!
# InfoGeometry.Categorical.ModularDoubledRealTwistorColimit

Twistor and fractal-colimit projection shadows.

This file records the terminology correction:

* the quaternionic Hopf map is the pre-projective projection
  `S^7 -> HP^1 ~= S^4`, with `S^3` fiber;
* after quotienting by global phase, the projective map `CP^3 -> S^4` is the
  twistor fibration, with fiber `CP^1 ~= S^2`;
* the smooth manifold lane is not assumed at the finite symbolic level.  It is
  represented here as a scale-colimit projection: finite/fractal boundary
  stages glue through compatible projections into a continuum boundary readout.

No topology, smooth structure, Mellin transform, or Cantor-set construction is
asserted here.  The file gives the categorical interfaces that those concrete
owners can instantiate.
-/

universe u v w z

namespace InfoGeometry.Categorical.ModularDoubledRealTwistorColimit

open ModularDoubledRealHopfFibration

/-! ## Projective twistor quotient -/

/--
Projective twistor quotient shadow.

`PreProjectiveTotal` is the normalized pre-projective carrier, morally the
`S^7` level.  `ProjectiveTotal` is the global-phase quotient, morally `CP^3`.
`Base` is the entanglement/base readout, morally `HP^1 ~= S^4`.

The descent law says the projective/twistor projection agrees with the
pre-projective Hopf-level projection after quotienting.
-/
structure TwistorQuotientShadow where
  PreProjectiveTotal : Type u
  ProjectiveTotal : Type v
  Base : Type w
  hopfLevelProjection : PreProjectiveTotal → Base
  phaseQuotient : PreProjectiveTotal → ProjectiveTotal
  twistorProjection : ProjectiveTotal → Base
  projection_descends :
    ∀ x : PreProjectiveTotal, twistorProjection (phaseQuotient x) = hopfLevelProjection x

namespace TwistorQuotientShadow

variable (T : TwistorQuotientShadow.{u, v, w})

/-- Fiber of the projective twistor projection over a base point. -/
def TwistorFiber (b : T.Base) : Type v :=
  { x : T.ProjectiveTotal // T.twistorProjection x = b }

/-- The pre-projective point and its projective quotient have the same base readout. -/
theorem quotient_base_readout (x : T.PreProjectiveTotal) :
    T.twistorProjection (T.phaseQuotient x) = T.hopfLevelProjection x :=
  T.projection_descends x

/--
Two pre-projective points that quotient to the same projective point have equal
base readouts.
-/
theorem same_projective_point_same_base
    {x y : T.PreProjectiveTotal} (h : T.phaseQuotient x = T.phaseQuotient y) :
    T.hopfLevelProjection x = T.hopfLevelProjection y := by
  calc
    T.hopfLevelProjection x = T.twistorProjection (T.phaseQuotient x) :=
      (T.projection_descends x).symm
    _ = T.twistorProjection (T.phaseQuotient y) := by rw [h]
    _ = T.hopfLevelProjection y := T.projection_descends y

end TwistorQuotientShadow

/-! ## Fractal scale colimit projection -/

/--
Scale-colimit projection interface for the fractal-boundary-to-continuum lane.

Each finite scale has a stage projection.  The limit objects carry one
continuum projection, and the commuting square says every finite/fractal stage
projects to the same base after passing to the colimit.
-/
structure FractalScaleProjectionData where
  StageTotal : ℕ → Type u
  StageBase : ℕ → Type v
  stageProjection : ∀ n : ℕ, StageTotal n → StageBase n
  TotalLimit : Type w
  BaseLimit : Type z
  stageToLimit : (n : ℕ) → StageTotal n → TotalLimit
  baseToLimit : (n : ℕ) → StageBase n → BaseLimit
  limitProjection : TotalLimit → BaseLimit
  projection_commutes :
    ∀ (n : ℕ) (x : StageTotal n),
      limitProjection (stageToLimit n x) = baseToLimit n (stageProjection n x)

namespace FractalScaleProjectionData

variable (C : FractalScaleProjectionData.{u, v, w, z})

/--
The continuum projection of a stage point is computed by first projecting at
the stage and then embedding the stage base into the base colimit.
-/
theorem stage_projection_commutes (n : ℕ) (x : C.StageTotal n) :
    C.limitProjection (C.stageToLimit n x) =
      C.baseToLimit n (C.stageProjection n x) :=
  C.projection_commutes n x

/--
If two stage points have the same base image after passing to the base colimit,
then their total-limit images have the same continuum base readout.
-/
theorem same_limit_base_of_same_stage_base
    {n : ℕ} {x y : C.StageTotal n}
    (h : C.baseToLimit n (C.stageProjection n x) =
      C.baseToLimit n (C.stageProjection n y)) :
    C.limitProjection (C.stageToLimit n x) =
      C.limitProjection (C.stageToLimit n y) := by
  calc
    C.limitProjection (C.stageToLimit n x) =
        C.baseToLimit n (C.stageProjection n x) := C.projection_commutes n x
    _ = C.baseToLimit n (C.stageProjection n y) := h
    _ = C.limitProjection (C.stageToLimit n y) := (C.projection_commutes n y).symm

/--
The colimit projection itself is a modular doubled-real fibration shadow when
equipped with compatible involutions.
-/
def toModularDoubledRealFibration
    (totalTwist : C.TotalLimit → C.TotalLimit)
    (baseTwist : C.BaseLimit → C.BaseLimit)
    (totalTwist_involutive : Function.Involutive totalTwist)
    (baseTwist_involutive : Function.Involutive baseTwist)
    (projection_twist :
      ∀ x : C.TotalLimit, C.limitProjection (totalTwist x) =
        baseTwist (C.limitProjection x)) :
    ModularDoubledRealHopfFibration.ModularDoubledRealHopf where
  Total := C.TotalLimit
  Base := C.BaseLimit
  projection := C.limitProjection
  modularTwist := totalTwist
  baseTwist := baseTwist
  modularTwist_involutive := totalTwist_involutive
  baseTwist_involutive := baseTwist_involutive
  projection_twist := projection_twist

end FractalScaleProjectionData

end InfoGeometry.Categorical.ModularDoubledRealTwistorColimit
