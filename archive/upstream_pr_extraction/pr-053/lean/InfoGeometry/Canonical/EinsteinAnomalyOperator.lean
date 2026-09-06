import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Canonical.MongeAmpereDualSheetBridge

namespace InfoGeometry.Canonical.ConformalUnification

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Canonical.MongeAmpereDualSheetBridge
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace CertifiedConformalInference

variable (CCI : CertifiedConformalInference E)

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- The property left-projector anomaly operator lifted to the doubled carrier. -/
noncomputable def liftedChiralAnomalyOperator : EndH :=
  dualSheetLift (E := E) CCI.chiralAnomalyOperator

/-- Explicit lifted left-projector anomaly alias on the doubled carrier. -/
noncomputable abbrev liftedLeftChiralAnomalyOperator : EndH :=
  CCI.liftedChiralAnomalyOperator

/--
Canonical lifted projector-obstruction operator on the doubled carrier.
This is the property owner alias used by transport/QGT closures.
-/
noncomputable abbrev liftedProjectorObstructionOperator : EndH :=
  CCI.liftedLeftChiralAnomalyOperator

/-- The property right-projector anomaly operator lifted to the doubled carrier. -/
noncomputable def liftedRightChiralAnomalyOperator : EndH :=
  dualSheetLift (E := E) CCI.rightChiralAnomalyOperator

/--
The singular Einstein anomaly lifted to the doubled carrier.

This keeps the singular naming explicit at the operator level, rather than
passing through a scalar readout.
-/
noncomputable def liftedEinsteinAnomalyOperator : EndH :=
  dualSheetLift (E := E)
    (InfoGeometry.Canonical.EinsteinAnomaly CCI.A CCI.A_MP CCI.A_D)

@[simp] theorem liftedChiralAnomalyOperator_apply_to_doubled
    (x ξ : E) :
    CCI.liftedChiralAnomalyOperator (to_doubled x ξ : H₂) =
      to_doubled (CCI.chiralAnomalyOperator x) (CCI.chiralAnomalyOperator ξ) := by
  change dualSheetLift (E := E) CCI.chiralAnomalyOperator (to_doubled x ξ : H₂) =
      to_doubled (CCI.chiralAnomalyOperator x) (CCI.chiralAnomalyOperator ξ)
  exact dualSheetLift_apply_to_doubled (E := E) (A := CCI.chiralAnomalyOperator) x ξ

@[simp] theorem liftedRightChiralAnomalyOperator_apply_to_doubled
    (x ξ : E) :
    CCI.liftedRightChiralAnomalyOperator (to_doubled x ξ : H₂) =
      to_doubled (CCI.rightChiralAnomalyOperator x) (CCI.rightChiralAnomalyOperator ξ) := by
  simp [liftedRightChiralAnomalyOperator]

@[simp] theorem liftedEinsteinAnomalyOperator_apply_to_doubled
    (x ξ : E) :
    CCI.liftedEinsteinAnomalyOperator (to_doubled x ξ : H₂) =
      to_doubled
        ((InfoGeometry.Canonical.EinsteinAnomaly CCI.A CCI.A_MP CCI.A_D) x)
        ((InfoGeometry.Canonical.EinsteinAnomaly CCI.A CCI.A_MP CCI.A_D) ξ) := by
  simp [liftedEinsteinAnomalyOperator]

omit [CompleteSpace E] in
/--
Every diagonal dual-sheet lift commutes with the doubled-space phase axis
`K = Jε`; hence it is phase-linear.
-/
theorem dualSheetLift_isPhaseLinear
    (A : E →L[ℝ] E) :
    IsPhaseLinear (E := E) (dualSheetLift (E := E) A) := by
  unfold IsPhaseLinear
  apply ContinuousLinearMap.ext
  intro u
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : H₂) = u := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply]

/--
The lifted singular Einstein anomaly is phase-linear on doubled space.
-/
theorem liftedEinsteinAnomalyOperator_isPhaseLinear :
    IsPhaseLinear (E := E) CCI.liftedEinsteinAnomalyOperator := by
  simpa [liftedEinsteinAnomalyOperator] using
    dualSheetLift_isPhaseLinear
      (E := E) (A := InfoGeometry.Canonical.EinsteinAnomaly CCI.A CCI.A_MP CCI.A_D)

omit [CompleteSpace E] in
@[simp] theorem dualSheetLift_neg (A : E →L[ℝ] E) :
    dualSheetLift (E := E) (-A) = -dualSheetLift (E := E) A := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [dualSheetLift, plusPointL, minusPointL, ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
/-- Diagonal lift is faithful: it vanishes exactly when the base operator vanishes. -/
theorem dualSheetLift_eq_zero_iff (A : E →L[ℝ] E) :
    dualSheetLift (E := E) A = 0 ↔ A = 0 := by
  constructor
  · intro hLift
    have hPlus :
        plusBlockMap (E := E) (dualSheetLift (E := E) A)
          = plusBlockMap (E := E) (0 : EndH) := by
      simp [hLift]
    simpa using hPlus
  · intro hA
    subst hA
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;>
      simp [dualSheetLift, plusPointL, minusPointL]

/-- Lifted left anomaly vanishes exactly when the base left anomaly vanishes. -/
theorem liftedLeftChiralAnomalyOperator_eq_zero_iff :
    CCI.liftedLeftChiralAnomalyOperator = 0
      ↔
    CCI.leftChiralAnomalyOperator = 0 := by
  change dualSheetLift (E := E) CCI.leftChiralAnomalyOperator = 0
      ↔ CCI.leftChiralAnomalyOperator = 0
  exact dualSheetLift_eq_zero_iff (E := E) CCI.leftChiralAnomalyOperator

/-- Lifted right anomaly vanishes exactly when the base right anomaly vanishes. -/
theorem liftedRightChiralAnomalyOperator_eq_zero_iff :
    CCI.liftedRightChiralAnomalyOperator = 0
      ↔
    CCI.rightChiralAnomalyOperator = 0 := by
  simpa [liftedRightChiralAnomalyOperator] using
    (dualSheetLift_eq_zero_iff (E := E) CCI.rightChiralAnomalyOperator)

/-- Lifted Einstein anomaly vanishes exactly when the base Einstein anomaly vanishes. -/
theorem liftedEinsteinAnomalyOperator_eq_zero_iff :
    CCI.liftedEinsteinAnomalyOperator = 0
      ↔
    InfoGeometry.Canonical.EinsteinAnomaly CCI.A CCI.A_MP CCI.A_D = 0 := by
  simpa [liftedEinsteinAnomalyOperator] using
    (dualSheetLift_eq_zero_iff (E := E)
      (InfoGeometry.Canonical.EinsteinAnomaly CCI.A CCI.A_MP CCI.A_D))

/-- Lifted left anomaly is nonzero exactly when the base left anomaly is nonzero. -/
theorem liftedLeftChiralAnomalyOperator_ne_zero_iff :
    CCI.liftedLeftChiralAnomalyOperator ≠ 0
      ↔
    CCI.leftChiralAnomalyOperator ≠ 0 := by
  exact not_congr (CCI.liftedLeftChiralAnomalyOperator_eq_zero_iff)

/-- Lifted right anomaly is nonzero exactly when the base right anomaly is nonzero. -/
theorem liftedRightChiralAnomalyOperator_ne_zero_iff :
    CCI.liftedRightChiralAnomalyOperator ≠ 0
      ↔
    CCI.rightChiralAnomalyOperator ≠ 0 := by
  simpa using not_congr (CCI.liftedRightChiralAnomalyOperator_eq_zero_iff)

/-- Lifted Einstein anomaly is nonzero exactly when the base Einstein anomaly is nonzero. -/
theorem liftedEinsteinAnomalyOperator_ne_zero_iff :
    CCI.liftedEinsteinAnomalyOperator ≠ 0
      ↔
    InfoGeometry.Canonical.EinsteinAnomaly CCI.A CCI.A_MP CCI.A_D ≠ 0 := by
  simpa using not_congr (CCI.liftedEinsteinAnomalyOperator_eq_zero_iff)

@[simp] theorem plusProjectorFlux_liftedChiralAnomalyOperator :
    plusProjectorFlux CCI.liftedChiralAnomalyOperator = 0 := by
  simpa only [liftedChiralAnomalyOperator] using
    (plusProjectorFlux_dualSheetLift (E := E) (A := CCI.chiralAnomalyOperator))

@[simp] theorem minusProjectorFlux_liftedChiralAnomalyOperator :
    minusProjectorFlux CCI.liftedChiralAnomalyOperator = 0 := by
  simpa only [liftedChiralAnomalyOperator] using
    (minusProjectorFlux_dualSheetLift (E := E) (A := CCI.chiralAnomalyOperator))

@[simp] theorem plusProjectorFlux_liftedEinsteinAnomalyOperator :
    plusProjectorFlux CCI.liftedEinsteinAnomalyOperator = 0 := by
  simp [liftedEinsteinAnomalyOperator]

@[simp] theorem minusProjectorFlux_liftedEinsteinAnomalyOperator :
    minusProjectorFlux CCI.liftedEinsteinAnomalyOperator = 0 := by
  simp [liftedEinsteinAnomalyOperator]

/--
On the property conformal surface, the lifted singular Einstein anomaly is
exactly the negative of the lifted right-projector anomaly.
-/
theorem liftedEinsteinAnomalyOperator_eq_neg_liftedRightChiralAnomalyOperator :
    CCI.liftedEinsteinAnomalyOperator = -CCI.liftedRightChiralAnomalyOperator := by
  have hLift :
      dualSheetLift (E := E)
          (InfoGeometry.Canonical.EinsteinAnomaly CCI.A CCI.A_MP CCI.A_D)
        =
      dualSheetLift (E := E) (-CCI.toConformalInference.rightChiralAnomalyOperator) := by
    exact congrArg (fun T : E →L[ℝ] E => dualSheetLift (E := E) T)
      CCI.toConformalInference.singularEinsteinAnomaly_eq_neg_rightChiralAnomaly
  simpa [liftedEinsteinAnomalyOperator, liftedRightChiralAnomalyOperator] using hLift

/--
If the Moore-Penrose left and right projectors agree, the lifted singular
Einstein anomaly is the negative of the lifted canonical left anomaly.
-/
theorem liftedEinsteinAnomalyOperator_eq_neg_liftedLeftChiralAnomalyOperator_of_projectorAgreement
    (hProj :
      IsMoorePenroseInverse.rightProjector CCI.A CCI.A_MP =
        IsMoorePenroseInverse.leftProjector CCI.A CCI.A_MP) :
    CCI.liftedEinsteinAnomalyOperator = -CCI.liftedLeftChiralAnomalyOperator := by
  have hLift :
      dualSheetLift (E := E)
          (InfoGeometry.Canonical.EinsteinAnomaly CCI.A CCI.A_MP CCI.A_D)
        =
      dualSheetLift (E := E) (-CCI.toConformalInference.leftChiralAnomalyOperator) := by
    exact congrArg (fun T : E →L[ℝ] E => dualSheetLift (E := E) T)
      (CCI.toConformalInference.singularEinsteinAnomaly_eq_neg_leftChiralAnomaly_of_projectorAgreement
        hProj)
  calc
    CCI.liftedEinsteinAnomalyOperator
        =
      dualSheetLift (E := E)
        (InfoGeometry.Canonical.EinsteinAnomaly CCI.A CCI.A_MP CCI.A_D) := rfl
    _ = dualSheetLift (E := E) (-CCI.toConformalInference.leftChiralAnomalyOperator) := hLift
    _ = -(dualSheetLift (E := E) CCI.toConformalInference.leftChiralAnomalyOperator) := by
          exact dualSheetLift_neg (E := E) CCI.toConformalInference.leftChiralAnomalyOperator
    _ = -CCI.liftedLeftChiralAnomalyOperator := rfl

/--
Projector-agreement closure in canonical naming:
the lifted Einstein anomaly is the negative of the lifted projector obstruction.
-/
theorem liftedEinsteinAnomalyOperator_eq_neg_liftedProjectorObstructionOperator_of_projectorAgreement
    (hProj :
      IsMoorePenroseInverse.rightProjector CCI.A CCI.A_MP =
        IsMoorePenroseInverse.leftProjector CCI.A CCI.A_MP) :
    CCI.liftedEinsteinAnomalyOperator = -CCI.liftedProjectorObstructionOperator := by
  simpa [liftedProjectorObstructionOperator] using
    CCI.liftedEinsteinAnomalyOperator_eq_neg_liftedLeftChiralAnomalyOperator_of_projectorAgreement hProj

/--
The lifted singular Einstein anomaly splits into gauge and source derivation
channels under relative-modular transport.
-/
theorem liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_modularGaugeDeriv_add_relativeModularSourceDeriv
    (hMod : EndH) :
    relativeModularDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator
      =
    modularGaugeDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator
      +
    relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator := by
  exact relativeModularDeriv_eq_modularGaugeDeriv_add_relativeModularSourceDeriv
    (E := E) hMod CCI.liftedEinsteinAnomalyOperator

/--
For the lifted singular Einstein anomaly, the source and sink scaling channels
cancel exactly.
-/
theorem liftedEinsteinAnomalyOperator_relativeModularSourceDeriv_add_relativeModularSinkDeriv
    (hMod : EndH) :
    relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator
      +
    relativeModularSinkDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator
      =
    0 := by
  exact relativeModularSourceDeriv_add_relativeModularSinkDeriv
    (E := E) hMod CCI.liftedEinsteinAnomalyOperator

/--
Equivalent gauge/sink form of the lifted singular Einstein-anomaly derivation
split.
-/
theorem liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_modularGaugeDeriv_sub_relativeModularSinkDeriv
    (hMod : EndH) :
    relativeModularDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator
      =
    modularGaugeDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator
      -
    relativeModularSinkDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator := by
  rw [liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_modularGaugeDeriv_add_relativeModularSourceDeriv
    (CCI := CCI) hMod]
  unfold relativeModularSinkDeriv
  abel

/--
If the gauge sector commutes with the lifted singular Einstein anomaly, its
relative-modular transport is carried entirely by the source channel.
-/
theorem liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_relativeModularSourceDeriv_of_commute_gaugePart
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod)) :
    relativeModularDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator
      =
    relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator := by
  exact relativeModularDeriv_eq_relativeModularSourceDeriv_of_commute_gaugePart
    (E := E) hMod CCI.liftedEinsteinAnomalyOperator hCommGauge

/--
If the scaling sector commutes with the lifted singular Einstein anomaly, its
relative-modular transport is carried entirely by the gauge channel.
-/
theorem liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_modularGaugeDeriv_of_commute_scalePart
    (hMod : EndH)
    (hCommScale :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorScalePart (E := E) hMod)) :
    relativeModularDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator
      =
    modularGaugeDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator := by
  simpa [relativeModularDeriv] using
    modularDeriv_eq_modularGaugeDeriv_of_commute_scalePart
      (E := E) (hMod := hMod) (A := CCI.liftedEinsteinAnomalyOperator) hCommScale

/--
If both gauge and scaling sectors commute with the lifted singular Einstein
anomaly, its relative-modular transport is infinitesimally stationary.
-/
theorem liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_zero_of_commute_parts
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (hCommScale :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorScalePart (E := E) hMod)) :
    relativeModularDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator = 0 := by
  simpa [relativeModularDeriv] using
    modularDeriv_eq_zero_of_commute_parts
      (E := E) (hMod := hMod) (A := CCI.liftedEinsteinAnomalyOperator) hCommGauge hCommScale

/--
If the full relative-modular generator commutes with the lifted singular
Einstein anomaly, the anomaly transport is infinitesimally stationary.
-/
theorem liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_zero_of_commute_generator
    (hMod : EndH)
    (hComm :
      Commute CCI.liftedEinsteinAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    relativeModularDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator = 0 := by
  exact relativeModularDeriv_eq_zero_of_commute_generator
    (E := E) hMod CCI.liftedEinsteinAnomalyOperator hComm

/--
If an operator commutes with the relative-modular generator, exact exponential
conjugation transport fixes that operator.
-/
private theorem expTransport_eq_self_of_commute_relativeModularKGenerator
    (A hMod : EndH) (t : ℝ)
    (hComm :
      Commute A (relativeModularKGenerator (E := E) hMod)) :
    InfoGeometry.Canonical.expTransport
      (A := EndH)
      (relativeModularKGenerator (E := E) hMod)
      A
      t
      =
    A := by
  let X : EndH := relativeModularKGenerator (E := E) hMod
  have hCommScaled : Commute A (t • X) := by
    simpa [X] using hComm.smul_right t
  have hCommExp : Commute A (NormedSpace.exp (t • X)) := by
    simpa using hCommScaled.exp_right
  have hScaledNeg : Commute (t • X) (t • (-X)) := by
    rw [smul_neg]
    exact (Commute.refl (t • X)).neg_right
  unfold InfoGeometry.Canonical.expTransport
  calc
    (NormedSpace.exp (t • X) * A) * NormedSpace.exp (t • (-X))
      =
    (A * NormedSpace.exp (t • X)) * NormedSpace.exp (t • (-X)) := by
          rw [hCommExp.eq]
    _ = A * (NormedSpace.exp (t • X) * NormedSpace.exp (t • (-X))) := by
          rw [mul_assoc]
    _ = A * NormedSpace.exp (t • X + t • (-X)) := by
          rw [← NormedSpace.exp_add_of_commute hScaledNeg]
    _ = A * 1 := by
          simp
    _ = A := by
          simp

/--
Bogoliubov conjugation of the lifted left chiral anomaly operator by the
relative-modular `K`-generator flow.
-/
noncomputable def bogoliubovConjugate_liftedLeftChiralAnomalyOperator
    (hMod : EndH) (t : ℝ) : EndH :=
  InfoGeometry.Canonical.expTransport
    (A := EndH)
    (relativeModularKGenerator (E := E) hMod)
    CCI.liftedLeftChiralAnomalyOperator
    t

/--
Bogoliubov conjugation of the lifted right chiral anomaly operator by the
relative-modular `K`-generator flow.
-/
noncomputable def bogoliubovConjugate_liftedRightChiralAnomalyOperator
    (hMod : EndH) (t : ℝ) : EndH :=
  InfoGeometry.Canonical.expTransport
    (A := EndH)
    (relativeModularKGenerator (E := E) hMod)
    CCI.liftedRightChiralAnomalyOperator
    t

/--
Explicit `U χ_L U⁻¹` form for Bogoliubov conjugation of the lifted left chiral
anomaly operator, with `U = exp(tX)` and `X = relativeModularKGenerator`.
-/
theorem bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_exp_mul_mul_exp_neg
    (hMod : EndH) (t : ℝ) :
    CCI.bogoliubovConjugate_liftedLeftChiralAnomalyOperator hMod t
      =
    (NormedSpace.exp (t • relativeModularKGenerator (E := E) hMod) *
        CCI.liftedLeftChiralAnomalyOperator) *
      NormedSpace.exp (t • (-(relativeModularKGenerator (E := E) hMod))) := by
  rfl

/--
Explicit `U χ_R U⁻¹` form for Bogoliubov conjugation of the lifted right chiral
anomaly operator, with `U = exp(tX)` and `X = relativeModularKGenerator`.
-/
theorem bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_exp_mul_mul_exp_neg
    (hMod : EndH) (t : ℝ) :
    CCI.bogoliubovConjugate_liftedRightChiralAnomalyOperator hMod t
      =
    (NormedSpace.exp (t • relativeModularKGenerator (E := E) hMod) *
        CCI.liftedRightChiralAnomalyOperator) *
      NormedSpace.exp (t • (-(relativeModularKGenerator (E := E) hMod))) := by
  rfl

/--
In the commuting-generator regime, Bogoliubov conjugation fixes the lifted left
chiral anomaly operator.
-/
theorem bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_self_of_commute_generator
    (hMod : EndH) (t : ℝ)
    (hComm :
      Commute CCI.liftedLeftChiralAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    CCI.bogoliubovConjugate_liftedLeftChiralAnomalyOperator hMod t
      =
    CCI.liftedLeftChiralAnomalyOperator := by
  simpa [bogoliubovConjugate_liftedLeftChiralAnomalyOperator] using
    expTransport_eq_self_of_commute_relativeModularKGenerator
      (E := E) (A := CCI.liftedLeftChiralAnomalyOperator) hMod t hComm

/--
In the commuting-generator regime, Bogoliubov conjugation fixes the lifted
right chiral anomaly operator.
-/
theorem bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_self_of_commute_generator
    (hMod : EndH) (t : ℝ)
    (hComm :
      Commute CCI.liftedRightChiralAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    CCI.bogoliubovConjugate_liftedRightChiralAnomalyOperator hMod t
      =
    CCI.liftedRightChiralAnomalyOperator := by
  simpa [bogoliubovConjugate_liftedRightChiralAnomalyOperator] using
    expTransport_eq_self_of_commute_relativeModularKGenerator
      (E := E) (A := CCI.liftedRightChiralAnomalyOperator) hMod t hComm

/--
In the commuting-generator regime, vanishing of the lifted left chiral anomaly
operator is invariant under Bogoliubov conjugation.
-/
theorem bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_zero_iff_of_commute_generator
    (hMod : EndH) (t : ℝ)
    (hComm :
      Commute CCI.liftedLeftChiralAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    CCI.bogoliubovConjugate_liftedLeftChiralAnomalyOperator hMod t = 0
      ↔
    CCI.liftedLeftChiralAnomalyOperator = 0 := by
  constructor
  · intro hZero
    simpa [CCI.bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_self_of_commute_generator
      hMod t hComm] using hZero
  · intro hZero
    simpa [CCI.bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_self_of_commute_generator
      hMod t hComm] using hZero

/--
In the commuting-generator regime, vanishing of the lifted right chiral anomaly
operator is invariant under Bogoliubov conjugation.
-/
theorem bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_zero_iff_of_commute_generator
    (hMod : EndH) (t : ℝ)
    (hComm :
      Commute CCI.liftedRightChiralAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    CCI.bogoliubovConjugate_liftedRightChiralAnomalyOperator hMod t = 0
      ↔
    CCI.liftedRightChiralAnomalyOperator = 0 := by
  constructor
  · intro hZero
    simpa [CCI.bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_self_of_commute_generator
      hMod t hComm] using hZero
  · intro hZero
    simpa [CCI.bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_self_of_commute_generator
      hMod t hComm] using hZero

/--
In the commuting-generator regime, non-vanishing of the lifted left chiral
anomaly operator is invariant under Bogoliubov conjugation.
-/
theorem bogoliubovConjugate_liftedLeftChiralAnomalyOperator_ne_zero_iff_of_commute_generator
    (hMod : EndH) (t : ℝ)
    (hComm :
      Commute CCI.liftedLeftChiralAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    CCI.bogoliubovConjugate_liftedLeftChiralAnomalyOperator hMod t ≠ 0
      ↔
    CCI.liftedLeftChiralAnomalyOperator ≠ 0 := by
  simpa using not_congr
    (CCI.bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_zero_iff_of_commute_generator
      hMod t hComm)

/--
In the commuting-generator regime, non-vanishing of the lifted right chiral
anomaly operator is invariant under Bogoliubov conjugation.
-/
theorem bogoliubovConjugate_liftedRightChiralAnomalyOperator_ne_zero_iff_of_commute_generator
    (hMod : EndH) (t : ℝ)
    (hComm :
      Commute CCI.liftedRightChiralAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    CCI.bogoliubovConjugate_liftedRightChiralAnomalyOperator hMod t ≠ 0
      ↔
    CCI.liftedRightChiralAnomalyOperator ≠ 0 := by
  simpa using not_congr
    (CCI.bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_zero_iff_of_commute_generator
      hMod t hComm)

/--
Bogoliubov conjugation of the lifted Einstein anomaly operator by the
relative-modular `K`-generator flow.
-/
noncomputable def bogoliubovConjugate_liftedEinsteinAnomalyOperator
    (hMod : EndH) (t : ℝ) : EndH :=
  InfoGeometry.Canonical.expTransport
    (A := EndH)
    (relativeModularKGenerator (E := E) hMod)
    CCI.liftedEinsteinAnomalyOperator
    t

/--
Explicit `U χ U⁻¹` form for Bogoliubov conjugation of the lifted Einstein
anomaly operator, with `U = exp(tX)` and `X = relativeModularKGenerator`.
-/
theorem bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_exp_mul_mul_exp_neg
    (hMod : EndH) (t : ℝ) :
    CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator hMod t
      =
    (NormedSpace.exp (t • relativeModularKGenerator (E := E) hMod) *
        CCI.liftedEinsteinAnomalyOperator) *
      NormedSpace.exp (t • (-(relativeModularKGenerator (E := E) hMod))) := by
  rfl

/--
Infinitesimal Bogoliubov transport of the lifted singular Einstein anomaly is
exactly the relative-modular derivation channel.
-/
theorem deriv_bogoliubovConjugate_liftedEinsteinAnomalyOperator_at_zero_eq_relativeModularDeriv
    (hMod : EndH) :
    deriv
      (fun t => CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator hMod t)
      0
      =
    relativeModularDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator := by
  simpa [bogoliubovConjugate_liftedEinsteinAnomalyOperator, relativeModularDeriv] using
    deriv_modularTransport_conjugation_at_zero
      (E := E) hMod CCI.liftedEinsteinAnomalyOperator

/--
If the gauge sector commutes with the lifted singular Einstein anomaly, its
infinitesimal Bogoliubov transport is carried entirely by the source channel.
-/
theorem deriv_bogoliubovConjugate_liftedEinsteinAnomalyOperator_at_zero_eq_relativeModularSourceDeriv_of_commute_gaugePart
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod)) :
    deriv
      (fun t => CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator hMod t)
      0
      =
    relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator := by
  rw [deriv_bogoliubovConjugate_liftedEinsteinAnomalyOperator_at_zero_eq_relativeModularDeriv
    (CCI := CCI) hMod]
  exact CCI.liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_relativeModularSourceDeriv_of_commute_gaugePart
    hMod hCommGauge

/--
If the lifted singular Einstein anomaly commutes with the full relative-modular
generator, its infinitesimal Bogoliubov transport vanishes at `t = 0`.
-/
theorem deriv_bogoliubovConjugate_liftedEinsteinAnomalyOperator_at_zero_eq_zero_of_commute_generator
    (hMod : EndH)
    (hComm :
      Commute CCI.liftedEinsteinAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    deriv
      (fun t => CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator hMod t)
      0
      =
    0 := by
  rw [deriv_bogoliubovConjugate_liftedEinsteinAnomalyOperator_at_zero_eq_relativeModularDeriv
    (CCI := CCI) hMod]
  exact CCI.liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_zero_of_commute_generator
    hMod hComm

/--
If the lifted singular Einstein anomaly commutes with the relative-modular
generator, then exact exponential conjugation transport fixes it.
-/
theorem expTransport_liftedEinsteinAnomalyOperator_eq_self_of_commute_generator
    (hMod : EndH) (t : ℝ)
    (hComm :
      Commute CCI.liftedEinsteinAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    InfoGeometry.Canonical.expTransport
      (A := EndH)
      (relativeModularKGenerator (E := E) hMod)
      CCI.liftedEinsteinAnomalyOperator
      t
      =
    CCI.liftedEinsteinAnomalyOperator := by
  let X : EndH := relativeModularKGenerator (E := E) hMod
  have hCommScaled :
      Commute CCI.liftedEinsteinAnomalyOperator (t • X) := by
    simpa [X] using hComm.smul_right t
  have hCommExp :
      Commute CCI.liftedEinsteinAnomalyOperator (NormedSpace.exp (t • X)) := by
    simpa using hCommScaled.exp_right
  have hScaledNeg : Commute (t • X) (t • (-X)) := by
    rw [smul_neg]
    exact (Commute.refl (t • X)).neg_right
  unfold InfoGeometry.Canonical.expTransport
  calc
    (NormedSpace.exp (t • X) * CCI.liftedEinsteinAnomalyOperator) *
        NormedSpace.exp (t • (-X))
      =
    (CCI.liftedEinsteinAnomalyOperator * NormedSpace.exp (t • X)) *
        NormedSpace.exp (t • (-X)) := by
          rw [hCommExp.eq]
    _ =
    CCI.liftedEinsteinAnomalyOperator *
        (NormedSpace.exp (t • X) * NormedSpace.exp (t • (-X))) := by
          rw [mul_assoc]
    _ =
    CCI.liftedEinsteinAnomalyOperator *
        NormedSpace.exp (t • X + t • (-X)) := by
          rw [← NormedSpace.exp_add_of_commute hScaledNeg]
    _ = CCI.liftedEinsteinAnomalyOperator * 1 := by
          simp
    _ = CCI.liftedEinsteinAnomalyOperator := by
          simp

/--
In the commuting-generator regime, Bogoliubov conjugation fixes the lifted
Einstein anomaly operator.
-/
theorem bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_self_of_commute_generator
    (hMod : EndH) (t : ℝ)
    (hComm :
      Commute CCI.liftedEinsteinAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator hMod t
      =
    CCI.liftedEinsteinAnomalyOperator := by
  simpa [bogoliubovConjugate_liftedEinsteinAnomalyOperator] using
    CCI.expTransport_liftedEinsteinAnomalyOperator_eq_self_of_commute_generator hMod t hComm

/--
In the commuting-generator regime, vanishing of the lifted Einstein anomaly is
invariant under Bogoliubov conjugation.
-/
theorem bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_zero_iff_of_commute_generator
    (hMod : EndH) (t : ℝ)
    (hComm :
      Commute CCI.liftedEinsteinAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator hMod t = 0
      ↔
    CCI.liftedEinsteinAnomalyOperator = 0 := by
  constructor
  · intro hZero
    simpa [CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_self_of_commute_generator
      hMod t hComm] using hZero
  · intro hZero
    simpa [CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_self_of_commute_generator
      hMod t hComm] using hZero

/--
In the commuting-generator regime, non-vanishing of the lifted Einstein anomaly
is invariant under Bogoliubov conjugation.
-/
theorem bogoliubovConjugate_liftedEinsteinAnomalyOperator_ne_zero_iff_of_commute_generator
    (hMod : EndH) (t : ℝ)
    (hComm :
      Commute CCI.liftedEinsteinAnomalyOperator
        (relativeModularKGenerator (E := E) hMod)) :
    CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator hMod t ≠ 0
      ↔
    CCI.liftedEinsteinAnomalyOperator ≠ 0 := by
  simpa using not_congr
    (CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_zero_iff_of_commute_generator
      hMod t hComm)

end CertifiedConformalInference

namespace StarCertifiedConformalInference

variable (SCI : StarCertifiedConformalInference E)

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Star-property lifted left anomaly operator on the doubled carrier. -/
noncomputable abbrev liftedLeftChiralAnomalyOperator : EndH :=
  SCI.toCertifiedConformalInference.liftedLeftChiralAnomalyOperator

/-- Star-property lifted right anomaly operator on the doubled carrier. -/
noncomputable abbrev liftedRightChiralAnomalyOperator : EndH :=
  SCI.toCertifiedConformalInference.liftedRightChiralAnomalyOperator

/-- Star-property lifted singular Einstein anomaly operator on the doubled carrier. -/
noncomputable abbrev liftedEinsteinAnomalyOperator : EndH :=
  SCI.toCertifiedConformalInference.liftedEinsteinAnomalyOperator

/--
On the star-property conformal surface, the lifted singular Einstein anomaly
is exactly the negative of the lifted right-projector anomaly.
-/
theorem liftedEinsteinAnomalyOperator_eq_neg_liftedRightChiralAnomalyOperator :
    SCI.liftedEinsteinAnomalyOperator = -SCI.liftedRightChiralAnomalyOperator := by
  simpa [StarCertifiedConformalInference.liftedEinsteinAnomalyOperator,
    StarCertifiedConformalInference.liftedRightChiralAnomalyOperator] using
      SCI.toCertifiedConformalInference.liftedEinsteinAnomalyOperator_eq_neg_liftedRightChiralAnomalyOperator

/--
On the star-property conformal surface, the lifted singular Einstein anomaly
commutes with the doubled-space phase axis `K = Jε`.
-/
theorem liftedEinsteinAnomalyOperator_isPhaseLinear :
    IsPhaseLinear (E := E) SCI.liftedEinsteinAnomalyOperator := by
  simpa [StarCertifiedConformalInference.liftedEinsteinAnomalyOperator] using
    SCI.toCertifiedConformalInference.liftedEinsteinAnomalyOperator_isPhaseLinear

/--
The lifted left-projector anomaly operator is skew-adjoint on the doubled
carrier under star-property conformal data.
-/
theorem liftedLeftChiralAnomalyOperator_star_eq_neg :
    star SCI.liftedLeftChiralAnomalyOperator = -SCI.liftedLeftChiralAnomalyOperator := by
  have hBase :
      star SCI.leftChiralAnomalyOperator = -SCI.leftChiralAnomalyOperator :=
    SCI.leftChiralAnomalyOperator_star_eq_neg
  have hLift :
      dualSheetLift (E := E) (star SCI.leftChiralAnomalyOperator)
        =
      dualSheetLift (E := E) (-SCI.leftChiralAnomalyOperator) :=
    congrArg (fun T : E →L[ℝ] E => dualSheetLift (E := E) T) hBase
  have hStarLift :
      star (dualSheetLift (E := E) SCI.leftChiralAnomalyOperator)
        =
      dualSheetLift (E := E) (star SCI.leftChiralAnomalyOperator) :=
    dualSheetLift_star (E := E) SCI.leftChiralAnomalyOperator
  have hNegLift :
      dualSheetLift (E := E) (-SCI.leftChiralAnomalyOperator)
        =
      -(dualSheetLift (E := E) SCI.leftChiralAnomalyOperator) := by
    exact dualSheetLift_neg (E := E) SCI.leftChiralAnomalyOperator
  calc
    star SCI.liftedLeftChiralAnomalyOperator
        = star (dualSheetLift (E := E) SCI.leftChiralAnomalyOperator) := rfl
    _ = dualSheetLift (E := E) (star SCI.leftChiralAnomalyOperator) := hStarLift
    _ = dualSheetLift (E := E) (-SCI.leftChiralAnomalyOperator) := hLift
    _ = -(dualSheetLift (E := E) SCI.leftChiralAnomalyOperator) := hNegLift
    _ = -SCI.liftedLeftChiralAnomalyOperator := rfl

/--
The lifted right-projector anomaly operator is skew-adjoint on the doubled
carrier under star-property conformal data.
-/
theorem liftedRightChiralAnomalyOperator_star_eq_neg :
    star SCI.liftedRightChiralAnomalyOperator = -SCI.liftedRightChiralAnomalyOperator := by
  have hBase :
      star SCI.rightChiralAnomalyOperator = -SCI.rightChiralAnomalyOperator :=
    SCI.rightChiralAnomalyOperator_star_eq_neg
  have hLift :
      dualSheetLift (E := E) (star SCI.rightChiralAnomalyOperator)
        =
      dualSheetLift (E := E) (-SCI.rightChiralAnomalyOperator) :=
    congrArg (fun T : E →L[ℝ] E => dualSheetLift (E := E) T) hBase
  calc
    star SCI.liftedRightChiralAnomalyOperator
        =
      dualSheetLift (E := E) (star SCI.rightChiralAnomalyOperator) := by
          change
            star (dualSheetLift (E := E) SCI.rightChiralAnomalyOperator)
              =
            dualSheetLift (E := E) (star SCI.rightChiralAnomalyOperator)
          exact dualSheetLift_star (E := E) SCI.rightChiralAnomalyOperator
    _ = dualSheetLift (E := E) (-SCI.rightChiralAnomalyOperator) := hLift
    _ = -SCI.liftedRightChiralAnomalyOperator := by
          change
            dualSheetLift (E := E) (-SCI.rightChiralAnomalyOperator)
              =
            -(dualSheetLift (E := E) SCI.rightChiralAnomalyOperator)
          exact dualSheetLift_neg (E := E) SCI.rightChiralAnomalyOperator

/--
The lifted singular Einstein anomaly operator is skew-adjoint on the doubled
carrier under star-property conformal data.
-/
theorem liftedEinsteinAnomalyOperator_star_eq_neg :
    star SCI.liftedEinsteinAnomalyOperator = -SCI.liftedEinsteinAnomalyOperator := by
  calc
    star SCI.liftedEinsteinAnomalyOperator
        = star (-SCI.liftedRightChiralAnomalyOperator) := by
            rw [SCI.liftedEinsteinAnomalyOperator_eq_neg_liftedRightChiralAnomalyOperator]
    _ = -star SCI.liftedRightChiralAnomalyOperator := by
            simp
    _ = -(-SCI.liftedRightChiralAnomalyOperator) := by
            rw [SCI.liftedRightChiralAnomalyOperator_star_eq_neg]
    _ = SCI.liftedRightChiralAnomalyOperator := by
            simp
    _ = -SCI.liftedEinsteinAnomalyOperator := by
            rw [SCI.liftedEinsteinAnomalyOperator_eq_neg_liftedRightChiralAnomalyOperator]
            simp

end StarCertifiedConformalInference

end InfoGeometry.Canonical.ConformalUnification
