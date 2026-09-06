import proofs.BogoliubovWeylChemicalPotential
import proofs.InformationGeometricCutoff
import proofs.AffineDynkinGoutevTonev

/-!
# Cramér--Rao phase-volume rescaling to canonical commutators

This file records finite algebraic rescaling data:

* the Bogoliubov/Weyl gauge gives a log-clock scale;
* Cramér--Rao data gives a positive phase-volume/action
  pixel `κ = I⁻¹`;
* after a canonical calibration/rescaling, an unmixed inertial phase-space pair
  has commutator `[X,P] = i κ 1`;
* the finite `M₂(ℂ)` Weyl cell remains trace-obstructed from exact CCR.
-/

noncomputable section

namespace RescaledPhaseVolumeCanonical

open InformationGeometricCutoff
open BogoliubovWeylChemicalPotential
open SupergradedCuntzBdG
open HestenesCuntzPhaseSpace

/-- Generic commutator in a noncommutative algebra. -/
def commA {A : Type*} [Ring A] (X P : A) : A := X * P - P * X

/-- Scalar rescaling of an unmixed pair rescales its commutator by the product of
coordinate and momentum scales. -/
theorem commA_rescale {A : Type*} [Ring A] [Algebra ℂ A]
    (sx sp : ℂ) (X P : A) :
    commA (sx • X) (sp • P) = (sx * sp) • commA X P := by
  simp [commA, smul_sub, smul_smul, mul_comm]

/-- Cramér--Rao phase-volume data: Fisher information is positive and its
reciprocal is no larger than the phase-space variance. -/
structure CramerRaoData where
  phaseSpaceVariance : ℝ
  fisherInformation : ℝ
  fisher_pos : 0 < fisherInformation
  fisher_inverse_le_variance : fisherInformation⁻¹ ≤ phaseSpaceVariance

/-- The Cramér--Rao phase-volume/action pixel as a real scalar. -/
def cramerRaoPhaseAction (cr : CramerRaoData) : ℝ :=
  cr.fisherInformation⁻¹

/-- The same Cramér--Rao phase-volume/action pixel as a complex scalar. -/
def cramerRaoPhaseActionC (cr : CramerRaoData) : ℂ :=
  (cramerRaoPhaseAction cr : ℂ)

/-- The Cramér--Rao phase action is strictly positive. -/
theorem cramerRaoPhaseAction_pos (cr : CramerRaoData) :
    0 < cramerRaoPhaseAction cr := by
  exact inv_pos.mpr cr.fisher_pos

/-- The Cramér--Rao action pixel is nonzero over `ℂ`. -/
theorem cramerRaoPhaseActionC_ne_zero (cr : CramerRaoData) :
    cramerRaoPhaseActionC cr ≠ 0 := by
  unfold cramerRaoPhaseActionC
  exact_mod_cast (ne_of_gt (cramerRaoPhaseAction_pos cr))

/-- The Cramér--Rao variance is positive. -/
theorem cramerRao_phaseSpaceVariance_pos (cr : CramerRaoData) :
    0 < cr.phaseSpaceVariance := by
  exact lt_of_lt_of_le (cramerRaoPhaseAction_pos cr) cr.fisher_inverse_le_variance

/-- Canonical phase rescaling data for an inertial/Bogoliubov frame. -/
structure CanonicalPhaseRescaling (A : Type*) [Ring A] [Algebra ℂ A]
    (cr : CramerRaoData) where
  rawCoordinate : A
  rawMomentum : A
  rawAction : ℂ
  coordinateScale : ℂ
  momentumScale : ℂ
  raw_commutator : commA rawCoordinate rawMomentum = rawAction • (1 : A)
  scale_calibration : coordinateScale * momentumScale * rawAction =
    Complex.I * cramerRaoPhaseActionC cr

/-- Rescaled coordinate. -/
def rescaledCoordinate {A : Type*} [Ring A] [Algebra ℂ A]
    {cr : CramerRaoData} (C : CanonicalPhaseRescaling A cr) : A :=
  C.coordinateScale • C.rawCoordinate

/-- Rescaled momentum. -/
def rescaledMomentum {A : Type*} [Ring A] [Algebra ℂ A]
    {cr : CramerRaoData} (C : CanonicalPhaseRescaling A cr) : A :=
  C.momentumScale • C.rawMomentum

/-- The calibrated rescaling gives the canonical commutator with action quantum
fixed by the Cramér--Rao phase-volume pixel. -/
theorem rescaled_canonical_commutator {A : Type*} [Ring A] [Algebra ℂ A]
    {cr : CramerRaoData} (C : CanonicalPhaseRescaling A cr) :
    commA (rescaledCoordinate C) (rescaledMomentum C) =
      (Complex.I * cramerRaoPhaseActionC cr) • (1 : A) := by
  unfold rescaledCoordinate rescaledMomentum
  rw [commA_rescale]
  rw [C.raw_commutator]
  simp [smul_smul, C.scale_calibration]

/-- The Bogoliubov/Weyl frame scales the Cramér--Rao action pixel by its q-gauge. -/
def framePhaseActionGauge (cr : CramerRaoData)
    (F : BogoliubovInertialFrame) : ℂ :=
  frameWeylQ F * cramerRaoPhaseActionC cr

/-- The frame phase-action gauge is nonzero: the q-clock is nonzero and the
Cramér--Rao pixel is nonzero. -/
theorem framePhaseActionGauge_ne_zero (cr : CramerRaoData)
    (F : BogoliubovInertialFrame) :
    framePhaseActionGauge cr F ≠ 0 := by
  exact mul_ne_zero (frameWeylQ_ne_zero F) (cramerRaoPhaseActionC_ne_zero cr)

/-- Chemical potential shifts the log-clock, hence shifts the phase-action gauge
at q-level by the corresponding exponential rapidity. -/
theorem framePhaseActionGauge_mu_shift (cr : CramerRaoData)
    (F : BogoliubovInertialFrame) (δμ : ℝ) :
    framePhaseActionGauge cr { F with μ := F.μ + δμ } =
      qRapidity (F.β * δμ * F.Q) * framePhaseActionGauge cr F := by
  unfold framePhaseActionGauge
  rw [frameWeylQ_eq_qRapidity_logClock]
  rw [frameWeylQ_eq_qRapidity_logClock]
  rw [frameWeylLogClock_mu_shift]
  rw [qRapidity_add]
  ring

/-- The finite `M₂(ℂ)` phase cell remains Weyl; calibrated rescaling gives the
target commutator for the supplied algebraic pair. -/
theorem finite_weyl_plus_abstract_rescaled_canonical
    (cr : CramerRaoData)
    {A : Type*} [Ring A] [Algebra ℂ A]
    (C : CanonicalPhaseRescaling A cr) :
    twoCellWeylPair.momentum * twoCellWeylPair.coordinate =
      twoCellWeylPair.q • (twoCellWeylPair.coordinate * twoCellWeylPair.momentum) ∧
    (¬ ∃ X P : M2C, commM X P = Complex.I • (1 : M2C)) ∧
    commA (rescaledCoordinate C) (rescaledMomentum C) =
      (Complex.I * cramerRaoPhaseActionC cr) • (1 : A) := by
  refine And.intro ?weyl ?rest
  · exact twoCellWeylPair.weyl_relation
  · refine And.intro ?noFinite ?canonical
    · exact no_finite_m2_canonical_ccr
    · exact rescaled_canonical_commutator C

end RescaledPhaseVolumeCanonical

end noncomputable section
