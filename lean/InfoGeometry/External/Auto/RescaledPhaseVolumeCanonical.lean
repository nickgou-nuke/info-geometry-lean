import InfoGeometry.Physics.BogoliubovWeylChemicalPotential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.InformationGeometricCutoff

/-!
# Cramér–Rao phase-action rescaling

This module proves the algebraic rescaling statement behind a proposed
canonical phase-volume calibration.  It also reuses the existing finite Weyl
pair and finite-dimensional obstruction to exact CCR.

The rescaling theorem transports an explicit raw-commutator hypothesis through
an explicit scalar calibration.
-/

noncomputable section

namespace RescaledPhaseVolumeCanonical

open InformationGeometricCutoff
open InfoGeometry.Physics.BogoliubovWeylChemicalPotential
open InfoGeometry.Physics.SupergradedCuntzBdG
open InfoGeometry.Physics.HestenesCuntzPhaseSpace

/-- Generic commutator in a ring. -/
def commA {A : Type*} [Ring A] (X P : A) : A := X * P - P * X

/-- Scalar rescaling multiplies a commutator by the product of the two scales. -/
theorem commA_rescale {A : Type*} [Ring A] [Algebra ℂ A]
    (sx sp : ℂ) (X P : A) :
    commA (sx • X) (sp • P) = (sx * sp) • commA X P := by
  simp [commA, smul_sub, smul_smul, mul_comm]

/-- Cramér–Rao minimal phase-space volume, regarded as an action scale. -/
def cramerRaoPhaseAction (cr : CramerRaoQuantumInequality) : ℝ :=
  MinimalPhaseSpaceVolume cr

/-- Complex form of the Cramér–Rao action scale. -/
def cramerRaoPhaseActionC (cr : CramerRaoQuantumInequality) : ℂ :=
  cramerRaoPhaseAction cr

/-- The Cramér–Rao action scale is positive. -/
theorem cramerRaoPhaseAction_pos (cr : CramerRaoQuantumInequality) :
    0 < cramerRaoPhaseAction cr :=
  minimal_phase_space_volume_pos cr

/-- The complex action scale is nonzero. -/
theorem cramerRaoPhaseActionC_ne_zero (cr : CramerRaoQuantumInequality) :
    cramerRaoPhaseActionC cr ≠ 0 := by
  unfold cramerRaoPhaseActionC
  exact_mod_cast ne_of_gt (cramerRaoPhaseAction_pos cr)

/-- Explicitly calibrated scalar rescaling of a supplied raw commutator.  This
is a conditional algebraic theorem, not an existence certificate for CCR. -/
theorem rescaled_canonical_commutator
    {A : Type*} [Ring A] [Algebra ℂ A]
    (cr : CramerRaoQuantumInequality)
    (X P : A) (rawAction sx sp : ℂ)
    (hraw : commA X P = rawAction • (1 : A))
    (hscale : sx * sp * rawAction = Complex.I * cramerRaoPhaseActionC cr) :
    commA (sx • X) (sp • P) =
      (Complex.I * cramerRaoPhaseActionC cr) • (1 : A) := by
  rw [commA_rescale, hraw]
  simp [smul_smul, hscale]

/-- Bogoliubov/Weyl q-gauge applied to the Cramér–Rao action scale. -/
def framePhaseActionGauge (cr : CramerRaoQuantumInequality)
    (F : BogoliubovInertialFrame) : ℂ :=
  frameWeylQ F * cramerRaoPhaseActionC cr

/-- The frame-scaled action is nonzero. -/
theorem framePhaseActionGauge_ne_zero (cr : CramerRaoQuantumInequality)
    (F : BogoliubovInertialFrame) :
    framePhaseActionGauge cr F ≠ 0 :=
  mul_ne_zero (frameWeylQ_ne_zero F) (cramerRaoPhaseActionC_ne_zero cr)

/-- Chemical-potential shift law for the frame-scaled action. -/
theorem framePhaseActionGauge_mu_shift (cr : CramerRaoQuantumInequality)
    (F : BogoliubovInertialFrame) (δμ : ℝ) :
    framePhaseActionGauge cr { F with μ := F.μ + δμ } =
      qRapidity (F.β * δμ * F.Q) * framePhaseActionGauge cr F := by
  unfold framePhaseActionGauge
  rw [frameWeylQ_eq_qRapidity_logClock]
  rw [frameWeylQ_eq_qRapidity_logClock]
  rw [frameWeylLogClock_mu_shift, qRapidity_add]
  ring

/-- The concrete finite Weyl pair coexists with the finite `M₂(ℂ)` obstruction;
a separately supplied calibrated raw pair satisfies the conditional rescaled
commutator. -/
theorem finite_weyl_plus_abstract_rescaled_canonical
    (cr : CramerRaoQuantumInequality)
    {A : Type*} [Ring A] [Algebra ℂ A]
    (X P : A) (rawAction sx sp : ℂ)
    (hraw : commA X P = rawAction • (1 : A))
    (hscale : sx * sp * rawAction = Complex.I * cramerRaoPhaseActionC cr) :
    twoCellWeylPair.momentum * twoCellWeylPair.coordinate =
      twoCellWeylPair.q • (twoCellWeylPair.coordinate * twoCellWeylPair.momentum) ∧
    (¬ ∃ X P : M2C, commM X P = Complex.I • (1 : M2C)) ∧
    commA (sx • X) (sp • P) =
      (Complex.I * cramerRaoPhaseActionC cr) • (1 : A) :=
  ⟨twoCellWeylPair.weyl_relation,
    no_finite_m2_canonical_ccr,
    rescaled_canonical_commutator cr X P rawAction sx sp hraw hscale⟩

/-- Synthesis of the native positivity, frame gauge, and algebraic rescaling results. -/
theorem rescaled_phase_volume_canonical_synthesis
    (cr : CramerRaoQuantumInequality) (F : BogoliubovInertialFrame)
    {A : Type*} [Ring A] [Algebra ℂ A]
    (X P : A) (rawAction sx sp : ℂ)
    (hraw : commA X P = rawAction • (1 : A))
    (hscale : sx * sp * rawAction = Complex.I * cramerRaoPhaseActionC cr) :
    0 < cramerRaoPhaseAction cr ∧
    frameWeylQ F = qRapidity (frameWeylLogClock F) ∧
    framePhaseActionGauge cr F ≠ 0 ∧
    commA (sx • X) (sp • P) =
      (Complex.I * cramerRaoPhaseActionC cr) • (1 : A) :=
  ⟨cramerRaoPhaseAction_pos cr,
    frameWeylQ_eq_qRapidity_logClock F,
    framePhaseActionGauge_ne_zero cr F,
    rescaled_canonical_commutator cr X P rawAction sx sp hraw hscale⟩

end RescaledPhaseVolumeCanonical

end noncomputable section
