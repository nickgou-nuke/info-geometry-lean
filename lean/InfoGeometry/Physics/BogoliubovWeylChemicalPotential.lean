import InfoGeometry.Physics.HestenesCuntzPhaseSpace

/-!
# Bogoliubov inertial frames, Weyl gauge, and chemical-potential log clock

This file records the finite algebraic bridge suggested by the phase-space
picture:

* a Bogoliubov/inertial frame is represented by an extra real rapidity/log-clock
  parameter `θ` applied to the grand-canonical Weyl weight;
* the grand-canonical rapidity is `-β(E - μ Q)`;
* changing chemical potential shifts the Weyl log-clock by `β δμ Q`;
* the Cuntz/BdG affine bracket uses precisely the corresponding q-weight;
* the finite coordinate--momentum sector remains the Weyl pair, while exact CCR
  is kept outside the finite matrix statement because of the trace obstruction.
-/

noncomputable section

namespace InfoGeometry.Physics.BogoliubovWeylChemicalPotential

open SupergradedCuntzBdG
open HestenesCuntzPhaseSpace

/-- A finite Bogoliubov/inertial thermodynamic frame: `θ` is the extra
inertial/Bogoliubov log-clock rapidity, while `(β,E,μ,Q)` are the
grand-canonical thermodynamic parameters. -/
structure BogoliubovInertialFrame where
  θ : ℝ
  β : ℝ
  E : ℝ
  μ : ℝ
  Q : ℝ

/-- The grand-canonical log-clock/rapidity in a frame. -/
def frameGrandCanonicalRapidity (F : BogoliubovInertialFrame) : ℝ :=
  grandCanonicalRapidity F.β F.E F.μ F.Q

/-- The Bogoliubov/Weyl log-clock after applying the inertial rapidity `θ`. -/
def frameWeylLogClock (F : BogoliubovInertialFrame) : ℝ :=
  F.θ + frameGrandCanonicalRapidity F

/-- The corresponding positive real Weyl scale. -/
def frameWeylRealScale (F : BogoliubovInertialFrame) : ℝ :=
  boostedGrandCanonicalRealWeight F.θ F.β F.E F.μ F.Q

/-- The corresponding complex q-weight used by the Cuntz/BdG affine bracket. -/
def frameWeylQ (F : BogoliubovInertialFrame) : ℂ :=
  boostedGrandCanonicalQ F.θ F.β F.E F.μ F.Q

/-- The log of the positive Weyl scale is the inertial rapidity plus the
grand-canonical rapidity. -/
theorem frame_logScale_eq_logClock (F : BogoliubovInertialFrame) :
    logScaleParam (frameWeylRealScale F) = frameWeylLogClock F := by
  cases F
  simp [frameWeylRealScale, frameWeylLogClock, frameGrandCanonicalRapidity,
    logScale_boostedGrandCanonicalRealWeight]

/-- The complex Weyl gauge is the exponential of the Bogoliubov log-clock. -/
theorem frameWeylQ_eq_qRapidity_logClock (F : BogoliubovInertialFrame) :
    frameWeylQ F = qRapidity (frameWeylLogClock F) := by
  cases F
  simp [frameWeylQ, frameWeylLogClock, frameGrandCanonicalRapidity,
    boostedGrandCanonicalQ_eq_qRapidity_add]

/-- The frame q-weight is nonzero, as required for a Weyl gauge. -/
theorem frameWeylQ_ne_zero (F : BogoliubovInertialFrame) : frameWeylQ F ≠ 0 := by
  rw [frameWeylQ_eq_qRapidity_logClock]
  exact qRapidity_ne_zero _

/-- Chemical-potential shifts translate the grand-canonical log-clock by
`β δμ Q`.  This is the algebraic statement that the gauge/Weyl clock scale is
chemical-potential controlled. -/
theorem grandCanonicalRapidity_mu_shift (β E μ Q δμ : ℝ) :
    grandCanonicalRapidity β E (μ + δμ) Q =
      grandCanonicalRapidity β E μ Q + β * δμ * Q := by
  simp [grandCanonicalRapidity]
  ring

/-- The same chemical-potential shift law in a Bogoliubov inertial frame. -/
theorem frameWeylLogClock_mu_shift (F : BogoliubovInertialFrame) (δμ : ℝ) :
    frameWeylLogClock { F with μ := F.μ + δμ } =
      frameWeylLogClock F + F.β * δμ * F.Q := by
  cases F
  simp [frameWeylLogClock, frameGrandCanonicalRapidity,
    grandCanonicalRapidity_mu_shift]
  ring

/-- Simultaneous inertial-rapidity and chemical-potential translation of the
Bogoliubov/Weyl log clock. -/
theorem frameWeylLogClock_theta_mu_shift
    (F : BogoliubovInertialFrame) (δθ δμ : ℝ) :
    frameWeylLogClock { F with θ := F.θ + δθ, μ := F.μ + δμ } =
      frameWeylLogClock F + δθ + F.β * δμ * F.Q := by
  cases F
  simp [frameWeylLogClock, frameGrandCanonicalRapidity,
    SupergradedCuntzBdG.grandCanonicalRapidity]
  ring

/-- Energy shifts translate the log-clock oppositely by `-β δE`. -/
theorem grandCanonicalRapidity_energy_shift (β E μ Q δE : ℝ) :
    grandCanonicalRapidity β (E + δE) μ Q =
      grandCanonicalRapidity β E μ Q - β * δE := by
  simp [grandCanonicalRapidity]
  ring

/-- Charge shifts translate the log-clock by `β μ δQ`. -/
theorem grandCanonicalRapidity_charge_shift (β E μ Q δQ : ℝ) :
    grandCanonicalRapidity β E μ (Q + δQ) =
      grandCanonicalRapidity β E μ Q + β * μ * δQ := by
  simp [grandCanonicalRapidity]
  ring

/-- The Cuntz/BdG grand-canonical odd--odd bracket uses the q-weight determined
by the Bogoliubov/Weyl log-clock. -/
theorem frame_grandCanonicalBracket_odd_odd {A : Type*} [Semiring A] [Algebra ℂ A]
    (F : BogoliubovInertialFrame) (x y : A) :
    grandCanonicalBracket F.β F.E F.μ F.Q Z2Parity.odd Z2Parity.odd x y =
      x * y + (2 * qRapidity (frameGrandCanonicalRapidity F) - 1) • (y * x) := by
  cases F
  simp [frameGrandCanonicalRapidity, grandCanonicalBracket_odd_odd, grandCanonicalQ]

/-- Adding a Bogoliubov inertial rapidity composes with KMS/grand-canonical
scaling by Weyl/Rindler flow. -/
theorem frame_kmsBoostFlow_eq_rindlerWeyl {A : Type*} [MulAction ℂ A]
    (F : BogoliubovInertialFrame) (x : A) :
    kmsBoostFlow F.θ F.β F.E F.μ F.Q x =
      RindlerWeylFlow F.θ (kmsScalarAction F.β F.E F.μ F.Q x) := by
  cases F
  exact kmsBoostFlow_eq_rapidity_after_kms _ _ _ _ _ x

/-- In the finite phase cell, the unmixed inertial coordinate--momentum sector is
the exact finite Weyl pair; exact CCR remains trace-obstructed. -/
theorem inertial_frame_finite_weyl_unmixed :
    twoCellWeylPair.momentum * twoCellWeylPair.coordinate =
      twoCellWeylPair.q • (twoCellWeylPair.coordinate * twoCellWeylPair.momentum) ∧
    ¬ ∃ X P : M2C, commM X P = Complex.I • (1 : M2C) := by
  exact ⟨twoCellWeylPair.weyl_relation, no_finite_m2_canonical_ccr⟩

/-- Consolidated bridge: Bogoliubov inertial log-clock, chemical potential, Weyl
q-gauge, and finite unmixed Weyl phase-space cell. -/
theorem bogoliubov_weyl_chemical_potential_synthesis
    (F : BogoliubovInertialFrame) (δμ : ℝ) :
    logScaleParam (frameWeylRealScale F) = frameWeylLogClock F ∧
    frameWeylQ F = qRapidity (frameWeylLogClock F) ∧
    frameWeylQ F ≠ 0 ∧
    frameWeylLogClock { F with μ := F.μ + δμ } =
      frameWeylLogClock F + F.β * δμ * F.Q ∧
    twoCellWeylPair.momentum * twoCellWeylPair.coordinate =
      twoCellWeylPair.q • (twoCellWeylPair.coordinate * twoCellWeylPair.momentum) ∧
    ¬ ∃ X P : M2C, commM X P = Complex.I • (1 : M2C) := by
  constructor
  · exact frame_logScale_eq_logClock F
  constructor
  · exact frameWeylQ_eq_qRapidity_logClock F
  constructor
  · exact frameWeylQ_ne_zero F
  constructor
  · exact frameWeylLogClock_mu_shift F δμ
  constructor
  · exact inertial_frame_finite_weyl_unmixed.1
  · exact inertial_frame_finite_weyl_unmixed.2

end InfoGeometry.Physics.BogoliubovWeylChemicalPotential

end noncomputable section
