import InfoGeometry.MassSpectrometry.PeakSpectrum
import InfoGeometry.MassSpectrometry.StochasticFragmentGrammar

/-!
# Experimental observation semantics

Measured m/z is not silently identified with neutral mass. The existing `Peak`
carrier is reused for both readouts, but conversion requires explicit charge,
ion-mass offset, and positivity. No physical constants, vendor conversion,
file parser, or calibration procedure are asserted here.
-/

namespace InfoGeometry.MassSpectrometry.ExperimentalObservation

/-- The unit tag is retained; no automatic NCE/voltage/eV conversion is defined. -/
inductive CollisionEnergyUnit
  | electronVolt
  | normalizedPercent
  | accelerationVolt
  | vendorSpecific (label : String)
  deriving DecidableEq, Repr

/-- Acquisition metadata retains signed charge and the original energy unit. -/
structure AcquisitionCondition where
  energyValue : ℝ
  energy_nonneg : 0 ≤ energyValue
  energyUnit : CollisionEnergyUnit
  precursorCharge : ℤ
  charge_ne_zero : precursorCharge ≠ 0
  activationMethod : String
  gas : String

/-- A lossy legacy view requires an explicitly supplied calibrated energy.
The original metadata must be retained alongside this view. -/
def AcquisitionCondition.toCollisionCondition
    (c : AcquisitionCondition) (calibratedEnergy : ℝ) : CollisionCondition where
  energy := calibratedEnergy
  charge := c.precursorCharge.natAbs
  gas := c.gas

@[simp] theorem legacy_energy (c : AcquisitionCondition) (E : ℝ) :
    (c.toCollisionCondition E).energy = E := rfl

@[simp] theorem legacy_charge_magnitude (c : AcquisitionCondition) (E : ℝ) :
    (c.toCollisionCondition E).charge = c.precursorCharge.natAbs := rfl

/-- Explicit convention `ion mass = neutral mass + ionMassOffset`.
The offset can include the chosen adduct/electron convention; it is supplied,
not inferred from an integer isotope label or a library name. -/
structure IonInterpretation where
  charge : ℤ
  charge_ne_zero : charge ≠ 0
  ionMassOffset : ℝ

noncomputable def IonInterpretation.chargeMagnitude (c : IonInterpretation) : ℝ :=
  (c.charge.natAbs : ℝ)

theorem IonInterpretation.chargeMagnitude_pos (c : IonInterpretation) :
    0 < c.chargeMagnitude := by
  have h : 0 < c.charge.natAbs := Int.natAbs_pos.mpr c.charge_ne_zero
  change 0 < (c.charge.natAbs : ℝ)
  exact_mod_cast h

noncomputable def IonInterpretation.neutralMass (c : IonInterpretation) (mz : ℝ) : ℝ :=
  c.chargeMagnitude * mz - c.ionMassOffset

noncomputable def IonInterpretation.mzOfNeutralMass (c : IonInterpretation) (m : ℝ) : ℝ :=
  (m + c.ionMassOffset) / c.chargeMagnitude

theorem IonInterpretation.neutralMass_mz_roundTrip (c : IonInterpretation) (m : ℝ) :
    c.neutralMass (c.mzOfNeutralMass m) = m := by
  have hz := ne_of_gt c.chargeMagnitude_pos
  dsimp [IonInterpretation.neutralMass, IonInterpretation.mzOfNeutralMass]
  field_simp [hz]
  ring

theorem IonInterpretation.mz_neutralMass_roundTrip (c : IonInterpretation) (mz : ℝ) :
    c.mzOfNeutralMass (c.neutralMass mz) = mz := by
  have hz := ne_of_gt c.chargeMagnitude_pos
  dsimp [IonInterpretation.neutralMass, IonInterpretation.mzOfNeutralMass]
  field_simp [hz]
  ring

/-- Under one fixed charge/offset convention, the mass map preserves strict order. -/
theorem IonInterpretation.neutralMass_lt_iff (c : IonInterpretation) (x y : ℝ) :
    c.neutralMass x < c.neutralMass y ↔ x < y := by
  simp only [IonInterpretation.neutralMass, sub_lt_sub_iff_right]
  have hc := c.chargeMagnitude_pos
  constructor
  · intro h
    by_contra hxy
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hxy) hc.le
    exact (not_lt_of_ge hmul) h
  · intro h
    exact mul_lt_mul_of_pos_left h hc

/-- Interpret the stored positive coordinate as m/z, with a certified positive
neutral-mass result. Intensity is unchanged. -/
noncomputable def interpretPeak (c : IonInterpretation) (p : Peak)
    (h : 0 < c.neutralMass p.mass) : Peak where
  mass := c.neutralMass p.mass
  intensity := p.intensity
  mass_pos := h
  intensity_nonneg := p.intensity_nonneg

@[simp] theorem interpretPeak_intensity (c : IonInterpretation) (p : Peak)
    (h : 0 < c.neutralMass p.mass) :
    (interpretPeak c p h).intensity = p.intensity := rfl

/-- Apply a fixed interpretation without changing the peak index set. -/
noncomputable def interpretSpectrum {n : ℕ} (c : IonInterpretation) (S : Spectrum n)
    (h : ∀ i, 0 < c.neutralMass (S i).mass) : Spectrum n :=
  fun i => interpretPeak c (S i) (h i)

theorem interpretSpectrum_totalIntensity {n : ℕ} (c : IonInterpretation) (S : Spectrum n)
    (h : ∀ i, 0 < c.neutralMass (S i).mass) :
    totalIntensity (interpretSpectrum c S h) = totalIntensity S := rfl

/-- Each scan has its own finite peak count; no padding or common count is implied. -/
abbrev VariableSpectrum := Σ n : ℕ, Spectrum n

noncomputable def canonicalizeVariable (S : VariableSpectrum) : CanonicalSpectrum :=
  S.2.canonicalize

theorem canonicalizeVariable_length (S : VariableSpectrum) :
    (canonicalizeVariable S).peaks.length = S.1 :=
  Spectrum.canonicalize_length S.2

/-- Original and processed observations remain distinct, with explicit provenance. -/
structure ExperimentalScan where
  sourceId : String
  sourceChecksum : String
  processingId : String
  condition : AcquisitionCondition
  centroidedMz : VariableSpectrum

/-- A rational interchange record; its checker is exact arithmetic, not a RAW parser. -/
structure RationalPeakRecord where
  mz : ℚ
  intensity : ℚ
  deriving DecidableEq, Repr

def RationalPeakRecord.Valid (p : RationalPeakRecord) : Prop :=
  0 < p.mz ∧ 0 ≤ p.intensity

instance (p : RationalPeakRecord) : Decidable p.Valid :=
  inferInstanceAs (Decidable (0 < p.mz ∧ 0 ≤ p.intensity))

def RationalPeakRecord.check (p : RationalPeakRecord) : Bool := decide p.Valid

theorem RationalPeakRecord.check_iff (p : RationalPeakRecord) :
    p.check = true ↔ p.Valid := by simp [RationalPeakRecord.check]

noncomputable def RationalPeakRecord.toPeak (p : RationalPeakRecord) (h : p.Valid) : Peak where
  mass := (p.mz : ℝ)
  intensity := (p.intensity : ℝ)
  mass_pos := by exact_mod_cast h.1
  intensity_nonneg := by exact_mod_cast h.2

@[simp] theorem RationalPeakRecord.toPeak_mass (p : RationalPeakRecord) (h : p.Valid) :
    (p.toPeak h).mass = (p.mz : ℝ) := rfl

@[simp] theorem RationalPeakRecord.toPeak_intensity (p : RationalPeakRecord) (h : p.Valid) :
    (p.toPeak h).intensity = (p.intensity : ℝ) := rfl

end InfoGeometry.MassSpectrometry.ExperimentalObservation
