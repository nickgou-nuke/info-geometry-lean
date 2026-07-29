import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.DrazinAnomaly

/-!
# Transport observables from proof-carrying Drazin readouts

The Landauer--Büttiker conductance identity is formalized as an algebraic
readout theorem. The physical resonance statement is an explicit field of
`AndreevDrazinReadout`, together with probability bounds.
-/

noncomputable section

namespace InfoGeometry.Canonical.TransportObservable

open InfoGeometry.Canonical.DrazinAnomaly

/-! ## Laboratory constants and Landauer readout -/

variable (e_charge : ℝ) (planck_h : ℝ)

/-- The doubled Nambu--Gor'kov conductance quantum `2e²/h`. -/
def conductance_quantum : ℝ :=
  (2 * e_charge ^ 2) / planck_h

/--
Proof-carrying Andreev/Drazin transport readout for one boundary operator.

The field `andreev_resonance` is the empirical/topological calibration linking
the scalar Andreev probability to the Drazin anomaly readout. It is deliberately
proof-carrying data, not a primitive declaration.
-/
abbrev AndreevDrazinReadout (Op : SpinorOp) (k : ℕ) : Type :=
  Σ' anomaly : DrazinAnomalyReadout Gamma_11 Op k,
    Σ' andreevProbability : ℝ,
      0 ≤ andreevProbability ∧
        andreevProbability ≤ 1 ∧
          andreevProbability = |(drazin_anomaly_index anomaly : ℝ)|

namespace AndreevDrazinReadout

variable {Op : SpinorOp} {k : ℕ} (R : AndreevDrazinReadout Op k)

abbrev anomaly : DrazinAnomalyReadout Gamma_11 Op k := R.1
abbrev andreevProbability : ℝ := R.2.1
abbrev andreevProbability_nonneg : 0 ≤ R.andreevProbability := R.2.2.1
abbrev andreevProbability_le_one : R.andreevProbability ≤ 1 := R.2.2.2.1
abbrev andreev_resonance :
    R.andreevProbability = |(drazin_anomaly_index R.anomaly : ℝ)| := R.2.2.2.2

/-- The readout exposes the Drazin-defect witness used by the anomaly packet. -/
theorem is_drazin_defective (R : AndreevDrazinReadout Op k) :
    DrazinAnomaly.is_drazin_defective Op k :=
  DrazinAnomalyReadout.is_drazin_defective R.anomaly

/-- The Andreev reflection probability carried by the readout. -/
def andreev_probability : ℝ :=
  R.andreevProbability

/-- The Andreev probability is bounded by construction. -/
theorem andreev_probability_bounds :
    0 ≤ R.andreev_probability ∧ R.andreev_probability ≤ 1 :=
  ⟨R.andreevProbability_nonneg, R.andreevProbability_le_one⟩

/-- The calibrated resonance equality carried by the readout. -/
theorem andreev_resonance_is_anomaly :
    R.andreev_probability = |(drazin_anomaly_index R.anomaly : ℝ)| :=
  R.andreev_resonance

/-- Zero-bias differential conductance for this readout. -/
def zero_bias_conductance : ℝ :=
  conductance_quantum e_charge planck_h * R.andreev_probability

/--
Geometry-to-observable transport identity.

Once a proof-carrying readout supplies the Andreev/Drazin resonance equality,
the Landauer conductance formula is immediate algebra.
-/
theorem majorana_conductance_peak :
    R.zero_bias_conductance e_charge planck_h =
      conductance_quantum e_charge planck_h *
        |(drazin_anomaly_index R.anomaly : ℝ)| := by
  unfold zero_bias_conductance andreev_probability
  rw [R.andreev_resonance]

/-- If the calibrated index has absolute value `1`, the Andreev probability is perfect. -/
theorem andreev_probability_eq_one_of_abs_index_eq_one
    (hindex : |(drazin_anomaly_index R.anomaly : ℝ)| = 1) :
    R.andreev_probability = 1 := by
  rw [andreev_resonance_is_anomaly, hindex]

/--
Unit-index specialization: perfect Andreev resonance gives exactly the
conductance quantum.
-/
theorem majorana_conductance_peak_of_abs_index_eq_one
    (hindex : |(drazin_anomaly_index R.anomaly : ℝ)| = 1) :
    R.zero_bias_conductance e_charge planck_h =
      conductance_quantum e_charge planck_h := by
  rw [majorana_conductance_peak, hindex, mul_one]

end AndreevDrazinReadout

end InfoGeometry.Canonical.TransportObservable
