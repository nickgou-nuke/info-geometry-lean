import InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.XiHardyZNormalizationBridge
import InfoGeometry.Topology.XiHardyZNormalizationBridge

/-!
# Concrete critical-line readout for the Hardy normalization interface

This owner exposes the actual completed-zeta readout on the critical line and
provides a constructor for `HardyZNormalizationDatum` from an explicit real
factorization.  The factorization is intentionally a hypothesis: this file
does not identify an independently constructed Hardy `Z` or theta factor with
the classical analytic objects.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge

open InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
open InfoGeometry.Canonical.XiHardyZNormalization
open InfoGeometry.Topology.XiHardyZNormalizationBridge

/-- The real critical-line readout of the concrete completed `riemannXi`. -/
def actualXiCriticalReadout (t : ℝ) : ℝ :=
  centeredRiemannXiReal 0 t

/-! A canonical algebraic readout obtained by dividing the actual critical-line
`Xi` value by the standard nonvanishing real prefactor.  This is deliberately
named `candidate`: no theorem identifying it with the classical Hardy
`Z`-function is asserted here. -/
def candidateHardyZ (t : ℝ) : ℝ :=
  actualXiCriticalReadout t / hardyNormalizationFactor t

theorem hardyNormalizationFactor_neg_eq (t : ℝ) :
    hardyNormalizationFactor (-t) = hardyNormalizationFactor t := by
  have harg :
      (1 / 4 : ℂ) + Complex.I * ((-t : ℝ) : ℂ) / 2 =
        star ((1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2) := by
    apply Complex.ext <;> simp
  have hgamma :
      Complex.Gamma (star ((1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2)) =
        star (Complex.Gamma ((1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2)) := by
    simpa only [starRingEnd_apply] using
      Complex.Gamma_conj ((1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2)
  unfold hardyNormalizationFactor
  rw [harg, hgamma]
  simp

theorem candidateHardyZ_neg (t : ℝ) :
    candidateHardyZ (-t) = candidateHardyZ t := by
  have hxi : actualXiCriticalReadout (-t) = actualXiCriticalReadout t := by
    unfold actualXiCriticalReadout
    simpa using congrArg Complex.re (centeredRiemannXi_neg 0 t)
  rw [candidateHardyZ, candidateHardyZ, hxi,
    hardyNormalizationFactor_neg_eq]

theorem actualXiCriticalReadout_eq_factor_mul_candidateHardyZ (t : ℝ) :
    actualXiCriticalReadout t =
      hardyNormalizationFactor t * candidateHardyZ t := by
  unfold candidateHardyZ
  field_simp [hardyNormalizationFactor_ne_zero t]

theorem actualXiCriticalReadout_zero_iff_candidateHardyZ_zero (t : ℝ) :
    actualXiCriticalReadout t = 0 ↔ candidateHardyZ t = 0 := by
  rw [actualXiCriticalReadout_eq_factor_mul_candidateHardyZ]
  exact zero_iff_of_mul_eq_zero_of_ne_zero _ _
    (hardyNormalizationFactor_ne_zero t)

/-- The concrete normalized critical-line readout obtained from `riemannXi`.
This is an actual normalization datum, but its `Z` field is the candidate
readout above rather than an identification with the classical Hardy function.
-/
def actualCandidateHardyZNormalizationDatum : HardyZNormalizationDatum where
  xi_crit := actualXiCriticalReadout
  Z := candidateHardyZ
  r := hardyNormalizationFactor
  r_ne_zero := hardyNormalizationFactor_ne_zero
  rel := actualXiCriticalReadout_eq_factor_mul_candidateHardyZ

@[simp] theorem actualCandidateHardyZNormalizationDatum_Z (t : ℝ) :
    actualCandidateHardyZNormalizationDatum.Z t = candidateHardyZ t := rfl

theorem actualCandidateHardyZNormalizationDatum_even (t : ℝ) :
    actualCandidateHardyZNormalizationDatum.Z (-t) =
      actualCandidateHardyZNormalizationDatum.Z t := by
  exact candidateHardyZ_neg t

theorem actualCandidateHardyZNormalizationDatum_zero_iff
    (t : ℝ) :
    actualCandidateHardyZNormalizationDatum.xi_crit t = 0 ↔
      actualCandidateHardyZNormalizationDatum.Z t = 0 := by
  exact xi_crit_zero_iff_Z_zero actualCandidateHardyZNormalizationDatum t

/-- Explicit data sufficient to realize the Hardy normalization interface. -/
structure HardyZFactorizationHypothesis where
  Z : ℝ → ℝ
  r : ℝ → ℝ
  r_ne_zero : ∀ t : ℝ, r t ≠ 0
  factorization : ∀ t : ℝ,
    actualXiCriticalReadout t = r t * Z t

/-! Any factorization using this same nonvanishing prefactor has the candidate
readout as its unique normalized function.  This is an algebraic uniqueness
statement, not the missing analytic identification with classical Hardy `Z`. -/
theorem factorized_Z_eq_candidateHardyZ
    (H : HardyZFactorizationHypothesis)
    (h_factor : ∀ t : ℝ, H.r t = hardyNormalizationFactor t)
    (t : ℝ) :
    H.Z t = candidateHardyZ t := by
  unfold candidateHardyZ
  rw [← h_factor t]
  apply (eq_div_iff (H.r_ne_zero t)).2
  calc
    H.Z t * H.r t = H.r t * H.Z t := mul_comm _ _
    _ = actualXiCriticalReadout t := (H.factorization t).symm

/-- Construct the existing normalization datum from explicit factorization data. -/
def actualHardyZNormalizationDatum
    (H : HardyZFactorizationHypothesis) : HardyZNormalizationDatum where
  xi_crit := actualXiCriticalReadout
  Z := H.Z
  r := H.r
  r_ne_zero := H.r_ne_zero
  rel := H.factorization

@[simp] theorem actualHardyZNormalizationDatum_xi_crit
    (H : HardyZFactorizationHypothesis) (t : ℝ) :
    (actualHardyZNormalizationDatum H).xi_crit t =
      actualXiCriticalReadout t := rfl

@[simp] theorem actualHardyZNormalizationDatum_Z
    (H : HardyZFactorizationHypothesis) (t : ℝ) :
    (actualHardyZNormalizationDatum H).Z t = H.Z t := rfl

theorem actualXiCriticalReadout_zero_iff_factorized_Z_zero
    (H : HardyZFactorizationHypothesis) (t : ℝ) :
    actualXiCriticalReadout t = 0 ↔ H.Z t = 0 := by
  exact xi_crit_zero_iff_Z_zero (actualHardyZNormalizationDatum H) t

theorem actualHardyZNormalizationDatum_master
    (H : HardyZFactorizationHypothesis) (t : ℝ) :
    actualXiCriticalReadout t = H.r t * H.Z t ∧
      H.r t ≠ 0 ∧
      (actualXiCriticalReadout t = 0 ↔ H.Z t = 0) := by
  exact hardy_z_normalization_master_synthesis
    (actualHardyZNormalizationDatum H) t

end InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge
