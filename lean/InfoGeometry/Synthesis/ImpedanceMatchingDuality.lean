import InfoGeometry.Detector.ConformalDualityHolonomy
import InfoGeometry.Spectral.QuadraticParameterReality

/-!
Two normalized quadratic functions share an extremal value. This module reuses
the detector polynomial and the Casimir parameterization; it does not identify
their physical units or prove a spectral theorem for an automorphic Laplacian.
The nonnegative-gap hypothesis is equivalent to the proposed lower bound.
-/

noncomputable section

namespace InfoGeometry.Synthesis.ImpedanceMatchingDuality

open InfoGeometry.Physics.HarishChandraCasimir
open InfoGeometry.Spectral.QuadraticParameterReality
open DetectorGeometry.ConformalDualityHolonomy

abbrev fisher_capacity (coupling efficiency : ℝ) : ℝ :=
  normSingles (coupling * efficiency)

def criticalValue (momentum : ℝ) : ℝ :=
  (casimirEigenvalue ⟨1 / 2, momentum⟩).re

theorem criticalValue_formula (momentum : ℝ) :
    criticalValue momentum = 1 / 4 + momentum ^ 2 :=
  real_part_of_critical ⟨1 / 2, momentum⟩ rfl

theorem capacity_vertex (coupling efficiency : ℝ) :
    fisher_capacity coupling efficiency = 1 / 4 - (coupling * efficiency - 1 / 2) ^ 2 :=
  normSingles_vertex_form _

theorem fisher_capacity_le_max (coupling efficiency : ℝ) :
    fisher_capacity coupling efficiency ≤ 1 / 4 := by
  rw [capacity_vertex]
  exact sub_le_self _ (sq_nonneg _)

theorem fisher_capacity_reaches_max (coupling : ℝ) (hnonzero : coupling ≠ 0) :
    fisher_capacity coupling (1 / (2 * coupling)) = 1 / 4 := by
  have hbalance : coupling * (1 / (2 * coupling)) = 1 / 2 := by
    field_simp
  rw [capacity_vertex, hbalance]
  norm_num

theorem capacity_maximum_iff (coupling efficiency : ℝ) (hnonzero : coupling ≠ 0) :
    fisher_capacity coupling efficiency = 1 / 4 ↔ efficiency = 1 / (2 * coupling) := by
  constructor
  · intro hequal
    rw [capacity_vertex] at hequal
    have hsquare : (coupling * efficiency - 1 / 2) ^ 2 = 0 := by linarith
    have hlinear := (sq_eq_zero_iff.mp hsquare)
    apply (eq_div_iff (mul_ne_zero (by norm_num) hnonzero)).mpr
    nlinarith
  · rintro rfl
    exact fisher_capacity_reaches_max coupling hnonzero

theorem criticalValue_lower_bound (momentum : ℝ) : 1 / 4 ≤ criticalValue momentum :=
  critical_lower_bound ⟨1 / 2, momentum⟩ rfl

theorem criticalValue_minimum_iff (momentum : ℝ) :
    criticalValue momentum = 1 / 4 ↔ momentum = 0 :=
  critical_minimum_iff ⟨1 / 2, momentum⟩ rfl

theorem capacity_isGreatest (coupling : ℝ) (hnonzero : coupling ≠ 0) :
    IsGreatest (Set.range (fisher_capacity coupling)) (1 / 4) := by
  refine ⟨⟨1 / (2 * coupling), fisher_capacity_reaches_max coupling hnonzero⟩, ?_⟩
  rintro value ⟨efficiency, rfl⟩
  exact fisher_capacity_le_max coupling efficiency

theorem criticalValue_isLeast : IsLeast (Set.range criticalValue) (1 / 4) := by
  refine ⟨⟨0, (criticalValue_minimum_iff 0).mpr rfl⟩, ?_⟩
  rintro value ⟨momentum, rfl⟩
  exact criticalValue_lower_bound momentum

def channel_duality_gap (coupling : ℝ) : ℝ :=
  sInf (Set.range criticalValue) - sSup (Set.range (fisher_capacity coupling))

theorem duality_gap_vanishes (coupling : ℝ) (hnonzero : coupling ≠ 0) :
    channel_duality_gap coupling = 0 := by
  rw [channel_duality_gap, criticalValue_isLeast.csInf_eq,
    (capacity_isGreatest coupling hnonzero).csSup_eq, sub_self]

theorem pointwise_gap (coupling efficiency momentum : ℝ) :
    criticalValue momentum - fisher_capacity coupling efficiency =
      momentum ^ 2 + (coupling * efficiency - 1 / 2) ^ 2 := by
  rw [criticalValue_formula, capacity_vertex]
  ring

theorem pointwise_gap_nonnegative (coupling efficiency momentum : ℝ) :
    0 ≤ criticalValue momentum - fisher_capacity coupling efficiency := by
  rw [pointwise_gap]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem unique_contact_point (coupling efficiency momentum : ℝ)
    (hnonzero : coupling ≠ 0) :
    fisher_capacity coupling efficiency = criticalValue momentum ↔
      efficiency = 1 / (2 * coupling) ∧ momentum = 0 := by
  constructor
  · intro hequal
    have hcapacity := fisher_capacity_le_max coupling efficiency
    have hcritical := criticalValue_lower_bound momentum
    have hmax : fisher_capacity coupling efficiency = 1 / 4 := by linarith
    have hmin : criticalValue momentum = 1 / 4 := by linarith
    exact ⟨(capacity_maximum_iff coupling efficiency hnonzero).mp hmax,
      (criticalValue_minimum_iff momentum).mp hmin⟩
  · rintro ⟨rfl, rfl⟩
    rw [fisher_capacity_reaches_max coupling hnonzero, criticalValue_formula]
    norm_num

theorem gap_positivity_iff_bound (value : ℝ) :
    0 ≤ value - 1 / 4 ↔ 1 / 4 ≤ value := sub_nonneg

theorem below_bound_has_negative_gap (value : ℝ) (hbelow : value < 1 / 4) :
    value - 1 / 4 < 0 := sub_neg.mpr hbelow

theorem zero_coupling_gap : channel_duality_gap 0 = 1 / 4 := by
  have hrange : Set.range (fisher_capacity 0) = {0} := by
    ext value
    simp [fisher_capacity, normSingles, eq_comm]
  rw [channel_duality_gap, criticalValue_isLeast.csInf_eq, hrange]
  simp

end InfoGeometry.Synthesis.ImpedanceMatchingDuality
