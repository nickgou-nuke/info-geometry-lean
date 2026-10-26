import InfoGeometry.MassSpectrometry.BirkhoffAssignment

/-!
# Rectangular partial peak--fragment transport

Rows and columns have independently specified nonnegative capacities. The
unmatched residuals are retained, rather than silently enforcing a bijection.
The existing square doubly-stochastic assignment is recovered as a special case.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry
open scoped BigOperators

structure PartialPeakAssignment (I J : Type*) [Fintype I] [Fintype J] where
  weight : Matrix I J ℝ
  peakCapacity : I → ℝ
  fragmentCapacity : J → ℝ
  nonneg : ∀ i j, 0 ≤ weight i j
  row_le : ∀ i, ∑ j, weight i j ≤ peakCapacity i
  col_le : ∀ j, ∑ i, weight i j ≤ fragmentCapacity j

namespace PartialPeakAssignment
variable {I J : Type*} [Fintype I] [Fintype J]

def unmatchedPeak (P : PartialPeakAssignment I J) (i : I) : ℝ :=
  P.peakCapacity i - ∑ j, P.weight i j

def undetectedFragment (P : PartialPeakAssignment I J) (j : J) : ℝ :=
  P.fragmentCapacity j - ∑ i, P.weight i j

theorem unmatchedPeak_nonneg (P : PartialPeakAssignment I J) (i : I) :
    0 ≤ P.unmatchedPeak i := sub_nonneg.mpr (P.row_le i)

theorem undetectedFragment_nonneg (P : PartialPeakAssignment I J) (j : J) :
    0 ≤ P.undetectedFragment j := sub_nonneg.mpr (P.col_le j)

theorem peakCapacity_nonneg (P : PartialPeakAssignment I J) (i : I) :
    0 ≤ P.peakCapacity i :=
  (Finset.sum_nonneg fun j _ => P.nonneg i j).trans (P.row_le i)

theorem fragmentCapacity_nonneg (P : PartialPeakAssignment I J) (j : J) :
    0 ≤ P.fragmentCapacity j :=
  (Finset.sum_nonneg fun i _ => P.nonneg i j).trans (P.col_le j)

theorem peak_accounting (P : PartialPeakAssignment I J) (i : I) :
    (∑ j, P.weight i j) + P.unmatchedPeak i = P.peakCapacity i := by
  simp [unmatchedPeak]

theorem fragment_accounting (P : PartialPeakAssignment I J) (j : J) :
    (∑ i, P.weight i j) + P.undetectedFragment j = P.fragmentCapacity j := by
  simp [undetectedFragment]

/-- Exact imbalance accounting: no observed or candidate capacity disappears. -/
theorem residual_mass_balance (P : PartialPeakAssignment I J) :
    (∑ i, P.unmatchedPeak i) - (∑ j, P.undetectedFragment j) =
      (∑ i, P.peakCapacity i) - (∑ j, P.fragmentCapacity j) := by
  simp only [unmatchedPeak, undetectedFragment, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun j i => P.weight i j)]
  ring

/-- The all-unmatched plan exists for any nonnegative capacity vectors. -/
def zeroPlan (r : I → ℝ) (c : J → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j) : PartialPeakAssignment I J where
  weight := 0
  peakCapacity := r
  fragmentCapacity := c
  nonneg := by simp
  row_le := by simpa using hr
  col_le := by simpa using hc

@[simp] theorem zeroPlan_unmatched (r : I → ℝ) (c : J → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j) (i : I) :
    (zeroPlan r c hr hc).unmatchedPeak i = r i := by simp [zeroPlan, unmatchedPeak]

/-- Reuse the existing exact square Birkhoff certificate, without a new predicate. -/
def ofSoftAssignment {n : ℕ} (A : AssignmentMatrix n) (h : IsSoftAssignment A) :
    PartialPeakAssignment (Fin n) (Fin n) where
  weight := A
  peakCapacity := fun _ => 1
  fragmentCapacity := fun _ => 1
  nonneg := (mem_doublyStochastic_iff_sum.mp h).1
  row_le := fun i => ((mem_doublyStochastic_iff_sum.mp h).2.1 i).le
  col_le := fun j => ((mem_doublyStochastic_iff_sum.mp h).2.2 j).le

theorem ofSoftAssignment_no_residual {n : ℕ}
    (A : AssignmentMatrix n) (h : IsSoftAssignment A) :
    (∀ i, (ofSoftAssignment A h).unmatchedPeak i = 0) ∧
    (∀ j, (ofSoftAssignment A h).undetectedFragment j = 0) := by
  constructor
  · intro i
    simp [unmatchedPeak, ofSoftAssignment, (mem_doublyStochastic_iff_sum.mp h).2.1 i]
  · intro j
    simp [undetectedFragment, ofSoftAssignment, (mem_doublyStochastic_iff_sum.mp h).2.2 j]

/-- Zero residuals recover Birkhoff only for a square, unit-capacity plan. -/
theorem softAssignment_of_no_residual {n : ℕ}
    (P : PartialPeakAssignment (Fin n) (Fin n))
    (hr : ∀ i, P.peakCapacity i = 1) (hc : ∀ j, P.fragmentCapacity j = 1)
    (hu : ∀ i, P.unmatchedPeak i = 0) (hv : ∀ j, P.undetectedFragment j = 0) :
    IsSoftAssignment P.weight := by
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨P.nonneg, ?_, ?_⟩
  · intro i
    have h := P.peak_accounting i
    simpa [hu i, hr i] using h
  · intro j
    have h := P.fragment_accounting j
    simpa [hv j, hc j] using h

end PartialPeakAssignment
end InfoGeometry.MassSpectrometry
