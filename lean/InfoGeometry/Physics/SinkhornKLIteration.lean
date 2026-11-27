/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SinkhornKLProjection
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The KL law for the actual alternating marginal updates

The existing rectangular row/column maps are used. The descending quantity is
KL from a fixed feasible coupling to the actual iterate. It is neither an axis
residual nor a purported primal objective evaluated outside its constraint set.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections
open InfoGeometry.Prequantum.JaynesKLPotential
variable {I J : Type*} [Fintype I] [Fintype J]

theorem matrixKL_three_point (P Q K : TransportPlan I J)
    (hQ : ∀ i j, 0 < Q i j) (hK : ∀ i j, 0 < K i j) :
    matrixKL P K = matrixKL P Q + matrixKL Q K +
      ∑ i, ∑ j, (P i j - Q i j) * Real.log (Q i j / K i j) := by
  have hpoint (i : I) (j : J) :
      scalarKLDivergence (P i j) (K i j) =
      scalarKLDivergence (P i j) (Q i j) + scalarKLDivergence (Q i j) (K i j) +
        (P i j - Q i j) * Real.log (Q i j / K i j) :=
    scalarKLDivergence_three_point _ _ _ (hQ i j) (hK i j)
  unfold matrixKL
  simp_rw [hpoint, Finset.sum_add_distrib]

theorem sinkhornRowUpdate_pos [Nonempty J]
    (M : TransportPlan I J) (r : I → ℝ)
    (hM : ∀ i j, 0 < M i j) (hr : ∀ i, 0 < r i) :
    ∀ i j, 0 < sinkhornRowUpdate M r i j := by
  intro i j
  exact mul_pos (div_pos (hr i)
    (Finset.sum_pos (fun k _ => hM i k) Finset.univ_nonempty)) (hM i j)

theorem sinkhornColUpdate_pos [Nonempty I]
    (M : TransportPlan I J) (c : J → ℝ)
    (hM : ∀ i j, 0 < M i j) (hc : ∀ j, 0 < c j) :
    ∀ i j, 0 < sinkhornColUpdate M c i j := by
  intro i j
  exact mul_pos (div_pos (hc j)
    (Finset.sum_pos (fun k _ => hM k j) Finset.univ_nonempty)) (hM i j)

/-- Row normalization is the exact KL projection onto its row constraint. -/
theorem matrixKL_row_pythagorean [Nonempty J]
    (P M : TransportPlan I J) (r : I → ℝ)
    (hM : ∀ i j, 0 < M i j) (hr : ∀ i, 0 < r i)
    (hPr : ∀ i, rowMass P i = r i) :
    matrixKL P M = matrixKL P (sinkhornRowUpdate M r) +
      matrixKL (sinkhornRowUpdate M r) M := by
  rw [matrixKL_three_point P _ M (sinkhornRowUpdate_pos M r hM hr) hM]
  suffices (∑ i, ∑ j,
      (P i j - sinkhornRowUpdate M r i j) *
        Real.log (sinkhornRowUpdate M r i j / M i j)) = 0 by rw [this, add_zero]
  apply Finset.sum_eq_zero
  intro i _
  have hm : 0 < ∑ j, M i j :=
    Finset.sum_pos (fun j _ => hM i j) Finset.univ_nonempty
  have hquot : ∀ j, sinkhornRowUpdate M r i j / M i j = r i / ∑ k, M i k := by
    intro j
    unfold sinkhornRowUpdate
    exact mul_div_cancel_right₀ _ (hM i j).ne'
  simp_rw [hquot]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib,
    sinkhornRowUpdate_row_sum M r i hm.ne']
  change (rowMass P i - r i) * _ = 0
  rw [hPr i, sub_self, zero_mul]

/-- Column normalization is the exact KL projection onto its column constraint. -/
theorem matrixKL_col_pythagorean [Nonempty I]
    (P M : TransportPlan I J) (c : J → ℝ)
    (hM : ∀ i j, 0 < M i j) (hc : ∀ j, 0 < c j)
    (hPc : ∀ j, colMass P j = c j) :
    matrixKL P M = matrixKL P (sinkhornColUpdate M c) +
      matrixKL (sinkhornColUpdate M c) M := by
  rw [matrixKL_three_point P _ M (sinkhornColUpdate_pos M c hM hc) hM]
  suffices (∑ i, ∑ j,
      (P i j - sinkhornColUpdate M c i j) *
        Real.log (sinkhornColUpdate M c i j / M i j)) = 0 by rw [this, add_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  have hm : 0 < ∑ i, M i j :=
    Finset.sum_pos (fun i _ => hM i j) Finset.univ_nonempty
  have hquot : ∀ i, sinkhornColUpdate M c i j / M i j = c j / ∑ k, M k j := by
    intro i
    unfold sinkhornColUpdate
    exact mul_div_cancel_right₀ _ (hM i j).ne'
  simp_rw [hquot]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib,
    sinkhornColUpdate_col_sum M c j hm.ne']
  change (colMass P j - c j) * _ = 0
  rw [hPc j, sub_self, zero_mul]

/-- The actual alternating row/column recursion starting at the reference matrix. -/
def sinkhornIterates (K : TransportPlan I J) (r : I → ℝ) (c : J → ℝ) :
    ℕ → TransportPlan I J :=
  Nat.rec (motive := fun _ => TransportPlan I J) K
    (fun _ M => sinkhornColUpdate (sinkhornRowUpdate M r) c)

@[simp] theorem sinkhornIterates_zero (K : TransportPlan I J) (r : I → ℝ) (c : J → ℝ) :
    sinkhornIterates K r c 0 = K := rfl

@[simp] theorem sinkhornIterates_succ (K : TransportPlan I J)
    (r : I → ℝ) (c : J → ℝ) (n : ℕ) :
    sinkhornIterates K r c (n + 1) =
      sinkhornColUpdate (sinkhornRowUpdate (sinkhornIterates K r c n) r) c := rfl

section Positive
variable [Nonempty I] [Nonempty J]
variable (K : TransportPlan I J) (r : I → ℝ) (c : J → ℝ)
variable (hK : ∀ i j, 0 < K i j) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
include hK hr hc

theorem sinkhornIterates_pos (n : ℕ) : ∀ i j, 0 < sinkhornIterates K r c n i j := by
  induction n with
  | zero => exact hK
  | succ n ih =>
    exact sinkhornColUpdate_pos _ c (sinkhornRowUpdate_pos _ r ih hr) hc

theorem sinkhornIterates_colMass (n : ℕ) (j : J) :
    colMass (sinkhornIterates K r c (n + 1)) j = c j := by
  exact sinkhornColUpdate_col_sum _ c j
    (Finset.sum_pos (fun i _ => sinkhornRowUpdate_pos _ r
      (sinkhornIterates_pos K r c hK hr hc n) hr i j) Finset.univ_nonempty).ne'

/-- A full iteration has an exact two-term KL dissipation identity. -/
theorem sinkhornIterates_KL_identity (P : TransportPlan I J)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j) (n : ℕ) :
    matrixKL P (sinkhornIterates K r c n) =
      matrixKL P (sinkhornIterates K r c (n + 1)) +
      matrixKL (sinkhornRowUpdate (sinkhornIterates K r c n) r)
        (sinkhornIterates K r c n) +
      matrixKL (sinkhornIterates K r c (n + 1))
        (sinkhornRowUpdate (sinkhornIterates K r c n) r) := by
  have hm := sinkhornIterates_pos K r c hK hr hc n
  have hrow := matrixKL_row_pythagorean P (sinkhornIterates K r c n) r hm hr hPr
  have hcol := matrixKL_col_pythagorean P
    (sinkhornRowUpdate (sinkhornIterates K r c n) r) c
    (sinkhornRowUpdate_pos _ r hm hr) hc hPc
  rw [hcol] at hrow
  change matrixKL P (sinkhornIterates K r c n) =
    matrixKL P (sinkhornIterates K r c (n + 1)) +
    matrixKL (sinkhornIterates K r c (n + 1))
      (sinkhornRowUpdate (sinkhornIterates K r c n) r) +
    matrixKL (sinkhornRowUpdate (sinkhornIterates K r c n) r)
      (sinkhornIterates K r c n) at hrow
  linarith

theorem sinkhornIterates_KL_antitone (P : TransportPlan I J)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j) :
    Antitone (fun n => matrixKL P (sinkhornIterates K r c n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hm := sinkhornIterates_pos K r c hK hr hc n
  have hrow := sinkhornRowUpdate_pos _ r hm hr
  have hnext := sinkhornIterates_pos K r c hK hr hc (n + 1)
  have hd₁ := matrixKL_nonneg _ _ (fun i j => (hrow i j).le) hm
  have hd₂ := matrixKL_nonneg _ _ (fun i j => (hnext i j).le) hrow
  have hid := sinkhornIterates_KL_identity K r c hK hr hc P hPr hPc n
  linarith

/-- Vanishing row-step divergence, used downstream to prove matrix convergence. -/
theorem sinkhornIterates_rowGap_tendsto (P : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j) :
    Tendsto (fun n => matrixKL (sinkhornRowUpdate (sinkhornIterates K r c n) r)
      (sinkhornIterates K r c n)) atTop (𝓝 0) := by
  let f := fun n => matrixKL P (sinkhornIterates K r c n)
  have hanti : Antitone f := sinkhornIterates_KL_antitone K r c hK hr hc P hPr hPc
  have hbounded : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact matrixKL_nonneg _ _ hP (sinkhornIterates_pos K r c hK hr hc n)
  have hlim : Tendsto f atTop (𝓝 (⨅ n, f n)) := tendsto_atTop_ciInf hanti hbounded
  have hdiff : Tendsto (fun n => f n - f (n + 1)) atTop (𝓝 0) := by
    simpa using hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff
  · intro n
    exact matrixKL_nonneg _ _
      (fun i j => (sinkhornRowUpdate_pos _ r
        (sinkhornIterates_pos K r c hK hr hc n) hr i j).le)
      (sinkhornIterates_pos K r c hK hr hc n)
  · intro n
    have hrow := sinkhornRowUpdate_pos _ r
      (sinkhornIterates_pos K r c hK hr hc n) hr
    have hnonneg := matrixKL_nonneg _ _
      (fun i j => (sinkhornIterates_pos K r c hK hr hc (n + 1) i j).le) hrow
    have hid := sinkhornIterates_KL_identity K r c hK hr hc P hPr hPc n
    change _ ≤ matrixKL P (sinkhornIterates K r c n) -
      matrixKL P (sinkhornIterates K r c (n + 1))
    linarith

end Positive
end InfoGeometry.Physics.AmariSinkhornAlternatingProjections
