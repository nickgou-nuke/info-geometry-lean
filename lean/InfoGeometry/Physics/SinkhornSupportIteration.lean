/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SinkhornSupportKL

/-! # The actual finite iteration on a preserved support -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections
open InfoGeometry.Prequantum.JaynesKLPotential
variable {I J : Type*} [Fintype I] [Fintype J]

lemma scaled_rowMass_pos (K : TransportPlan I J) (u : I → ℝ) (v : J → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hs : ∀ i, ∃ j, 0 < K i j) (i : I) :
    0 < rowMass (fun i j => u i * K i j * v j) i := by
  obtain ⟨j, hj⟩ := hs i
  exact Finset.sum_pos'
    (fun k _ => mul_nonneg (mul_nonneg (hu i).le (hK i k)) (hv k).le)
    ⟨j, Finset.mem_univ j, mul_pos (mul_pos (hu i) hj) (hv j)⟩

lemma scaled_colMass_pos (K : TransportPlan I J) (u : I → ℝ) (v : J → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hs : ∀ j, ∃ i, 0 < K i j) (j : J) :
    0 < colMass (fun i j => u i * K i j * v j) j := by
  obtain ⟨i, hi⟩ := hs j
  exact Finset.sum_pos'
    (fun k _ => mul_nonneg (mul_nonneg (hu k).le (hK k j)) (hv j).le)
    ⟨i, Finset.mem_univ i, mul_pos (mul_pos (hu i) hi) (hv j)⟩

section
variable (K : TransportPlan I J) (r : I → ℝ) (c : J → ℝ)
variable (hK : ∀ i j, 0 ≤ K i j)
variable (hrows : ∀ i, ∃ j, 0 < K i j) (hcols : ∀ j, ∃ i, 0 < K i j)
variable (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
include hK hrows hcols hr hc

theorem sinkhornIterates_scaling_supported (n : ℕ) :
    ∃ u : I → ℝ, ∃ v : J → ℝ, (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      sinkhornIterates K r c n = (fun i j => u i * K i j * v j) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 1, fun _ => 1, fun _ => zero_lt_one, fun _ => zero_lt_one, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨u, v, hu, hv, he⟩ := ih
    let M := sinkhornIterates K r c n
    let R := sinkhornRowUpdate M r
    have hrow : ∀ i, 0 < rowMass M i := by
      intro i
      change 0 < rowMass (sinkhornIterates K r c n) i
      rw [he]
      exact scaled_rowMass_pos K u v hK hu hv hrows i
    let a : I → ℝ := fun i => r i / rowMass M i
    have ha : ∀ i, 0 < a i := fun i => div_pos (hr i) (hrow i)
    have hRe : R = fun i j => (a i * u i) * K i j * v j := by
      funext i j
      change a i * M i j = _
      have hij : M i j = u i * K i j * v j := congrFun (congrFun he i) j
      rw [hij]
      ring
    have hcol : ∀ j, 0 < colMass R j := by
      intro j
      rw [hRe]
      exact scaled_colMass_pos K (fun i => a i * u i) v hK
        (fun i => mul_pos (ha i) (hu i)) hv hcols j
    let b : J → ℝ := fun j => c j / colMass R j
    have hb : ∀ j, 0 < b j := fun j => div_pos (hc j) (hcol j)
    refine ⟨fun i => a i * u i, fun j => b j * v j,
      fun i => mul_pos (ha i) (hu i), fun j => mul_pos (hb j) (hv j), ?_⟩
    funext i j
    change b j * R i j = _
    rw [hRe]
    ring

theorem sinkhornIterates_nonneg_supported (n : ℕ) (i : I) (j : J) :
    0 ≤ sinkhornIterates K r c n i j := by
  obtain ⟨u, v, hu, hv, he⟩ := sinkhornIterates_scaling_supported K r c hK hrows hcols hr hc n
  rw [he]
  exact mul_nonneg (mul_nonneg (hu i).le (hK i j)) (hv j).le

theorem sinkhornIterates_zero_iff (n : ℕ) (i : I) (j : J) :
    sinkhornIterates K r c n i j = 0 ↔ K i j = 0 := by
  obtain ⟨u, v, hu, hv, he⟩ := sinkhornIterates_scaling_supported K r c hK hrows hcols hr hc n
  simp [he, (hu i).ne', (hv j).ne']

theorem sinkhornIterates_pos_on_support (n : ℕ) (i : I) (j : J) (hij : 0 < K i j) :
    0 < sinkhornIterates K r c n i j := by
  obtain ⟨u, v, hu, hv, he⟩ := sinkhornIterates_scaling_supported K r c hK hrows hcols hr hc n
  rw [he]
  exact mul_pos (mul_pos (hu i) hij) (hv j)

theorem sinkhornIterates_rowMass_pos_supported (n : ℕ) (i : I) :
    0 < rowMass (sinkhornIterates K r c n) i := by
  obtain ⟨u, v, hu, hv, he⟩ := sinkhornIterates_scaling_supported K r c hK hrows hcols hr hc n
  rw [he]
  exact scaled_rowMass_pos K u v hK hu hv hrows i

theorem sinkhornIterates_rowUpdate_colMass_pos_supported (n : ℕ) (j : J) :
    0 < colMass (sinkhornRowUpdate (sinkhornIterates K r c n) r) j := by
  obtain ⟨i, hi⟩ := hcols j
  have hm := sinkhornIterates_nonneg_supported K r c hK hrows hcols hr hc n
  have hsum := sinkhornIterates_rowMass_pos_supported K r c hK hrows hcols hr hc n
  have ha (k : I) : 0 < r k / rowMass (sinkhornIterates K r c n) k :=
    div_pos (hr k) (hsum k)
  exact Finset.sum_pos'
    (fun k _ => mul_nonneg (ha k).le (hm k j))
    ⟨i, Finset.mem_univ i, mul_pos (ha i)
      (sinkhornIterates_pos_on_support K r c hK hrows hcols hr hc n i j hi)⟩

theorem sinkhornIterates_colMass_supported (n : ℕ) (j : J) :
    colMass (sinkhornIterates K r c (n + 1)) j = c j :=
  sinkhornColUpdate_col_sum _ c j
    (sinkhornIterates_rowUpdate_colMass_pos_supported K r c hK hrows hcols hr hc n j).ne'

theorem sinkhornIterates_KL_identity_supported (P : TransportPlan I J)
    (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j) (n : ℕ) :
    matrixKL P (sinkhornIterates K r c n) =
      matrixKL P (sinkhornIterates K r c (n + 1)) +
      matrixKL (sinkhornRowUpdate (sinkhornIterates K r c n) r) (sinkhornIterates K r c n) +
      matrixKL (sinkhornIterates K r c (n + 1))
        (sinkhornRowUpdate (sinkhornIterates K r c n) r) := by
  have hm := sinkhornIterates_nonneg_supported K r c hK hrows hcols hr hc n
  have hsum := sinkhornIterates_rowMass_pos_supported K r c hK hrows hcols hr hc n
  have hPM : ∀ i j, sinkhornIterates K r c n i j = 0 → P i j = 0 := by
    intro i j hz
    exact hPK i j ((sinkhornIterates_zero_iff K r c hK hrows hcols hr hc n i j).1 hz)
  have ha (i : I) : 0 < r i / rowMass (sinkhornIterates K r c n) i :=
    div_pos (hr i) (hsum i)
  have hR : ∀ i j, 0 ≤ sinkhornRowUpdate (sinkhornIterates K r c n) r i j :=
    fun i j => mul_nonneg (ha i).le (hm i j)
  have hPR : ∀ i j, sinkhornRowUpdate (sinkhornIterates K r c n) r i j = 0 → P i j = 0 := by
    intro i j hz
    apply hPM i j
    exact (mul_eq_zero.mp hz).resolve_left (ha i).ne'
  have hrow := matrixKL_row_pythagorean_supported P _ r hm hr hsum hPM hPr
  have hcol := matrixKL_col_pythagorean_supported P _ c hR hc
    (sinkhornIterates_rowUpdate_colMass_pos_supported K r c hK hrows hcols hr hc n) hPR hPc
  rw [hcol] at hrow
  change matrixKL P (sinkhornIterates K r c n) =
    matrixKL P (sinkhornIterates K r c (n + 1)) +
    matrixKL (sinkhornIterates K r c (n + 1))
      (sinkhornRowUpdate (sinkhornIterates K r c n) r) +
    matrixKL (sinkhornRowUpdate (sinkhornIterates K r c n) r) (sinkhornIterates K r c n) at hrow
  linarith

theorem sinkhornIterates_rowGap_nonneg_supported (n : ℕ) :
    0 ≤ matrixKL (sinkhornRowUpdate (sinkhornIterates K r c n) r) (sinkhornIterates K r c n) := by
  have hm := sinkhornIterates_nonneg_supported K r c hK hrows hcols hr hc n
  have hsum := sinkhornIterates_rowMass_pos_supported K r c hK hrows hcols hr hc n
  apply matrixKL_nonneg_supported _ _
    (fun i j => mul_nonneg (div_pos (hr i) (hsum i)).le (hm i j)) hm
  intro i j hz
  simp [sinkhornRowUpdate, hz]

theorem sinkhornIterates_colGap_nonneg_supported (n : ℕ) :
    0 ≤ matrixKL (sinkhornIterates K r c (n + 1))
      (sinkhornRowUpdate (sinkhornIterates K r c n) r) := by
  have hm := sinkhornIterates_nonneg_supported K r c hK hrows hcols hr hc n
  have hsum := sinkhornIterates_rowMass_pos_supported K r c hK hrows hcols hr hc n
  apply matrixKL_nonneg_supported _ _
    (sinkhornIterates_nonneg_supported K r c hK hrows hcols hr hc (n + 1))
    (fun i j => mul_nonneg (div_pos (hr i) (hsum i)).le (hm i j))
  intro i j hz
  change sinkhornRowUpdate (sinkhornIterates K r c n) r i j = 0 at hz
  exact sinkhornColUpdate_eq_zero_of_eq_zero _ c i j hz

theorem sinkhornIterates_KL_antitone_supported (P : TransportPlan I J)
    (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j) :
    Antitone (fun n => matrixKL P (sinkhornIterates K r c n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := sinkhornIterates_KL_identity_supported K r c hK hrows hcols hr hc P hPK hPr hPc n
  have h₁ := sinkhornIterates_rowGap_nonneg_supported K r c hK hrows hcols hr hc n
  have h₂ := sinkhornIterates_colGap_nonneg_supported K r c hK hrows hcols hr hc n
  linarith

theorem sinkhornIterates_rowGap_tendsto_supported (P : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j) (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hPr : ∀ i, rowMass P i = r i) (hPc : ∀ j, colMass P j = c j) :
    Tendsto (fun n => matrixKL (sinkhornRowUpdate (sinkhornIterates K r c n) r)
      (sinkhornIterates K r c n)) atTop (𝓝 0) := by
  let f := fun n => matrixKL P (sinkhornIterates K r c n)
  have hanti : Antitone f := sinkhornIterates_KL_antitone_supported K r c hK hrows hcols hr hc P hPK hPr hPc
  have hbounded : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply matrixKL_nonneg_supported _ _ hP
      (sinkhornIterates_nonneg_supported K r c hK hrows hcols hr hc n)
    intro i j hz
    exact hPK i j ((sinkhornIterates_zero_iff K r c hK hrows hcols hr hc n i j).1 hz)
  have hlim : Tendsto f atTop (𝓝 (⨅ n, f n)) := tendsto_atTop_ciInf hanti hbounded
  have hdiff : Tendsto (fun n => f n - f (n + 1)) atTop (𝓝 0) := by
    simpa using hlim.sub (hlim.comp (tendsto_add_atTop_nat 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff
  · exact sinkhornIterates_rowGap_nonneg_supported K r c hK hrows hcols hr hc
  · intro n
    have h := sinkhornIterates_KL_identity_supported K r c hK hrows hcols hr hc P hPK hPr hPc n
    have h₂ := sinkhornIterates_colGap_nonneg_supported K r c hK hrows hcols hr hc n
    change _ ≤ matrixKL P (sinkhornIterates K r c n) - matrixKL P (sinkhornIterates K r c (n + 1))
    linarith

end
end InfoGeometry.Physics.AmariSinkhornAlternatingProjections
