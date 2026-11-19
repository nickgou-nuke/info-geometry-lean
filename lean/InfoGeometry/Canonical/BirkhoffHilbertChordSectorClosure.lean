/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.BirkhoffHilbertConeMetric

/-!
# Birkhoff–Hilbert Arbitrary-Endpoint Two-Ray Sector & Projective Chord Closure

This module closes the documented gap on `InfoGeometry.Erlangen.BirkhoffHilbertConeMetric`
regarding the explicit two-ray sector hypothesis in `birkhoff_crossRatio_chord_identity`.

For ANY salient `C : ProperCone ℝ E` on a real normed space `[Nontrivial E]` and ANY two interior
points `x, y ∈ interior (C : Set E)` on distinct rays (`¬ ∃ c : ℝ, 0 < c ∧ x = c • y`), without
assuming incomparability or supplying any boundary sector axiom:

1. **Constructive Boundary-Ray Extraction**:
   Defines the two cone-frontier rays
   - `extremalRayLeft C x y := upperGauge C y x • x - y`
   - `extremalRayRight C x y := upperGauge C x y • y - x`
   and proves `1 < upperGauge C x y * upperGauge C y x`, `u ≠ 0`, `v ≠ 0`,
   `u ∈ frontier (C : Set E)`, and `v ∈ frontier (C : Set E)`.
2. **Unconditional Derivation of the Two-Ray Sector Hypothesis & Linear Independence**:
   Proves `extremalRays_twoRay_sector`:
   `∀ α β : ℝ, α • u + β • v ∈ C → 0 ≤ α ∧ 0 ≤ β`,
   and deduces `extremalRays_linearIndependent : LinearIndependent ℝ ![u, v]`.
3. **Unconditional Projective Chord Cross-Ratio Theorem**:
   Constructs `τ_x := 1 / (upperGauge C x y + 1)` and `τ_y := upperGauge C y x / (upperGauge C y x + 1)`
   with `0 < τ_x < τ_y < 1`, identifies the cone chord `p τ = (1 - τ) • u + τ • v` positively with
   `x` and `y`, and applies `birkhoff_crossRatio_chord_identity` unconditionally to prove:
   `birkhoffHilbertMetric C x y = (1 / 2 : ℝ) * Real.log (scalarCrossRatio 0 τ_x τ_y 1)`.
4. **Affine Chord Dichotomy (Incomparable Interior Chord vs. Comparable Infinite Ray)**:
   - When `1 < upperGauge C x y` and `1 < upperGauge C y x` (incomparable rays), the affine line
     `(1 - s) • x + s • y` intersects `frontier C` at finite parameters
     `s_a = -(1 / (M₂ - 1)) < 0 < 1 < s_b = M₁ / (M₁ - 1)` and
     `birkhoffHilbertMetric C x y = (1 / 2 : ℝ) * Real.log (scalarCrossRatio s_a 0 1 s_b)`.
   - When `upperGauge C x y ≤ 1` (`coneLE C x y`), the forward affine ray `(1 - s) • x + s • y`
     (`0 ≤ s`) remains inside `C` for all `s ≥ 0`.

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

noncomputable section

namespace InfoGeometry.Canonical.BirkhoffHilbertChordSectorClosure

open Filter Set Metric
open InfoGeometry.Projective.GeneralHilbertConeMetric
open InfoGeometry.Erlangen.BirkhoffHilbertConeMetric

section ArbitraryConeEndpoints

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- Left extremal boundary ray along the 2-plane spanned by `x, y ∈ interior C`:
`u := M(y, x) • x - y`. -/
def extremalRayLeft (C : ProperCone ℝ E) (x y : E) : E :=
  upperGauge C y x • x - y

/-- Right extremal boundary ray along the 2-plane spanned by `x, y ∈ interior C`:
`v := M(x, y) • y - x`. -/
def extremalRayRight (C : ProperCone ℝ E) (x y : E) : E :=
  upperGauge C x y • y - x

omit [Nontrivial E] in
theorem extremalRayLeft_mem (C : ProperCone ℝ E)
    {x : E} (hx : x ∈ interior (C : Set E)) (y : E) :
    extremalRayLeft C x y ∈ C :=
  coneLE_upperGauge_of_mem_interior C hx

omit [Nontrivial E] in
theorem extremalRayRight_mem (C : ProperCone ℝ E)
    (x : E) {y : E} (hy : y ∈ interior (C : Set E)) :
    extremalRayRight C x y ∈ C :=
  coneLE_upperGauge_of_mem_interior C hy

/-- Strict product bound `1 < M(x, y) * M(y, x)` for any two distinct interior rays of a salient
proper cone. -/
theorem one_lt_upperGauge_mul (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ x = c • y) :
    1 < upperGauge C x y * upperGauge C y x := by
  let M₁ : ℝ := upperGauge C x y
  let M₂ : ℝ := upperGauge C y x
  have hM₁_pos : 0 < M₁ := upperGauge_pos_of_mem_interior C hC hx hy
  have hM₂_pos : 0 < M₂ := upperGauge_pos_of_mem_interior C hC hy hx
  have hu : M₂ • x - y ∈ C := extremalRayLeft_mem C hx y
  have hv : M₁ • y - x ∈ C := extremalRayRight_mem C x hy
  have hcomb : (M₁ * M₂ - 1) • x ∈ C := by
    have hmul : M₁ • (M₂ • x - y) + (M₁ • y - x) ∈ C :=
      C.add_mem (C.smul_mem hu hM₁_pos.le) hv
    have heq : M₁ • (M₂ • x - y) + (M₁ • y - x) = (M₁ * M₂ - 1) • x := by
      module
    rwa [heq] at hmul
  have hx_mem : x ∈ C := interior_subset hx
  have hx_ne : x ≠ 0 := interior_mem_ne_zero_of_salient C hC hx
  have hge : 1 ≤ M₁ * M₂ := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < 1 - M₁ * M₂ := sub_pos.mpr hlt
    have hvec_mem : (1 - M₁ * M₂) • x ∈ C := C.smul_mem hx_mem hpos.le
    have hvec_ne : (1 - M₁ * M₂) • x ≠ 0 := smul_ne_zero hpos.ne' hx_ne
    have hneg_mem : -((1 - M₁ * M₂) • x) ∈ C := by
      have heq : -((1 - M₁ * M₂) • x) = (M₁ * M₂ - 1) • x := by module
      rwa [heq]
    exact hC _ hvec_mem hvec_ne hneg_mem
  rcases lt_or_eq_of_le hge with hgt | heq1
  · exact hgt
  · exfalso
    have hv_neg : -(M₁ • y - x) ∈ C := by
      have hsc : M₁ • (M₂ • x - y) ∈ C := C.smul_mem hu hM₁_pos.le
      have heq : M₁ • (M₂ • x - y) = (M₁ * M₂ - 1) • x - (M₁ • y - x) := by module
      rw [heq, heq1, sub_self, zero_smul, zero_sub] at hsc
      exact hsc
    have hv_zero : M₁ • y - x = 0 := by
      by_contra hv_ne
      exact hC _ hv hv_ne hv_neg
    exact hray ⟨M₁, hM₁_pos, (sub_eq_zero.mp hv_zero).symm⟩

omit [Nontrivial E] in
private lemma distinct_ray_symm {x y : E}
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ x = c • y) :
    ¬ ∃ c : ℝ, 0 < c ∧ y = c • x := by
  rintro ⟨c, hc, hy⟩
  apply hray
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  rw [hy, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

theorem extremalRayLeft_ne_zero (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ x = c • y) :
    extremalRayLeft C x y ≠ 0 := by
  intro hz
  have hM₂ : 0 < upperGauge C y x := upperGauge_pos_of_mem_interior C hC hy hx
  have hxy : upperGauge C y x • x = y := sub_eq_zero.mp hz
  exact distinct_ray_symm hray ⟨upperGauge C y x, hM₂, hxy.symm⟩

theorem extremalRayRight_ne_zero (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ x = c • y) :
    extremalRayRight C x y ≠ 0 := by
  intro hz
  have hM₁ : 0 < upperGauge C x y := upperGauge_pos_of_mem_interior C hC hx hy
  have hyx : upperGauge C x y • y = x := sub_eq_zero.mp hz
  exact hray ⟨upperGauge C x y, hM₁, hyx.symm⟩

/-- Every extremal ray `M(y, x) • x - y` lies on the topological boundary (`frontier`) of `C`:
it belongs to `C`, yet cannot belong to `interior C` by infimality of `upperGauge C y x`. -/
theorem extremalRayLeft_mem_frontier (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E)) :
    extremalRayLeft C x y ∈ frontier (C : Set E) := by
  rw [C.isClosed.frontier_eq]
  refine ⟨extremalRayLeft_mem C hx y, fun hint => ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  have hM₂ : 0 < upperGauge C y x := upperGauge_pos_of_mem_interior C hC hy hx
  have hx_ne : x ≠ 0 := interior_mem_ne_zero_of_salient C hC hx
  have hx_norm : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  let ε : ℝ := min (upperGauge C y x / 2) (δ / (2 * ‖x‖))
  have hε_pos : 0 < ε := lt_min (by positivity) (by positivity)
  have hball_mem : extremalRayLeft C x y - ε • x ∈ Metric.ball (extremalRayLeft C x y) δ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hε_pos]
    have hε_le : ε ≤ δ / (2 * ‖x‖) := min_le_right _ _
    calc
      ε * ‖x‖ ≤ (δ / (2 * ‖x‖)) * ‖x‖ := mul_le_mul_of_nonneg_right hε_le (norm_nonneg x)
      _ = δ / 2 := by
        have hx0 : ‖x‖ ≠ 0 := hx_norm.ne'
        field_simp [hx0]
      _ < δ := half_lt_self hδ
  have hmemC : (upperGauge C y x - ε) • x - y ∈ C := by
    have heq : (upperGauge C y x - ε) • x - y = extremalRayLeft C x y - ε • x := by
      simp only [extremalRayLeft]
      module
    rw [heq]
    exact hball hball_mem
  have hnonneg : 0 ≤ upperGauge C y x - ε := by
    have hε_le : ε ≤ upperGauge C y x / 2 := min_le_left _ _
    linarith
  have hle : upperGauge C y x ≤ upperGauge C y x - ε :=
    upperGauge_le_of_feasible C y x ⟨hnonneg, hmemC⟩
  linarith

omit [Nontrivial E] in
private lemma positive_smul_mem_frontier (C : ProperCone ℝ E)
    {z : E} (hz : z ∈ frontier (C : Set E)) {c : ℝ} (hc : 0 < c) :
    c • z ∈ frontier (C : Set E) := by
  rw [C.isClosed.frontier_eq] at hz ⊢
  refine ⟨C.smul_mem hz.1 hc.le, fun hint => hz.2 ?_⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint ⊢
  obtain ⟨δ, hδ, hball⟩ := hint
  refine ⟨c⁻¹ * δ, mul_pos (inv_pos.mpr hc) hδ, fun w hw => ?_⟩
  have hball' : c • w ∈ Metric.ball (c • z) δ := by
    rw [Metric.mem_ball, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    rw [Metric.mem_ball, dist_eq_norm] at hw
    calc
      c * ‖w - z‖ < c * (c⁻¹ * δ) := mul_lt_mul_of_pos_left hw hc
      _ = δ := by rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have hwC := C.smul_mem (hball hball') (inv_pos.mpr hc).le
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at hwC

theorem extremalRayRight_mem_frontier (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E)) :
    extremalRayRight C x y ∈ frontier (C : Set E) := by
  simpa [extremalRayRight, extremalRayLeft] using extremalRayLeft_mem_frontier C hC hy hx

/-- Shared helper proving `0 ≤ α` for `α • extremalRayLeft C x y + β • extremalRayRight C x y ∈ C`. -/
private lemma extremalRays_fst_nonneg (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ x = c • y)
    {α β : ℝ} (hw : α • extremalRayLeft C x y + β • extremalRayRight C x y ∈ C) :
    0 ≤ α := by
  by_contra hα_neg
  push Not at hα_neg
  let u : E := extremalRayLeft C x y
  let v : E := extremalRayRight C x y
  have hu : u ∈ C := extremalRayLeft_mem C hx y
  have hv : v ∈ C := extremalRayRight_mem C x hy
  have hu_ne : u ≠ 0 := extremalRayLeft_ne_zero C hC hx hy hray
  rcases le_or_gt β 0 with hβ_le | hβ_pos
  · have hw_zero : α • u + β • v = 0 := by
      by_contra hw_ne
      have hneg : -(α • u + β • v) ∈ C := by
        have hrew : -(α • u + β • v) = (-α) • u + (-β) • v := by module
        rw [hrew]
        exact C.add_mem (C.smul_mem hu (neg_nonneg.mpr hα_neg.le))
          (C.smul_mem hv (neg_nonneg.mpr hβ_le))
      exact hC _ hw hw_ne hneg
    have hαu_neg : -((-α) • u) ∈ C := by
      have hrew : -((-α) • u) = (-β) • v := by
        have hz : α • u + β • v = 0 := hw_zero
        calc
          -((-α) • u) = α • u := by module
          _ = α • u + β • v - β • v := by module
          _ = (-β) • v := by rw [hz]; module
      rw [hrew]
      exact C.smul_mem hv (neg_nonneg.mpr hβ_le)
    have hαu_mem : (-α) • u ∈ C := C.smul_mem hu (neg_nonneg.mpr hα_neg.le)
    have hαu_ne : (-α) • u ≠ 0 := smul_ne_zero (neg_pos.mpr hα_neg).ne' hu_ne
    exact hC _ hαu_mem hαu_ne hαu_neg
  · let M₁ : ℝ := upperGauge C x y
    let M₂ : ℝ := upperGauge C y x
    have hM₁ : 0 < M₁ := upperGauge_pos_of_mem_interior C hC hx hy
    have hM₂ : 0 < M₂ := upperGauge_pos_of_mem_interior C hC hy hx
    let P : ℝ := β - α * M₂
    let Q : ℝ := β * M₁ - α
    have hP : 0 < P := by
      dsimp [P]
      have : α * M₂ < 0 := mul_neg_of_neg_of_pos hα_neg hM₂
      linarith
    have hQ : 0 < Q := by
      dsimp [Q]
      have : 0 < β * M₁ := mul_pos hβ_pos hM₁
      linarith
    have hw_xy : α • u + β • v = Q • y - P • x := by
      dsimp [u, v, extremalRayLeft, extremalRayRight, M₁, M₂, P, Q]
      module
    have hfeas : coneLE C x ((Q / P) • y) := by
      change (Q / P) • y - x ∈ C
      have hscaled : P⁻¹ • (Q • y - P • x) ∈ C := by
        rw [← hw_xy]
        exact C.smul_mem hw (inv_pos.mpr hP).le
      have hrew : P⁻¹ • (Q • y - P • x) = (Q / P) • y - x := by
        rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hP.ne', one_smul, inv_mul_eq_div]
      rwa [← hrew]
    have hbound : M₁ ≤ Q / P := upperGauge_le_of_feasible C x y ⟨(div_pos hQ hP).le, hfeas⟩
    have hmul_le : M₁ * P ≤ Q := (le_div_iff₀ hP).mp hbound
    have hprod_le : 0 ≤ α * (M₁ * M₂ - 1) := by
      dsimp [P, Q] at hmul_le
      linarith
    have hgt1 : 0 < M₁ * M₂ - 1 := sub_pos.mpr (one_lt_upperGauge_mul C hC hx hy hray)
    have hprod_neg : α * (M₁ * M₂ - 1) < 0 := mul_neg_of_neg_of_pos hα_neg hgt1
    linarith

/-- **Unconditional Derivation of the Two-Ray Sector Hypothesis**:
For any two distinct interior rays `x, y ∈ interior C` of a salient proper cone, the extremal
boundary rays `u = M(y, x) • x - y` and `v = M(x, y) • y - x` automatically satisfy the
nonnegative cone-sector condition `∀ α β, α • u + β • v ∈ C → 0 ≤ α ∧ 0 ≤ β`. -/
theorem extremalRays_twoRay_sector (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ x = c • y) :
    ∀ α β : ℝ, α • extremalRayLeft C x y + β • extremalRayRight C x y ∈ C →
      0 ≤ α ∧ 0 ≤ β := by
  intro α β hw
  refine ⟨extremalRays_fst_nonneg C hC hx hy hray hw, ?_⟩
  have hw_swap : β • extremalRayLeft C y x + α • extremalRayRight C y x ∈ C := by
    change β • extremalRayRight C x y + α • extremalRayLeft C x y ∈ C
    rwa [add_comm]
  exact extremalRays_fst_nonneg C hC hy hx (distinct_ray_symm hray) hw_swap

/-- The two extremal boundary rays are linearly independent whenever `x, y` lie on distinct rays. -/
theorem extremalRays_linearIndependent (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ x = c • y) :
    LinearIndependent ℝ ![extremalRayLeft C x y, extremalRayRight C x y] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  have hmem_pos : c 0 • extremalRayLeft C x y + c 1 • extremalRayRight C x y ∈ C := by
    rw [hc]
    exact C.zero_mem
  have hmem_neg : (-c 0) • extremalRayLeft C x y + (-c 1) • extremalRayRight C x y ∈ C := by
    have hz : (-c 0) • extremalRayLeft C x y + (-c 1) • extremalRayRight C x y = 0 := by
      calc
        (-c 0) • extremalRayLeft C x y + (-c 1) • extremalRayRight C x y =
            -(c 0 • extremalRayLeft C x y + c 1 • extremalRayRight C x y) := by module
        _ = 0 := by rw [hc, neg_zero]
    rw [hz]
    exact C.zero_mem
  have hpos := extremalRays_twoRay_sector C hC hx hy hray (c 0) (c 1) hmem_pos
  have hneg := extremalRays_twoRay_sector C hC hx hy hray (-c 0) (-c 1) hmem_neg
  have hc0 : c 0 = 0 := by linarith [hpos.1, hneg.1]
  have hc1 : c 1 = 0 := by linarith [hpos.2, hneg.2]
  fin_cases i
  · exact hc0
  · exact hc1

omit [Nontrivial E] in
private lemma chord_projective_identity_x (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (u v x y : E)
    (hu : u = M₂ • x - y) (hv : v = M₁ • y - x) :
    let τ_x : ℝ := 1 / (M₁ + 1)
    ((1 - τ_x) / (1 - 0)) • u + ((τ_x - 0) / (1 - 0)) • v =
      ((M₁ * M₂ - 1) / (M₁ + 1)) • x := by
  dsimp only
  have h1 : M₁ + 1 ≠ 0 := by linarith [hM₁]
  rw [hu, hv]
  simp only [sub_zero, div_one]
  have hcx : (1 - 1 / (M₁ + 1)) * M₂ - 1 / (M₁ + 1) = (M₁ * M₂ - 1) / (M₁ + 1) := by
    field_simp [h1]
    ring
  have hcy : -(1 - 1 / (M₁ + 1)) + (1 / (M₁ + 1)) * M₁ = 0 := by
    field_simp [h1]
    ring
  calc
    (1 - 1 / (M₁ + 1)) • (M₂ • x - y) + (1 / (M₁ + 1)) • (M₁ • y - x) =
        ((1 - 1 / (M₁ + 1)) * M₂ - 1 / (M₁ + 1)) • x +
          (-(1 - 1 / (M₁ + 1)) + (1 / (M₁ + 1)) * M₁) • y := by module
    _ = ((M₁ * M₂ - 1) / (M₁ + 1)) • x + (0 : ℝ) • y := by rw [hcx, hcy]
    _ = ((M₁ * M₂ - 1) / (M₁ + 1)) • x := by rw [zero_smul, add_zero]

omit [Nontrivial E] in
private lemma chord_projective_identity_y (M₁ M₂ : ℝ) (hM₂ : 0 < M₂) (u v x y : E)
    (hu : u = M₂ • x - y) (hv : v = M₁ • y - x) :
    let τ_y : ℝ := M₂ / (M₂ + 1)
    ((1 - τ_y) / (1 - 0)) • u + ((τ_y - 0) / (1 - 0)) • v =
      ((M₁ * M₂ - 1) / (M₂ + 1)) • y := by
  dsimp only
  have h2 : M₂ + 1 ≠ 0 := by linarith [hM₂]
  rw [hu, hv]
  simp only [sub_zero, div_one]
  have hcx : (1 - M₂ / (M₂ + 1)) * M₂ - M₂ / (M₂ + 1) = 0 := by
    field_simp [h2]
    ring
  have hcy : -(1 - M₂ / (M₂ + 1)) + (M₂ / (M₂ + 1)) * M₁ = (M₁ * M₂ - 1) / (M₂ + 1) := by
    field_simp [h2]
    ring
  calc
    (1 - M₂ / (M₂ + 1)) • (M₂ • x - y) + (M₂ / (M₂ + 1)) • (M₁ • y - x) =
        ((1 - M₂ / (M₂ + 1)) * M₂ - M₂ / (M₂ + 1)) • x +
          (-(1 - M₂ / (M₂ + 1)) + (M₂ / (M₂ + 1)) * M₁) • y := by module
    _ = (0 : ℝ) • x + ((M₁ * M₂ - 1) / (M₂ + 1)) • y := by rw [hcx, hcy]
    _ = ((M₁ * M₂ - 1) / (M₂ + 1)) • y := by rw [zero_smul, zero_add]

/-- **Unconditional Birkhoff–Hilbert Cross-Ratio Chord Formula for Arbitrary Distinct Interior Rays**:
Given any salient proper cone `C` and ANY two distinct interior rays `x, y ∈ interior C`, this
derives both extremal boundary rays `u, v ∈ frontier C` and the exact projective chord parameters
`0 < τ_x < τ_y < 1` without assuming the two-ray sector hypothesis or endpoint incomparability,
establishing `d_C(x, y) = (1 / 2) * log [0, τ_x; τ_y, 1]`. -/
theorem birkhoffHilbertMetric_arbitrary_endpoints_projective_chord (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ x = c • y) :
    let u := extremalRayLeft C x y
    let v := extremalRayRight C x y
    let τ_x := 1 / (upperGauge C x y + 1)
    let τ_y := upperGauge C y x / (upperGauge C y x + 1)
    let p : ℝ → E := fun τ => (1 - τ) • u + τ • v
    u ∈ frontier (C : Set E) ∧ v ∈ frontier (C : Set E) ∧
      0 < τ_x ∧ τ_x < τ_y ∧ τ_y < 1 ∧
      (∃ cx : ℝ, 0 < cx ∧ p τ_x = cx • x) ∧ (∃ cy : ℝ, 0 < cy ∧ p τ_y = cy • y) ∧
      birkhoffHilbertMetric C x y =
        (1 / 2 : ℝ) * Real.log (scalarCrossRatio 0 τ_x τ_y 1) := by
  let M₁ : ℝ := upperGauge C x y
  let M₂ : ℝ := upperGauge C y x
  let u : E := extremalRayLeft C x y
  let v : E := extremalRayRight C x y
  let τ_x : ℝ := 1 / (M₁ + 1)
  let τ_y : ℝ := M₂ / (M₂ + 1)
  let p : ℝ → E := fun τ => (1 - τ) • u + τ • v
  have hM₁ : 0 < M₁ := upperGauge_pos_of_mem_interior C hC hx hy
  have hM₂ : 0 < M₂ := upperGauge_pos_of_mem_interior C hC hy hx
  have hprod : 1 < M₁ * M₂ := one_lt_upperGauge_mul C hC hx hy hray
  have h1 : 0 < M₁ + 1 := by linarith
  have h2 : 0 < M₂ + 1 := by linarith
  have h0x : 0 < τ_x := div_pos zero_lt_one h1
  have hxy : τ_x < τ_y := by
    dsimp [τ_x, τ_y]
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith
  have hy1 : τ_y < 1 := by
    dsimp [τ_y]
    exact (div_lt_one h2).mpr (by linarith)
  have hcx_pos : 0 < (M₁ * M₂ - 1) / (M₁ + 1) := div_pos (sub_pos.mpr hprod) h1
  have hcy_pos : 0 < (M₁ * M₂ - 1) / (M₂ + 1) := div_pos (sub_pos.mpr hprod) h2
  have hpx : p τ_x = ((M₁ * M₂ - 1) / (M₁ + 1)) • x := by
    have hpx0 := chord_projective_identity_x M₁ M₂ hM₁ u v x y rfl rfl
    simp only [p, τ_x, sub_zero, div_one] at hpx0 ⊢
    exact hpx0
  have hpy : p τ_y = ((M₁ * M₂ - 1) / (M₂ + 1)) • y := by
    have hpy0 := chord_projective_identity_y M₁ M₂ hM₂ u v x y rfl rfl
    simp only [p, τ_y, sub_zero, div_one] at hpy0 ⊢
    exact hpy0
  have hchord := birkhoff_crossRatio_chord_identity C
    (extremalRayLeft_mem C hx y) (extremalRayRight_mem C x hy)
    (extremalRays_twoRay_sector C hC hx hy hray) h0x hxy hy1
  have hp_eq : birkhoffHilbertMetric C (p τ_x) (p τ_y) =
      (1 / 2 : ℝ) * Real.log (scalarCrossRatio 0 τ_x τ_y 1) := by
    simpa [p, sub_zero, div_one] using hchord
  have hproj : birkhoffHilbertMetric C (p τ_x) (p τ_y) = birkhoffHilbertMetric C x y := by
    rw [hpx, hpy]
    exact birkhoffHilbertMetric_projective C
      ((M₁ * M₂ - 1) / (M₁ + 1)) ((M₁ * M₂ - 1) / (M₂ + 1)) hcx_pos hcy_pos x y
  refine ⟨extremalRayLeft_mem_frontier C hC hx hy, extremalRayRight_mem_frontier C hC hx hy,
    h0x, hxy, hy1, ⟨(M₁ * M₂ - 1) / (M₁ + 1), hcx_pos, hpx⟩,
    ⟨(M₁ * M₂ - 1) / (M₂ + 1), hcy_pos, hpy⟩, ?_⟩
  exact hproj.symm.trans hp_eq

/-- **Affine Chord Formula for Incomparable Rays (`1 < M(x, y)` and `1 < M(y, x)`)**:
When neither endpoint dominates the other in the cone order, the affine segment `(1 - s) • x + s • y`
intersects `frontier C` at finite affine parameters `s_a = -(1 / (M₂ - 1)) < 0` and
`s_b = M₁ / (M₁ - 1) > 1`, and `d_C(x, y) = (1 / 2) * log [s_a, 0; 1, s_b]`. -/
theorem birkhoffHilbertMetric_affine_chord_of_incomparable (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ x = c • y)
    (hM₁_gt : 1 < upperGauge C x y) (hM₂_gt : 1 < upperGauge C y x) :
    let M₁ := upperGauge C x y
    let M₂ := upperGauge C y x
    let s_a : ℝ := -(1 / (M₂ - 1))
    let s_b : ℝ := M₁ / (M₁ - 1)
    let q : ℝ → E := fun s => (1 - s) • x + s • y
    s_a < 0 ∧ (1 : ℝ) < s_b ∧
      q s_a ∈ frontier (C : Set E) ∧ q s_b ∈ frontier (C : Set E) ∧
      birkhoffHilbertMetric C x y =
        (1 / 2 : ℝ) * Real.log (scalarCrossRatio s_a 0 1 s_b) := by
  let M₁ : ℝ := upperGauge C x y
  let M₂ : ℝ := upperGauge C y x
  let s_a : ℝ := -(1 / (M₂ - 1))
  let s_b : ℝ := M₁ / (M₁ - 1)
  let q : ℝ → E := fun s => (1 - s) • x + s • y
  have h1 : 0 < M₁ - 1 := sub_pos.mpr hM₁_gt
  have h2 : 0 < M₂ - 1 := sub_pos.mpr hM₂_gt
  have hsa_neg : s_a < 0 := neg_neg_of_pos (div_pos zero_lt_one h2)
  have hsb_gt : 1 < s_b := (one_lt_div h1).mpr (by linarith)
  have hqa_eq : q s_a = (M₂ - 1)⁻¹ • extremalRayLeft C x y := by
    dsimp [q, s_a, extremalRayLeft, M₂]
    have h2ne : M₂ - 1 ≠ 0 := h2.ne'
    have hcx : 1 - -(1 / (M₂ - 1)) = (M₂ - 1)⁻¹ * M₂ := by field_simp [h2ne]; ring
    have hcy : -(1 / (M₂ - 1)) = -((M₂ - 1)⁻¹) := by ring
    rw [smul_sub, smul_smul, hcx, hcy]
    module
  have hqb_eq : q s_b = (M₁ - 1)⁻¹ • extremalRayRight C x y := by
    dsimp [q, s_b, extremalRayRight, M₁]
    have h1ne : M₁ - 1 ≠ 0 := h1.ne'
    have hcx : 1 - M₁ / (M₁ - 1) = -((M₁ - 1)⁻¹) := by field_simp [h1ne]; ring
    have hcy : M₁ / (M₁ - 1) = (M₁ - 1)⁻¹ * M₁ := by field_simp [h1ne]
    rw [smul_sub, smul_smul, hcx, hcy]
    module
  have hqa_front : q s_a ∈ frontier (C : Set E) := by
    rw [hqa_eq]
    exact positive_smul_mem_frontier C (extremalRayLeft_mem_frontier C hC hx hy) (inv_pos.mpr h2)
  have hqb_front : q s_b ∈ frontier (C : Set E) := by
    rw [hqb_eq]
    exact positive_smul_mem_frontier C (extremalRayRight_mem_frontier C hC hx hy) (inv_pos.mpr h1)
  have hsec_aff : ∀ α β : ℝ, α • q s_a + β • q s_b ∈ C → 0 ≤ α ∧ 0 ≤ β := by
    intro α β hmem
    rw [hqa_eq, hqb_eq, smul_smul, smul_smul] at hmem
    have hraw := extremalRays_twoRay_sector C hC hx hy hray
      (α * (M₂ - 1)⁻¹) (β * (M₁ - 1)⁻¹) hmem
    refine ⟨?_, ?_⟩
    · exact nonneg_of_mul_nonneg_left hraw.1 (inv_pos.mpr h2)
    · exact nonneg_of_mul_nonneg_left hraw.2 (inv_pos.mpr h1)
  have hchord := birkhoff_crossRatio_chord_identity C
    (by rw [hqa_eq]; exact C.smul_mem (extremalRayLeft_mem C hx y) (inv_pos.mpr h2).le)
    (by rw [hqb_eq]; exact C.smul_mem (extremalRayRight_mem C x hy) (inv_pos.mpr h1).le)
    hsec_aff hsa_neg zero_lt_one hsb_gt
  have haff0 : ((s_b - 0) / (s_b - s_a)) • q s_a + ((0 - s_a) / (s_b - s_a)) • q s_b = x := by
    have hden : s_b - s_a ≠ 0 := by linarith
    have h1ne : M₁ - 1 ≠ 0 := h1.ne'
    have h2ne : M₂ - 1 ≠ 0 := h2.ne'
    have hx_c : ((s_b - 0) / (s_b - s_a)) * (1 - s_a) + ((0 - s_a) / (s_b - s_a)) * (1 - s_b) = 1 := by
      field_simp [hden, h1ne, h2ne]
      ring
    have hy_c : ((s_b - 0) / (s_b - s_a)) * s_a + ((0 - s_a) / (s_b - s_a)) * s_b = 0 := by
      field_simp [hden, h1ne, h2ne]
      ring
    dsimp [q]
    calc
      ((s_b - 0) / (s_b - s_a)) • ((1 - s_a) • x + s_a • y) +
          ((0 - s_a) / (s_b - s_a)) • ((1 - s_b) • x + s_b • y) =
          (((s_b - 0) / (s_b - s_a)) * (1 - s_a) + ((0 - s_a) / (s_b - s_a)) * (1 - s_b)) • x +
          (((s_b - 0) / (s_b - s_a)) * s_a + ((0 - s_a) / (s_b - s_a)) * s_b) • y := by module
      _ = (1 : ℝ) • x + (0 : ℝ) • y := by rw [hx_c, hy_c]
      _ = x := by rw [one_smul, zero_smul, add_zero]
  have haff1 : ((s_b - 1) / (s_b - s_a)) • q s_a + ((1 - s_a) / (s_b - s_a)) • q s_b = y := by
    have hden : s_b - s_a ≠ 0 := by linarith
    have h1ne : M₁ - 1 ≠ 0 := h1.ne'
    have h2ne : M₂ - 1 ≠ 0 := h2.ne'
    have hx_c : ((s_b - 1) / (s_b - s_a)) * (1 - s_a) + ((1 - s_a) / (s_b - s_a)) * (1 - s_b) = 0 := by
      field_simp [hden, h1ne, h2ne]
      ring
    have hy_c : ((s_b - 1) / (s_b - s_a)) * s_a + ((1 - s_a) / (s_b - s_a)) * s_b = 1 := by
      field_simp [hden, h1ne, h2ne]
      ring
    dsimp [q]
    calc
      ((s_b - 1) / (s_b - s_a)) • ((1 - s_a) • x + s_a • y) +
          ((1 - s_a) / (s_b - s_a)) • ((1 - s_b) • x + s_b • y) =
          (((s_b - 1) / (s_b - s_a)) * (1 - s_a) + ((1 - s_a) / (s_b - s_a)) * (1 - s_b)) • x +
          (((s_b - 1) / (s_b - s_a)) * s_a + ((1 - s_a) / (s_b - s_a)) * s_b) • y := by module
      _ = (0 : ℝ) • x + (1 : ℝ) • y := by rw [hx_c, hy_c]
      _ = y := by rw [zero_smul, one_smul, zero_add]
  dsimp only at hchord
  rw [haff0, haff1] at hchord
  exact ⟨hsa_neg, hsb_gt, hqa_front, hqb_front, hchord⟩

omit [Nontrivial E] in
/-- **Affine Ray Permanence When `upperGauge C x y ≤ 1` (`coneLE C x y`)**:
In the comparable case `M(x, y) ≤ 1`, the affine ray `(1 - s) • x + s • y` (`0 ≤ s`) never
exits the cone `C` for any finite positive `s`. Thus a finite affine chord does not intersect `∂C`
beyond `y`; the extremal ray `v = M₁ • y - x` still exists in `frontier C` and corresponds to the
projective ray parameter `τ_b = 1` used by `birkhoffHilbertMetric_arbitrary_endpoints_projective_chord`. -/
theorem affine_ray_stays_in_cone_of_upperGauge_le_one (C : ProperCone ℝ E)
    {x y : E} (hx : x ∈ interior (C : Set E)) (hy : y ∈ interior (C : Set E))
    (hle : upperGauge C x y ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    (1 - s) • x + s • y ∈ C := by
  have hyx : y - x ∈ C := by
    have hmem : upperGauge C x y • y - x ∈ C := coneLE_upperGauge_of_mem_interior C hy
    have hnonneg : 0 ≤ 1 - upperGauge C x y := sub_nonneg.mpr hle
    have hsum : (upperGauge C x y • y - x) + (1 - upperGauge C x y) • y ∈ C :=
      C.add_mem hmem (C.smul_mem (interior_subset hy) hnonneg)
    have heq : (upperGauge C x y • y - x) + (1 - upperGauge C x y) • y = y - x := by module
    rwa [← heq]
  have hsplit : (1 - s) • x + s • y = x + s • (y - x) := by module
  rw [hsplit]
  exact C.add_mem (interior_subset hx) (C.smul_mem hyx hs)

end ArbitraryConeEndpoints

/-- Noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℝ` inherited cleanly via T16. -/
theorem birkhoff_sector_closure_matrix2_noncommutative :
    posMatA * posMatB ≠ posMatB * posMatA :=
  posMatA_mul_posMatB_ne

end InfoGeometry.Canonical.BirkhoffHilbertChordSectorClosure
