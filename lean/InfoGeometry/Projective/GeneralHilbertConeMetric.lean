/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Real.Basic

/-!
# Order gauges for a general proper cone

This is the order-theoretic starting point for the Hilbert projective metric.
The carrier is a Mathlib `ProperCone`, rather than the positive orthant.  This
file deliberately proves only consequences of the cone order and the infimum
definition; comparability and finiteness are separate hypotheses when a
logarithmic metric is introduced.
-/

noncomputable section

open scoped Pointwise

namespace InfoGeometry.Projective.GeneralHilbertConeMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The preorder induced by a proper cone: `x ≤C y` means `y - x ∈ C`. -/
def coneLE (C : ProperCone ℝ E) (x y : E) : Prop := y - x ∈ C

theorem coneLE_refl (C : ProperCone ℝ E) (x : E) : coneLE C x x := by
  simp [coneLE]

theorem coneLE_trans (C : ProperCone ℝ E) {x y z : E}
    (hxy : coneLE C x y) (hyz : coneLE C y z) : coneLE C x z := by
  change z - x ∈ C
  have hsum : (y - x) + (z - y) ∈ C := C.add_mem hxy hyz
  have heq : z - x = (y - x) + (z - y) := by abel
  rw [heq]
  exact hsum

/-- Salience of the cone upgrades its induced preorder to an order. -/
theorem coneLE_antisymm (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) {x y : E}
    (hxy : coneLE C x y) (hyx : coneLE C y x) : x = y := by
  by_contra hne
  have hnonzero : y - x ≠ 0 := by
    intro hzero
    apply hne
    exact (sub_eq_zero.mp hzero).symm
  have hyx' : -(y - x) ∈ C := by
    change x - y ∈ C at hyx
    simpa using hyx
  exact hC (y - x) hxy hnonzero hyx'

/-- The upper order gauge `inf {r ≥ 0 | x ≤C r • y}`.  When its feasible set
is empty, the `sInf` convention is Lean's real infimum convention; geometric
properties below explicitly establish nonemptiness when needed. -/
def upperGauge (C : ProperCone ℝ E) (x y : E) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ coneLE C x (r • y)}

/-- Simultaneous positive rescaling of both vectors leaves the order gauge
unchanged. This is the basic projective homogeneity law; positivity is used to
transport cone membership in both directions. -/
theorem upperGauge_common_scale (C : ProperCone ℝ E) (c : ℝ) (hc : 0 < c)
    (x y : E) :
    upperGauge C (c • x) (c • y) = upperGauge C x y := by
  let f : Set ℝ := {r | 0 ≤ r ∧ coneLE C (c • x) (r • (c • y))}
  let g : Set ℝ := {r | 0 ≤ r ∧ coneLE C x (r • y)}
  have hfg : f = g := by
    ext r
    constructor
    · rintro ⟨hr, hmem⟩
      refine ⟨hr, ?_⟩
      change r • (c • y) - c • x ∈ C at hmem
      have hfactor : r • (c • y) - c • x = c • (r • y - x) := by
        rw [smul_sub, smul_smul]
        module
      rw [hfactor] at hmem
      have hinv : c⁻¹ • (c • (r • y - x)) ∈ C :=
        C.smul_mem hmem (le_of_lt (inv_pos.mpr hc))
      have hbase : r • y - x ∈ C := by
        simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using hinv
      change r • y - x ∈ C
      exact hbase
    · rintro ⟨hr, hmem⟩
      refine ⟨hr, ?_⟩
      change r • y - x ∈ C at hmem
      have hscaled : c • (r • y - x) ∈ C := C.smul_mem hmem (le_of_lt hc)
      have hfactor : c • (r • y - x) = r • c • y - c • x := by
        module
      change r • c • y - c • x ∈ C
      rw [← hfactor]
      exact hscaled
  change sInf f = sInf g
  rw [hfg]

/-- Positive homogeneity in the first argument of the order gauge. The feasible
scales are exactly the positive rescalings of the original feasible set. -/
theorem upperGauge_scale_left (C : ProperCone ℝ E) (c : ℝ) (hc : 0 < c)
    (x y : E) :
    upperGauge C (c • x) y = c * upperGauge C x y := by
  let f : Set ℝ := {r | 0 ≤ r ∧ coneLE C (c • x) (r • y)}
  let g : Set ℝ := {r | 0 ≤ r ∧ coneLE C x (r • y)}
  have hfg : f = c • g := by
    ext r
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
    constructor
    · rintro ⟨hr, hmem⟩
      refine ⟨?_, ?_⟩
      · exact mul_nonneg (inv_nonneg.mpr hc.le) hr
      · change r • y - c • x ∈ C at hmem
        have hscaled : c⁻¹ • (r • y - c • x) ∈ C :=
          C.smul_mem hmem (le_of_lt (inv_pos.mpr hc))
        change (c⁻¹ * r) • y - x ∈ C
        simpa [smul_sub, smul_smul, inv_mul_cancel₀ hc.ne'] using hscaled
    · rintro ⟨hr, hmem⟩
      have hr0 : 0 ≤ r := by
        have hmul := mul_nonneg (le_of_lt hc) hr
        simpa [smul_eq_mul, mul_assoc, hc.ne'] using hmul
      refine ⟨hr0, ?_⟩
      change (c⁻¹ * r) • y - x ∈ C at hmem
      have hscaled : c • ((c⁻¹ * r) • y - x) ∈ C :=
        C.smul_mem hmem (le_of_lt hc)
      change r • y - c • x ∈ C
      simpa [smul_sub, smul_smul, mul_assoc, hc.ne'] using hscaled
  change sInf f = c * sInf g
  rw [hfg, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]

/-- Positive homogeneity in the second argument of the order gauge; scaling the
comparison ray inversely scales the least feasible coefficient. -/
theorem upperGauge_scale_right (C : ProperCone ℝ E) (c : ℝ) (hc : 0 < c)
    (x y : E) :
    upperGauge C x (c • y) = c⁻¹ * upperGauge C x y := by
  have hcancel : c • (c⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  calc
    upperGauge C x (c • y) = upperGauge C (c • (c⁻¹ • x)) (c • y) := by
      rw [hcancel]
    _ = upperGauge C (c⁻¹ • x) y := upperGauge_common_scale C c hc _ _
    _ = c⁻¹ * upperGauge C x y :=
      upperGauge_scale_left C c⁻¹ (inv_pos.mpr hc) x y

/-- Every vector is order-bounded above by a positive multiple of an interior
point of a proper cone.  This supplies the nonemptiness needed by the gauge,
rather than postulating a comparison witness as a theorem hypothesis. -/
theorem exists_cone_upper_bound_of_mem_interior (C : ProperCone ℝ E)
    {z y : E} (hz : z ∈ interior (C : Set E)) :
    ∃ r : ℝ, 0 ≤ r ∧ coneLE C y (r • z) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hz)
  let q : ℝ := ε / (2 * (‖y‖ + 1))
  have hden : 0 < 2 * (‖y‖ + 1) := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hqnorm : ‖q • y‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    dsimp [q]
    have hy : 0 ≤ ‖y‖ := norm_nonneg y
    field_simp
    nlinarith
  have hpoint : z - q • y ∈ C := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [sub_sub, norm_neg] using hqnorm
  let r : ℝ := q⁻¹
  have hr : 0 < r := inv_pos.mpr hq
  have hscaled : r • (z - q • y) ∈ C := C.smul_mem hpoint (le_of_lt hr)
  have hrewrite : r • (z - q • y) = r • z - y := by
    rw [smul_sub, smul_smul]
    have hmul : r * q = 1 := inv_mul_cancel₀ hq.ne'
    rw [hmul, one_smul]
  refine ⟨r, le_of_lt hr, ?_⟩
  change r • z - y ∈ C
  rw [← hrewrite]
  exact hscaled

/-- A salient cone with nonempty ambient vector content cannot have zero in its
interior: otherwise interior domination would place every vector and its
negative in the cone. -/
theorem interior_mem_ne_zero_of_salient (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    {x : E} (hx : x ∈ interior (C : Set E)) : x ≠ 0 := by
  intro hx0
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hv_neg : -v ∈ C := by
    obtain ⟨r, _, hle⟩ := exists_cone_upper_bound_of_mem_interior C
      (z := x) (y := v) (by simpa [hx0] using hx)
    change r • x - v ∈ C at hle
    simpa [hx0] using hle
  have hv_pos : v ∈ C := by
    obtain ⟨r, _, hle⟩ := exists_cone_upper_bound_of_mem_interior C
      (z := x) (y := -v) (by simpa [hx0] using hx)
    change r • x - -v ∈ C at hle
    simpa [hx0] using hle
  exact hC v hv_pos hv hv_neg

/-- The order gauge is strictly positive when both rays are represented by
interior points of a salient cone. Closedness excludes arbitrarily small
feasible scales, while interior domination supplies a nonempty feasible set. -/
theorem upperGauge_pos_of_mem_interior (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    {x y : E} (hx : x ∈ interior (C : Set E))
    (hy : y ∈ interior (C : Set E)) : 0 < upperGauge C x y := by
  let f : Set ℝ := {r | 0 ≤ r ∧ coneLE C x (r • y)}
  have hne : f.Nonempty := exists_cone_upper_bound_of_mem_interior C hy
  have hx_ne : x ≠ 0 := interior_mem_ne_zero_of_salient C hC hx
  have hx_mem : x ∈ C := interior_subset hx
  have hneg_not : -x ∉ C := hC x hx_mem hx_ne
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((C.isClosed.isOpen_compl).mem_nhds hneg_not)
  let δ : ℝ := ε / (2 * (‖y‖ + 1))
  have hden : 0 < 2 * (‖y‖ + 1) := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδnorm : ‖δ • y‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    dsimp [δ]
    have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
    field_simp
    nlinarith
  have h_lower : ∀ r ∈ f, δ ≤ r := by
    intro r hr
    by_contra hnot
    have hrlt : r < δ := lt_of_not_ge hnot
    have hrnorm : ‖r • y‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
      dsimp [δ] at hrlt ⊢
      have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
      have hratio : ‖y‖ / (2 * (‖y‖ + 1)) ≤ (1 / 2 : ℝ) := by
        have hsum : 0 < ‖y‖ + 1 := by positivity
        field_simp
        nlinarith
      calc
        r * ‖y‖ ≤ (ε / (2 * (‖y‖ + 1))) * ‖y‖ :=
          mul_le_mul_of_nonneg_right hrlt.le hy_nonneg
        _ = ε * (‖y‖ / (2 * (‖y‖ + 1))) := by ring
        _ ≤ ε / 2 := by nlinarith [mul_le_mul_of_nonneg_left hratio hε.le]
        _ < ε := by linarith
    have hnear : ‖(r • y - x) - -x‖ < ε := by
      simpa [sub_sub] using hrnorm
    have hball_mem : r • y - x ∈ Metric.ball (-x) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hnear
    have hnotC : r • y - x ∉ C := hball hball_mem
    exact hnotC hr.2
  change 0 < sInf f
  have hδle : δ ≤ sInf f := le_csInf hne h_lower
  exact lt_of_lt_of_le hδ hδle

/-- The upper order gauge is nonnegative whenever the comparison vector is an
interior point, because its feasible set is nonempty and consists of
nonnegative scalars. -/
theorem upperGauge_nonneg_of_mem_interior (C : ProperCone ℝ E) {x y : E}
    (hy : y ∈ interior (C : Set E)) : 0 ≤ upperGauge C x y := by
  let f : Set ℝ := {r | 0 ≤ r ∧ coneLE C x (r • y)}
  have hne : f.Nonempty := exists_cone_upper_bound_of_mem_interior C hy
  change 0 ≤ sInf f
  apply le_csInf hne
  intro r hr
  exact hr.1

theorem upperGauge_mono_left (C : ProperCone ℝ E) {x y z : E}
    (hxy : coneLE C x y) (hz : z ∈ interior (C : Set E)) :
    upperGauge C x z ≤ upperGauge C y z := by
  let fx : Set ℝ := {r | 0 ≤ r ∧ coneLE C x (r • z)}
  let fy : Set ℝ := {r | 0 ≤ r ∧ coneLE C y (r • z)}
  have hfx : BddBelow fx := ⟨0, fun r hr => hr.1⟩
  have hfy_nonempty : fy.Nonempty := exists_cone_upper_bound_of_mem_interior C hz
  have hfy_fx : fy ⊆ fx := by
    intro r hr
    exact ⟨hr.1, coneLE_trans C hxy hr.2⟩
  change sInf fx ≤ sInf fy
  apply le_csInf hfy_nonempty
  intro r hr
  exact csInf_le hfx (hfy_fx hr)

/-- Every feasible order bound is an upper bound for the infimum gauge. -/
theorem upperGauge_le_of_feasible (C : ProperCone ℝ E) (x y : E) {r : ℝ}
    (hr : 0 ≤ r ∧ coneLE C x (r • y)) : upperGauge C x y ≤ r := by
  let f : Set ℝ := {s | 0 ≤ s ∧ coneLE C x (s • y)}
  change sInf f ≤ r
  exact csInf_le ⟨0, fun s hs => hs.1⟩ hr

/-- On an interior ray of a salient cone, the order gauge of a point against
itself is exactly one. The lower bound is derived from salience; the feasible
scale one gives the upper bound. -/
theorem upperGauge_self_eq_one_of_mem_interior (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    {x : E} (hx : x ∈ interior (C : Set E)) : upperGauge C x x = 1 := by
  let f : Set ℝ := {r | 0 ≤ r ∧ coneLE C x (r • x)}
  have hx_ne : x ≠ 0 := interior_mem_ne_zero_of_salient C hC hx
  have hx_mem : x ∈ C := interior_subset hx
  have hnot_neg : -x ∉ C := hC x hx_mem hx_ne
  have h_lower : ∀ r ∈ f, 1 ≤ r := by
    intro r hr
    by_contra hnot
    have hrlt : r < 1 := lt_of_not_ge hnot
    have hmem : r • x - x ∈ C := hr.2
    have hfactor : r • x - x = (1 - r) • (-x) := by module
    rw [hfactor] at hmem
    have hpos : 0 < 1 - r := by linarith
    have hscaled : (1 - r)⁻¹ • ((1 - r) • (-x)) ∈ C :=
      C.smul_mem hmem (le_of_lt (inv_pos.mpr hpos))
    have hmul : (1 - r)⁻¹ * (1 - r) = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr (by linarith))
    have hneg : -x ∈ C := by simpa [smul_smul, hmul] using hscaled
    exact hnot_neg hneg
  have hone : 1 ∈ f := by
    refine ⟨by norm_num, ?_⟩
    change 1 • x - x ∈ C
    simp
  have hbound : BddBelow f := ⟨1, h_lower⟩
  change sInf f = 1
  apply le_antisymm
  · exact csInf_le hbound hone
  · exact le_csInf ⟨1, hone⟩ h_lower

/-- Feasible order bounds compose multiplicatively.  This is the algebraic
composition law underlying the triangle inequality for the Hilbert order gauge. -/
theorem coneLE_mul_feasible (C : ProperCone ℝ E) {x y z : E} {r s : ℝ}
    (hr : 0 ≤ r)
    (hxy : coneLE C x (r • y)) (hyz : coneLE C y (s • z)) :
    coneLE C x ((r * s) • z) := by
  change r • y - x ∈ C at hxy
  change s • z - y ∈ C at hyz
  change (r * s) • z - x ∈ C
  have hscaled : r • (s • z - y) ∈ C := C.smul_mem hyz hr
  have hsum : (r • y - x) + r • (s • z - y) ∈ C := C.add_mem hxy hscaled
  have hrewrite : (r • y - x) + r • (s • z - y) = (r * s) • z - x := by
    rw [smul_sub, smul_smul]
    module
  rw [← hrewrite]
  exact hsum

/-- The order gauge is bounded by the product of any two composable feasible
order bounds.  Taking infima of such bounds yields the usual submultiplicative
gauge inequality. -/
theorem upperGauge_le_mul_of_feasible (C : ProperCone ℝ E)
    (x y z : E) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hxy : coneLE C x (r • y)) (hyz : coneLE C y (s • z)) :
    upperGauge C x z ≤ r * s := by
  exact upperGauge_le_of_feasible C x z
    ⟨mul_nonneg hr hs, coneLE_mul_feasible C hr hxy hyz⟩

/-- Submultiplicativity of the order gauge.  Interior points provide the
nonempty feasible sets, and nonnegativity bounds them below; neither fact is
assumed as an opaque comparison witness. -/
theorem upperGauge_submultiplicative (C : ProperCone ℝ E) (x y z : E)
    (hy : y ∈ interior (C : Set E)) (hz : z ∈ interior (C : Set E)) :
    upperGauge C x z ≤ upperGauge C x y * upperGauge C y z := by
  let A : Set ℝ := {r | 0 ≤ r ∧ coneLE C x (r • y)}
  let B : Set ℝ := {s | 0 ≤ s ∧ coneLE C y (s • z)}
  let a := upperGauge C x y
  let b := upperGauge C y z
  have hA_nonempty : A.Nonempty := exists_cone_upper_bound_of_mem_interior C hy
  have hB_nonempty : B.Nonempty := exists_cone_upper_bound_of_mem_interior C hz
  have ha : 0 ≤ a := upperGauge_nonneg_of_mem_interior C hy
  have hb : 0 ≤ b := upperGauge_nonneg_of_mem_interior C hz
  change upperGauge C x z ≤ a * b
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let δ := min 1 (ε / (2 * (a + b + 1)))
  have hden : 0 < 2 * (a + b + 1) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hε hden)
  have hδ_one : δ ≤ 1 := min_le_left _ _
  have hδ_frac : δ ≤ ε / (2 * (a + b + 1)) := min_le_right _ _
  have hδ_bound : δ * (a + b + 1) ≤ ε := by
    have hsum : 0 < a + b + 1 := by positivity
    rw [div_eq_mul_inv] at hδ_frac
    have hmul := mul_le_mul_of_nonneg_right hδ_frac (le_of_lt hsum)
    field_simp at hmul ⊢
    nlinarith
  obtain ⟨r, hrA, hr_lt⟩ := exists_lt_of_csInf_lt hA_nonempty
    (lt_add_of_pos_right a hδ)
  obtain ⟨s, hsB, hs_lt⟩ := exists_lt_of_csInf_lt hB_nonempty
    (lt_add_of_pos_right b hδ)
  have hbound := upperGauge_le_mul_of_feasible C x y z hrA.1 hsB.1 hrA.2 hsB.2
  have hproduct : r * s ≤ (a + δ) * (b + δ) := by
    have hr' : r ≤ a + δ := le_of_lt hr_lt
    have hs' : s ≤ b + δ := le_of_lt hs_lt
    have h1 : 0 ≤ a + δ - r := sub_nonneg.mpr hr'
    have h2 : 0 ≤ b + δ - s := sub_nonneg.mpr hs'
    have h3 : 0 ≤ a + δ := by positivity
    nlinarith [mul_nonneg h1 (by positivity), mul_nonneg hrA.1 h2]
  have hexpand : (a + δ) * (b + δ) ≤ a * b + ε := by
    nlinarith [mul_nonneg hδ.le (by positivity : 0 ≤ a + b + 1)]
  exact hbound.trans (hproduct.trans hexpand)

/-- The order-theoretic Hilbert projective expression.  It becomes a real-valued
distance on mutually comparable rays when both order gauges are finite and
strictly positive. -/
def hilbertOrderDistance (C : ProperCone ℝ E) (x y : E) : ℝ :=
  Real.log (upperGauge C x y * upperGauge C y x)

/-- Nonnegativity of the Hilbert order-gauge distance on interior points.
It follows from submultiplicativity and the self-gauge identity. -/
theorem hilbertOrderDistance_nonneg (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    {x y : E} (hx : x ∈ interior (C : Set E))
    (hy : y ∈ interior (C : Set E)) :
    0 ≤ hilbertOrderDistance C x y := by
  have hself := upperGauge_self_eq_one_of_mem_interior C hC hx
  have hsub := upperGauge_submultiplicative C x y x hy hx
  have hprod : 1 ≤ upperGauge C x y * upperGauge C y x := by
    rw [hself] at hsub
    nlinarith [hsub]
  exact Real.log_nonneg hprod

theorem hilbertOrderDistance_symm (C : ProperCone ℝ E) (x y : E) :
    hilbertOrderDistance C x y = hilbertOrderDistance C y x := by
  simp [hilbertOrderDistance, mul_comm]

/-- The logarithmic order-gauge expression is invariant under a common
positive rescaling of its two representatives, hence depends only on their
projective rays. -/
theorem hilbertOrderDistance_common_scale (C : ProperCone ℝ E)
    (c : ℝ) (hc : 0 < c) (x y : E) :
    hilbertOrderDistance C (c • x) (c • y) = hilbertOrderDistance C x y := by
  simp only [hilbertOrderDistance, upperGauge_common_scale C c hc]

/-- Independent positive rescaling of either representative leaves the
Hilbert order-gauge distance unchanged, so the distance descends to rays. -/
theorem hilbertOrderDistance_projective (C : ProperCone ℝ E)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x y : E) :
    hilbertOrderDistance C (a • x) (b • y) = hilbertOrderDistance C x y := by
  have hprod :
      upperGauge C (a • x) (b • y) * upperGauge C (b • y) (a • x) =
        upperGauge C x y * upperGauge C y x := by
    rw [upperGauge_scale_left C a ha, upperGauge_scale_left C b hb,
      upperGauge_scale_right C b hb, upperGauge_scale_right C a ha]
    field_simp [ha.ne', hb.ne']
  simp only [hilbertOrderDistance]
  rw [hprod]

/-- Triangle inequality for the logarithmic order-gauge distance on the
interior of a nontrivial salient proper cone.  Positivity of every gauge is
derived from closedness and salience above, rather than supplied as a metric
axiom. -/
theorem hilbertOrderDistance_triangle (C : ProperCone ℝ E)
    (hC : C.toPointedCone.toConvexCone.Salient) [Nontrivial E]
    {x y z : E} (hx : x ∈ interior (C : Set E))
    (hy : y ∈ interior (C : Set E)) (hz : z ∈ interior (C : Set E)) :
    hilbertOrderDistance C x z ≤
      hilbertOrderDistance C x y + hilbertOrderDistance C y z := by
  have hxy : 0 < upperGauge C x y := upperGauge_pos_of_mem_interior C hC hx hy
  have hyx : 0 < upperGauge C y x := upperGauge_pos_of_mem_interior C hC hy hx
  have hyz : 0 < upperGauge C y z := upperGauge_pos_of_mem_interior C hC hy hz
  have hzy : 0 < upperGauge C z y := upperGauge_pos_of_mem_interior C hC hz hy
  have hxz : 0 < upperGauge C x z := upperGauge_pos_of_mem_interior C hC hx hz
  have hzx : 0 < upperGauge C z x := upperGauge_pos_of_mem_interior C hC hz hx
  have hforward := upperGauge_submultiplicative C x y z hy hz
  have hbackward := upperGauge_submultiplicative C z y x hy hx
  have hproduct : upperGauge C x z * upperGauge C z x ≤
      (upperGauge C x y * upperGauge C y x) *
        (upperGauge C y z * upperGauge C z y) := by
    calc
      upperGauge C x z * upperGauge C z x ≤
          (upperGauge C x y * upperGauge C y z) * upperGauge C z x :=
        mul_le_mul_of_nonneg_right hforward (le_of_lt hzx)
      _ ≤ (upperGauge C x y * upperGauge C y z) *
          (upperGauge C z y * upperGauge C y x) :=
        mul_le_mul_of_nonneg_left hbackward (le_of_lt (mul_pos hxy hyz))
      _ = (upperGauge C x y * upperGauge C y x) *
          (upperGauge C y z * upperGauge C z y) := by ring
  have hlog := Real.log_le_log (mul_pos hxz hzx) hproduct
  have hprod_eq : (upperGauge C x y * upperGauge C y z) *
      (upperGauge C z y * upperGauge C y x) =
      (upperGauge C x y * upperGauge C y x) *
        (upperGauge C y z * upperGauge C z y) := by ring
  have hsplit :
      Real.log ((upperGauge C x y * upperGauge C y z) *
          (upperGauge C z y * upperGauge C y x)) =
        Real.log (upperGauge C x y * upperGauge C y x) +
          Real.log (upperGauge C y z * upperGauge C z y) := by
    rw [hprod_eq, Real.log_mul (ne_of_gt (mul_pos hxy hyx))
      (ne_of_gt (mul_pos hyz hzy))]
  rw [← hprod_eq] at hlog
  rw [hsplit] at hlog
  simpa [hilbertOrderDistance] using hlog

end InfoGeometry.Projective.GeneralHilbertConeMetric
