/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.NormNum

/-!
# Two metric contractions of a common symplectic form

The contractions are the native forms `ω.compRight I` and `ω.compLeft K`.
For an involution reversing `ω`, preservation of the first contraction is
equivalent to anticommutation with `I`. Positivity alone only excludes
commutation. The general metric intertwiner has the ordered product `-K * I`;
identifying it with `I * K` requires the additional anticommutation law.

Every result states its actual algebraic hypotheses. No finite dimension,
manifold integrability, statistical model, or Clifford faithfulness is assumed
or constructed here.
-/

namespace InfoGeometry.Geometry.SymplecticMetricCompatibility

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A symplectic square-minus-one endomorphism is skew for the original form. -/
theorem complex_skew (ω : LinearMap.BilinForm ℝ E) {I : Module.End ℝ E}
    (hI : I * I = -1) (hωI : ∀ x y, ω (I x) (I y) = ω x y)
    (x y : E) : ω (I x) y = -ω x (I y) := by
  have hIy : I (I y) = -y := by
    simpa using congrArg (fun A : Module.End ℝ E => A y) hI
  have h := hωI x (I y)
  rw [hIy, map_neg] at h
  simpa only [neg_neg] using congrArg Neg.neg h

/-- An involution reversing a bilinear form is skew for that form. -/
theorem involution_skew (ω : LinearMap.BilinForm ℝ E) {K : Module.End ℝ E}
    (hK : K * K = 1) (hωK : ∀ x y, ω (K x) (K y) = -ω x y)
    (x y : E) : ω (K x) y = -ω x (K y) := by
  have hKy : K (K y) = y := by
    simpa using congrArg (fun A : Module.End ℝ E => A y) hK
  simpa only [hKy] using hωK x (K y)

/-- Alternation and complex compatibility make the right contraction symmetric. -/
theorem compRight_isSymm (ω : LinearMap.BilinForm ℝ E) (hAlt : ω.IsAlt)
    {I : Module.End ℝ E} (hI : I * I = -1)
    (hωI : ∀ x y, ω (I x) (I y) = ω x y) : (ω.compRight I).IsSymm := by
  refine ⟨fun x y => ?_⟩
  change ω x (I y) = ω y (I x)
  calc
    ω x (I y) = -ω (I x) y := by rw [complex_skew ω hI hωI, neg_neg]
    _ = ω y (I x) := hAlt.neg_eq (I x) y

/-- Alternation and para compatibility make the left contraction symmetric. -/
theorem compLeft_isSymm (ω : LinearMap.BilinForm ℝ E) (hAlt : ω.IsAlt)
    {K : Module.End ℝ E} (hK : K * K = 1)
    (hωK : ∀ x y, ω (K x) (K y) = -ω x y) : (ω.compLeft K).IsSymm := by
  refine ⟨fun x y => ?_⟩
  change ω (K x) y = ω (K y) x
  calc
    ω (K x) y = -ω x (K y) := involution_skew ω hK hωK x y
    _ = ω (K y) x := hAlt.neg_eq x (K y)

/-- Nondegeneracy survives right contraction by a square-minus-one map. -/
theorem compRight_nondegenerate (ω : LinearMap.BilinForm ℝ E)
    (hω : ω.Nondegenerate) {I : Module.End ℝ E} (hI : I * I = -1) :
    (ω.compRight I).Nondegenerate := by
  have hII (x : E) : I (I x) = -x := by
    simpa using congrArg (fun A : Module.End ℝ E => A x) hI
  constructor
  · intro x hx
    apply hω.1 x
    intro y
    simpa only [LinearMap.BilinForm.compRight_apply, map_neg, hII, neg_neg]
      using hx (-(I y))
  · intro x hx
    have hIx : I x = 0 := hω.2 (I x) hx
    have hz : -x = 0 := (hII x).symm.trans (by rw [hIx, map_zero])
    exact neg_eq_zero.mp hz

/-- Nondegeneracy survives left contraction by an involution. -/
theorem compLeft_nondegenerate (ω : LinearMap.BilinForm ℝ E)
    (hω : ω.Nondegenerate) {K : Module.End ℝ E} (hK : K * K = 1) :
    (ω.compLeft K).Nondegenerate := by
  have hKK (x : E) : K (K x) = x := by
    simpa using congrArg (fun A : Module.End ℝ E => A x) hK
  constructor
  · intro x hx
    have hKx : K x = 0 := hω.1 (K x) hx
    exact (hKK x).symm.trans (by rw [hKx, map_zero])
  · intro x hx
    apply hω.2 x
    intro y
    simpa only [LinearMap.BilinForm.compLeft_apply, hKK] using hx (K y)

/-- The missing condition is metric preservation, not positivity.
Only right separation, involutivity, and reversal of `ω` are needed here. -/
theorem isometry_iff_anticommute (ω : LinearMap.BilinForm ℝ E)
    (hω : ω.SeparatingRight) (I K : Module.End ℝ E) (hK : K * K = 1)
    (hωK : ∀ x y, ω (K x) (K y) = -ω x y) :
    (∀ x y, (ω.compRight I) (K x) (K y) = (ω.compRight I) x y) ↔
      I * K = -(K * I) := by
  have hKK (x : E) : K (K x) = x := by
    simpa using congrArg (fun A : Module.End ℝ E => A x) hK
  constructor
  · intro h
    apply LinearMap.ext
    intro y
    change I (K y) = -(K (I y))
    have hz : I (K y) + K (I y) = 0 := by
      apply hω
      intro x
      have hxy := h (K x) y
      change ω (K (K x)) (I (K y)) = ω (K x) (I y) at hxy
      rw [hKK, involution_skew ω hK hωK] at hxy
      rw [map_add, hxy, neg_add_cancel]
    apply eq_of_sub_eq_zero
    simpa only [sub_neg_eq_add] using hz
  · intro h x y
    have hy : I (K y) = -(K (I y)) := by
      simpa using congrArg (fun A : Module.End ℝ E => A y) h
    change ω (K x) (I (K y)) = ω x (I y)
    rw [hy, map_neg, hωK, neg_neg]

/-- The universally valid ordered comparison of the two metric contractions. -/
theorem metric_intertwiner (ω : LinearMap.BilinForm ℝ E)
    {I K : Module.End ℝ E} (hI : I * I = -1) (hK : K * K = 1)
    (hωI : ∀ x y, ω (I x) (I y) = ω x y) :
    (ω.compLeft K).compLeft (-(K * I)) = ω.compRight I := by
  have hKK (x : E) : K (K x) = x := by
    simpa using congrArg (fun A : Module.End ℝ E => A x) hK
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change ω (K (-(K (I x)))) y = ω x (I y)
  simp only [map_neg, LinearMap.neg_apply, hKK]
  rw [complex_skew ω hI hωI, neg_neg]

/-- Nondegeneracy identifies the comparison map uniquely, in its actual order. -/
theorem metric_intertwiner_unique (ω : LinearMap.BilinForm ℝ E)
    (hω : ω.Nondegenerate) {I K : Module.End ℝ E}
    (hI : I * I = -1) (hK : K * K = 1)
    (hωI : ∀ x y, ω (I x) (I y) = ω x y) (T : Module.End ℝ E) :
    (ω.compLeft K).compLeft T = ω.compRight I ↔ T = -(K * I) := by
  constructor
  · intro h
    apply (ω.compLeft K).compLeft_injective (compLeft_nondegenerate ω hω hK)
    exact h.trans (metric_intertwiner ω hI hK hωI).symm
  · intro h
    rw [h]
    exact metric_intertwiner ω hI hK hωI

/-- For opposite square laws, the ordered product is an involution exactly
when the two operators anticommute. -/
theorem mul_sq_eq_one_iff_anticommute (I K : Module.End ℝ E)
    (hI : I * I = -1) (hK : K * K = 1) :
    (I * K) * (I * K) = 1 ↔ I * K = -(K * I) := by
  have hII (x : E) : I (I x) = -x := by
    simpa using congrArg (fun A : Module.End ℝ E => A x) hI
  have hKK (x : E) : K (K x) = x := by
    simpa using congrArg (fun A : Module.End ℝ E => A x) hK
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have hx := congrArg I (congrArg (fun A : Module.End ℝ E => A (K x)) h)
    simpa only [Module.End.mul_apply, Module.End.one_apply, LinearMap.neg_apply,
      hII, hKK] using hx.symm
  · intro h
    have ha (x : E) : I (K x) = -(K (I x)) := by
      simpa using congrArg (fun A : Module.End ℝ E => A x) h
    apply LinearMap.ext
    intro x
    change I (K (I (K x))) = x
    rw [ha x]
    simp only [map_neg, hKK, hII, neg_neg]

/-- A positive right contraction excludes commuting with an antisymplectic
involution on a nonzero carrier; it does not assert anticommutation. -/
theorem not_commute_of_positive [Nontrivial E] (ω : LinearMap.BilinForm ℝ E)
    (I K : Module.End ℝ E) (hK : K * K = 1)
    (hωK : ∀ x y, ω (K x) (K y) = -ω x y)
    (hpos : ∀ x, x ≠ 0 → 0 < (ω.compRight I) x x) : I * K ≠ K * I := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hKK : K (K x) = x := by
    simpa using congrArg (fun A : Module.End ℝ E => A x) hK
  have hKx : K x ≠ 0 := by
    intro hz
    exact hx (hKK.symm.trans (by rw [hz, map_zero]))
  have hc : I (K x) = K (I x) := by
    simpa using congrArg (fun A : Module.End ℝ E => A x) h
  have hp := hpos x hx
  have hpK := hpos (K x) hKx
  change 0 < ω x (I x) at hp
  change 0 < ω (K x) (I (K x)) at hpK
  rw [hc, hωK] at hpK
  exact (not_lt_of_ge (neg_nonpos.mpr hp.le)) hpK

/-- A nondegenerate common metric cannot produce both square signs through
the same contraction on a nonzero real vector space. -/
theorem compLeft_ne_of_opposite_squares [Nontrivial E]
    (g : LinearMap.BilinForm ℝ E) (hg : g.Nondegenerate)
    (I K : Module.End ℝ E) (hI : I * I = -1) (hK : K * K = 1) :
    g.compLeft I ≠ g.compLeft K := by
  intro h
  have hIK := g.compLeft_injective hg h
  have hs : -(1 : Module.End ℝ E) = 1 := by
    rw [← hI, hIK, hK]
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hneg : -x = x := by
    simpa using congrArg (fun A : Module.End ℝ E => A x) hs
  have hsum : x + x = 0 := by
    calc
      x + x = -x + x := congrArg (fun y : E => y + x) hneg.symm
      _ = 0 := neg_add_cancel x
  have htwo : (2 : ℝ) • x = 0 := by simpa only [two_smul] using hsum
  exact hx ((smul_eq_zero.mp htwo).resolve_left (by norm_num))

end InfoGeometry.Geometry.SymplecticMetricCompatibility
