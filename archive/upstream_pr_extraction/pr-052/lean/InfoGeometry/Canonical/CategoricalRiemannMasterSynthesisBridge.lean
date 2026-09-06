import Mathlib.Tactic

/-!
# Affine reflection fixed-locus lemma

This module records one elementary affine-geometric fact:

The result concerns only the fixed locus of `(x, y) ↦ (1 - x, y)`.
-/

namespace InfoGeometry.Canonical.CategoricalRiemannMasterSynthesisBridge

open Complex
/-- Real antiunitary reflection on $\mathbb{R}^2$: $\mathcal{J}_{\text{anti}}(x, y) = (1 - x, y)$. -/
def realAntiunitaryReflection (v : ℝ × ℝ) : ℝ × ℝ :=
  (1 - v.1, v.2)

/--
**Affine reflection fixed locus.**
For `(x, y) : ℝ × ℝ`, the reflection is fixed exactly when `x = 1/2`:
$$\mathcal{J}_{\text{anti}}(v) = v \iff v.1 = \frac{1}{2}.$$
-/
theorem realAntiunitaryReflection_fixed_locus (v : ℝ × ℝ) :
    realAntiunitaryReflection v = v ↔ v.1 = 1 / 2 := by
  unfold realAntiunitaryReflection
  constructor
  · intro h
    have h1 : 1 - v.1 = v.1 := (Prod.mk.inj h).1
    linarith
  · intro h
    ext
    · linarith
    · rfl

end InfoGeometry.Canonical.CategoricalRiemannMasterSynthesisBridge
