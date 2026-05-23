import InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics

/-!
# InfoGeometry.Krein.SplitBoost

Canonical split-boost layer on the split-complex carrier.

This file packages the genuine hyperbolic boost laws already implicit in the
split-complex arithmetic layer:

* the boost element is `cosh t + j sinh t`;
* it forms a one-parameter subgroup;
* it has split norm `1`;
* its action preserves the split norm;
* on light-cone coordinates it scales by `exp(±t)`.

No placeholder `True` carriers are introduced here.
-/

noncomputable section

namespace InfoGeometry.Krein.SplitBoost

open InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics
open InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex

abbrev SC := InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex

/-- The canonical split boost element `cosh t + j sinh t`. -/
def boostElement (t : ℝ) : SC :=
  ⟨Real.cosh t, Real.sinh t⟩

@[simp] theorem boostElement_re (t : ℝ) :
    (boostElement t).re = Real.cosh t := rfl

@[simp] theorem boostElement_im (t : ℝ) :
    (boostElement t).hyp = Real.sinh t := rfl

/-- The canonical split boost has split norm one. -/
theorem boostElement_norm (t : ℝ) :
    SplitComplex.norm (boostElement t) = 1 := by
  unfold SplitComplex.norm leftPart rightPart boostElement
  rw [Real.cosh_add_sinh, Real.cosh_sub_sinh]
  rw [← Real.exp_add]
  ring_nf
  simp

/-- The boost family is a one-parameter subgroup. -/
theorem boostElement_add (s t : ℝ) :
    boostElement (s + t)
      = mul (boostElement s) (boostElement t) := by
  ext <;> simp [boostElement, mul,
    Real.cosh_add, Real.sinh_add] <;> ring

/-- The identity boost is the split multiplicative unit. -/
@[simp] theorem boostElement_zero :
    boostElement 0 = SplitComplex.one := by
  ext <;> simp [boostElement, SplitComplex.one]

/-- The inverse boost is the boost with opposite rapidity. -/
@[simp] theorem boostElement_neg (t : ℝ) :
    boostElement (-t) = ⟨Real.cosh t, -Real.sinh t⟩ := by
  simp [boostElement, Real.cosh_neg, Real.sinh_neg]

/-- `boost(t)` times `boost(-t)` is the identity. -/
theorem boostElement_mul_neg (t : ℝ) :
    mul (boostElement t) (boostElement (-t)) = SplitComplex.one := by
  rw [← boostElement_add, add_neg_cancel, boostElement_zero]

/-- Left light-cone coordinate scales by `exp(t)` under the boost action. -/
theorem boost_leftPart_mul (t : ℝ) (x : SC) :
    leftPart (mul (boostElement t) x) = Real.exp t * leftPart x := by
  rw [SplitComplex.leftPart_mul]
  simp [boostElement, leftPart, Real.cosh_add_sinh]

/-- Right light-cone coordinate scales by `exp(-t)` under the boost action. -/
theorem boost_rightPart_mul (t : ℝ) (x : SC) :
    rightPart (mul (boostElement t) x) = Real.exp (-t) * rightPart x := by
  rw [SplitComplex.rightPart_mul]
  simp [boostElement, rightPart, Real.cosh_sub_sinh]

/-- The split boost action preserves the split norm. -/
theorem boost_norm_preserved (t : ℝ) (x : SC) :
    SplitComplex.norm (mul (boostElement t) x) = SplitComplex.norm x := by
  rw [SplitComplex.norm_mul, boostElement_norm, one_mul]

/-- A split-boost unit preserves any zero-norm element. -/
theorem boost_preserves_zeroNorm (t : ℝ) (x : SC) (hx : SplitComplex.norm x = 0) :
    SplitComplex.norm (mul (boostElement t) x) = 0 := by
  rw [boost_norm_preserved, hx]

/-- The split boost action on reconstructed light-cone coordinates. -/
theorem boost_reconstruct_lightcone (t u v : ℝ) :
    leftPart (mul (boostElement t) (reconstruct u v)) = Real.exp t * u ∧
      rightPart (mul (boostElement t) (reconstruct u v)) = Real.exp (-t) * v := by
  have h1 := boost_leftPart_mul (t := t) (x := reconstruct u v)
  rw [SplitComplex.leftPart_reconstruct] at h1
  have h2 := boost_rightPart_mul (t := t) (x := reconstruct u v)
  rw [SplitComplex.rightPart_reconstruct] at h2
  exact And.intro h1 h2

/-- The split boost preserves the split norm of a light-cone reconstruction. -/
theorem boost_reconstruct_norm (t u v : ℝ) :
    SplitComplex.norm (mul (boostElement t) (reconstruct u v)) = u * v := by
  simpa [SplitComplex.norm_reconstruct] using
    (boost_norm_preserved (t := t) (x := reconstruct u v))

end InfoGeometry.Krein.SplitBoost
