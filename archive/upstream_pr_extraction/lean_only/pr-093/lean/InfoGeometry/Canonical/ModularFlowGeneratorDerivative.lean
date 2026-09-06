import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivative of an implemented operator flow

This owner proves the genuine Banach-algebra product rule for a conjugation
curve.  Differentiability of the implementing paths is explicit input; no
exponential or unbounded-generator theorem is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ModularFlowGeneratorDerivative

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def conjugationPath (U V : ℝ → A) (x : A) (t : ℝ) : A :=
  U t * x * V t

theorem hasDerivAt_conjugationPath
    (U V : ℝ → A) (U' V' : A) (x : A) (t : ℝ)
    (hU : HasDerivAt U U' t)
    (hV : HasDerivAt V V' t) :
    HasDerivAt (conjugationPath U V x)
      (U' * x * V t + U t * x * V') t := by
  unfold conjugationPath
  have hconst : HasDerivAt (fun _ : ℝ => x) 0 t := hasDerivAt_const t x
  have hleft : HasDerivAt (fun s => U s * x)
      (U' * x + U t * 0) t := hU.mul hconst
  have hright : HasDerivAt (fun s => U s * x * V s)
      ((U' * x + U t * 0) * V t + U t * x * V') t :=
    hleft.mul hV
  simpa using hright

theorem hasDerivAt_conjugationPath_zero
    (U V : ℝ → A) (U' V' : A) (x : A)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : HasDerivAt U U' 0)
    (hV : HasDerivAt V V' 0) :
    HasDerivAt (conjugationPath U V x)
      (U' * x + x * V') 0 := by
  have h := hasDerivAt_conjugationPath U V U' V' x 0 hU hV
  simpa [hU0, hV0] using h

theorem hasDerivAt_conjugationPath_zero_commutator
    (U V : ℝ → A) (c G : A) (x : A)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : HasDerivAt U (c * G) 0)
    (hV : HasDerivAt V (-(c * G)) 0)
    (hc : ∀ y : A, y * c = c * y) :
    HasDerivAt (conjugationPath U V x)
      (c * (G * x - x * G)) 0 := by
  have h := hasDerivAt_conjugationPath_zero
    U V (c * G) (-(c * G)) x hU0 hV0 hU hV
  have hcx := hc x
  have heq :
      c * G * x + x * -(c * G) = c * (G * x - x * G) := by
    rw [mul_neg]
    rw [← mul_assoc x c G, hcx]
    noncomm_ring
  rw [heq] at h
  exact h

theorem hasDerivAt_conjugationPath_zero_scalar_commutator
    (U V : ℝ → A) (c G : A) (x : A)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : HasDerivAt U (c * G) 0)
    (hV : HasDerivAt V (-(c * G)) 0)
    (hc : ∀ y : A, y * c = c * y) :
    HasDerivAt (conjugationPath U V x)
      (c * G * x - c * x * G) 0 := by
  simpa only [mul_sub, mul_assoc] using
    hasDerivAt_conjugationPath_zero_commutator
      U V c G x hU0 hV0 hU hV hc

end InfoGeometry.Canonical.ModularFlowGeneratorDerivative
