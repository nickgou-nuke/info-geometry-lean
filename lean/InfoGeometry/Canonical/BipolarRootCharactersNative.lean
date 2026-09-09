import InfoGeometry.Analysis.BipolarCrossRatioLog
import Mathlib.Tactic

/-! The two exponential characters of the additive bipolar Cartan line.

This owner contains only the native multiplicative representation.  Matrix
adjoint statements belong to a separate owner and are not asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarRootCharactersNative

open InfoGeometry.Analysis.BipolarCrossRatioLog

def plus : Multiplicative ℂ →* ℂˣ where
  toFun w := Units.mk0 (Complex.exp (Multiplicative.toAdd w))
    (Complex.exp_ne_zero _)
  map_one' := by
    ext
    simp
  map_mul' w z := by
    ext
    change Complex.exp (Multiplicative.toAdd w + Multiplicative.toAdd z) =
      Complex.exp (Multiplicative.toAdd w) * Complex.exp (Multiplicative.toAdd z)
    rw [Complex.exp_add]

def minus : Multiplicative ℂ →* ℂˣ where
  toFun w := Units.mk0 (Complex.exp (-Multiplicative.toAdd w))
    (Complex.exp_ne_zero _)
  map_one' := by
    ext
    simp
  map_mul' w z := by
    ext
    change Complex.exp (-(Multiplicative.toAdd w + Multiplicative.toAdd z)) =
      Complex.exp (-Multiplicative.toAdd w) * Complex.exp (-Multiplicative.toAdd z)
    rw [show -(Multiplicative.toAdd w + Multiplicative.toAdd z) =
      -Multiplicative.toAdd w + -Multiplicative.toAdd z by ring, Complex.exp_add]

@[simp] theorem plus_apply (w : Multiplicative ℂ) :
    ((plus w : ℂˣ) : ℂ) = Complex.exp (Multiplicative.toAdd w) := rfl

@[simp] theorem minus_apply (w : Multiplicative ℂ) :
    ((minus w : ℂˣ) : ℂ) = Complex.exp (-Multiplicative.toAdd w) := rfl

theorem plus_bipolar {s : ℂ} (hs : s ∈ punctured01) :
    ((plus (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) = crossRatio01 s := by
  simpa using exp_bipolarLog hs

theorem minus_bipolar {s : ℂ} (hs : s ∈ punctured01) :
    ((minus (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) =
      (crossRatio01 s)⁻¹ := by
  change Complex.exp (-bipolarLog s) = (crossRatio01 s)⁻¹
  rw [Complex.exp_neg]
  rw [exp_bipolarLog hs]

theorem bipolar_root_character_packet {s : ℂ} (hs : s ∈ punctured01) :
    ((plus (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) = crossRatio01 s ∧
    ((minus (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) =
      (crossRatio01 s)⁻¹ :=
  ⟨plus_bipolar hs, minus_bipolar hs⟩

end InfoGeometry.Canonical.BipolarRootCharactersNative
