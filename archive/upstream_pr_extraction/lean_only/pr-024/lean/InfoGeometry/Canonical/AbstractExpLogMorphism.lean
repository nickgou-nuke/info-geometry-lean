import Mathlib

/-!
# InfoGeometry.Canonical.AbstractExpLogMorphism

Abstract additive-to-multiplicative exp/log morphism with a concrete
infinitesimal derivative theorem on `ℝ`.
-/

open Topology

namespace InfoGeometry.Canonical.AbstractExpLogMorphism

/-- Continuous additive-to-multiplicative group isomorphism data. -/
structure TopologicalGroupIso (E : Type*) (G : Type*)
    [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousNeg E]
    [CommGroup G] [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G] where
  toFun : E → G
  invFun : G → E
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  map_add' : ∀ x y : E, toFun (x + y) = toFun x * toFun y
  continuous_toFun : Continuous toFun
  continuous_invFun : Continuous invFun

variable {E G : Type*}
    [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousNeg E]
    [CommGroup G] [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (Φ : TopologicalGroupIso E G)

/-- Additive identity maps to multiplicative identity. -/
theorem map_zero_eq_one : Φ.toFun 0 = 1 := by
  have h : Φ.toFun 0 = Φ.toFun 0 * Φ.toFun 0 := by
    simpa using Φ.map_add' 0 0
  have h' := congrArg (fun z => (Φ.toFun 0)⁻¹ * z) h
  simpa [mul_assoc] using h'.symm

/-- Multiplicative identity maps to additive identity under the inverse. -/
theorem map_one_eq_zero : Φ.invFun 1 = 0 := by
  rw [← map_zero_eq_one Φ, Φ.left_inv]

/--
If `f (x+y) = f x * f y` and `f` has derivative `c` at `0`, then
`f` has derivative `f x * c` at every point `x`.
-/
theorem infinitesimal_derivation_near_zero
    (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f x * f y)
    (c : ℝ) (h_deriv : HasDerivAt f c 0) (x : ℝ) :
    HasDerivAt f (f x * c) x := by
  let h₂ : ℝ → ℝ := fun t => f (x + t)
  have h₂_eq : h₂ = fun t => f x * f t := by
    funext t
    simp [h₂, hf x t]
  have hh₂ : HasDerivAt h₂ (f x * c) 0 := by
    rw [h₂_eq]
    exact (h_deriv.const_mul (f x))
  let h : ℝ → ℝ := fun u => u - x
  have hh : HasDerivAt h 1 x := by
    simpa [h] using (hasDerivAt_id x).sub_const x
  have hx : h x = 0 := by
    simp [h]
  have hh₂' : HasDerivAt h₂ (f x * c) (h x) := by
    simpa [hx] using hh₂
  have hcomp : HasDerivAt (h₂ ∘ h) ((f x * c) * 1) x := hh₂'.comp x hh
  have hfun : (h₂ ∘ h) = f := by
    funext u
    simp [h₂, h, sub_eq_add_neg]
  rw [hfun] at hcomp
  simpa using hcomp

end InfoGeometry.Canonical.AbstractExpLogMorphism

