import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# InfoGeometry.Canonical.TopologicalGroupIsoExpLog

Abstract exp/log unification as a continuous additive-to-multiplicative group isomorphism,
plus a concrete infinitesimal derivative propagation theorem on `ℝ`.

No wrappers. No `sorry`.
-/

open Topology

namespace InfoGeometry.Canonical.TopologicalGroupIsoExpLog

structure TopologicalGroupIso (E : Type*) (G : Type*)
    [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E]
    [CommGroup G] [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G] where
  toFun : E → G
  invFun : G → E
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  map_add' : ∀ x y : E, toFun (x + y) = toFun x * toFun y
  continuous_toFun : Continuous toFun
  continuous_invFun : Continuous invFun

variable {E G : Type*}
  [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E]
  [CommGroup G] [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
  (Φ : TopologicalGroupIso E G)

theorem map_zero_eq_one : Φ.toFun 0 = 1 := by
  have h0 : Φ.toFun 0 = Φ.toFun 0 * Φ.toFun 0 := by
    simpa using Φ.map_add' 0 0
  have h1 := congrArg (fun z => (Φ.toFun 0)⁻¹ * z) h0
  simpa [mul_assoc] using h1.symm

theorem map_one_eq_zero : Φ.invFun 1 = 0 := by
  have h0 : Φ.toFun 0 = 1 := map_zero_eq_one Φ
  have hleft : Φ.invFun (Φ.toFun 0) = 0 := Φ.left_inv 0
  simpa [h0] using hleft

section RealInfinitesimal

variable (f : ℝ → ℝ)
variable {c : ℝ}

/--
If `f(x+y)=f x * f y` and `f' (0)=c`, then `f' (x)=f(x)*c`.
-/
theorem infinitesimal_derivation_near_zero
    (hf : ∀ x y, f (x + y) = f x * f y)
    (h_deriv : HasDerivAt f c 0) (x : ℝ) :
    HasDerivAt f (f x * c) x := by
  have hmul : HasDerivAt (fun t => f x * f t) (f x * c) 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_deriv.const_mul (f x)
  have hshift0 : HasDerivAt (fun t => f (x + t)) (f x * c) 0 := by
    refine hmul.congr_of_eventuallyEq ?_
    filter_upwards [] with t
    simpa [hf x t]
  have hsub : HasDerivAt (fun u => u - x) 1 x := by
    have hsub' : HasDerivAt (fun u => u - x) (1 - 0) x := (hasDerivAt_id x).sub (hasDerivAt_const x x)
    simpa using hsub'
  have hshift0' : HasDerivAt (fun t => f (x + t)) (f x * c) (x - x) := by
    simpa using hshift0
  let g : ℝ → ℝ := fun u => u - x
  have hg : HasDerivAt g 1 x := by
    simpa [g] using hsub
  have hcomp : HasDerivAt (((fun t => f (x + t)) ∘ g)) ((f x * c) * 1) x :=
    HasDerivAt.comp x hshift0' hg
  have hfun : (((fun t => f (x + t)) ∘ g)) = f := by
    funext u
    simp [g, Function.comp]
  simpa [hfun, mul_one] using hcomp

end RealInfinitesimal

end InfoGeometry.Canonical.TopologicalGroupIsoExpLog
