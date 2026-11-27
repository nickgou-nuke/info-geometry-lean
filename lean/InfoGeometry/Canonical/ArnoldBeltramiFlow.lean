/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NavierStokesShearReconstruction
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Explicit real Beltrami fields and their particle flow

On the existing spatial carrier `Fin 3 → ℝ`, the field
`(cos z, -s sin z, 0)` has actual curl `(s cos z, -sin z, 0)`.
Its helicity density is `s`; when `s ^ 2 = 1` it is a curl eigenfield.
The explicit particle trajectories solve the velocity ODE and form smooth
invertible maps with determinant-one spatial derivative. The Euler statement
uses the existing native coordinate-derivative PDE predicate.

These are smooth fields on real coordinate space. No finite-energy claim on
all of real coordinate space or spectral decomposition of general curl is made.
-/

noncomputable section

open scoped ContDiff

namespace InfoGeometry.Canonical.ArnoldBeltramiFlow

open InfoGeometry.Canonical.NavierStokesShearReconstruction

/-- A real two-sign Beltrami family, with a general real parameter retained. -/
def velocity (s : ℝ) (x : Space) : Space :=
  ![Real.cos (x 2), -s * Real.sin (x 2), 0]

/-- The actual particle flow: the third coordinate is constant along each orbit. -/
def flow (s t : ℝ) (x : Space) : Space :=
  ![x 0 + t * Real.cos (x 2), x 1 - s * t * Real.sin (x 2), x 2]

@[simp] theorem velocity_third (s : ℝ) (x : Space) : velocity s x 2 = 0 := rfl

@[simp] theorem flow_third (s t : ℝ) (x : Space) : flow s t x 2 = x 2 := rfl

theorem contDiff_velocity (s : ℝ) : ContDiff ℝ ∞ (velocity s) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> dsimp [velocity] <;> fun_prop

theorem contDiff_flow (s t : ℝ) : ContDiff ℝ ∞ (flow s t) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> dsimp [flow] <;> fun_prop

theorem contDiff_flow_uncurry (s : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Space => flow s p.1 p.2) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> dsimp [flow] <;> fun_prop

/-- Every partial derivative is computed from the actual trigonometric field. -/
theorem coordDeriv_velocity (s : ℝ) (i j : Fin 3) (x : Space) :
    coordDeriv i (fun y => velocity s y j) x =
      if i = 2 then ![-Real.sin (x 2), -s * Real.cos (x 2), 0] j else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [coordDeriv, velocity, Real.deriv_sin, Real.deriv_cos]

@[simp] theorem divergence_velocity (s : ℝ) (x : Space) :
    divergence (velocity s) x = 0 := by
  simp [divergence, coordDeriv_velocity]

/-- The actual curl formula does not require a unit-sign hypothesis. -/
theorem curl_velocity_formula (s : ℝ) (x : Space) :
    curl (velocity s) x = ![s * Real.cos (x 2), -Real.sin (x 2), 0] := by
  simp [curl, coordDeriv_velocity]

/-- The two signs `s = 1` and `s = -1` give curl eigenvalues of the same sign. -/
theorem curl_velocity (s : ℝ) (hs : s ^ 2 = 1) (x : Space) :
    curl (velocity s) x = s • velocity s x := by
  rw [curl_velocity_formula]
  ext i
  fin_cases i <;> simp [velocity]
  nlinarith [congrArg (fun a : ℝ => a * Real.sin (x 2)) hs]

/-- Unit-sign modes have Euclidean squared length one. -/
theorem sum_sq_velocity (s : ℝ) (hs : s ^ 2 = 1) (x : Space) :
    ∑ i, (velocity s x i) ^ 2 = 1 := by
  simp [velocity, Fin.sum_univ_three, mul_pow, hs]

/-- The physical local helicity density uses the computed spatial curl. -/
theorem helicity_density_velocity (s : ℝ) (x : Space) :
    ∑ i, velocity s x i * curl (velocity s) x i = s := by
  rw [curl_velocity_formula]
  simp [velocity, Fin.sum_univ_three]
  nlinarith [congrArg (fun a : ℝ => s * a) (Real.sin_sq_add_cos_sq (x 2))]

theorem velocity_ne_zero (s : ℝ) (hs : s ^ 2 = 1) (x : Space) :
    velocity s x ≠ 0 := by
  intro h
  have hsq := sum_sq_velocity s hs x
  simp [h] at hsq

@[simp] theorem advection_velocity (s : ℝ) (x : Space) (i : Fin 3) :
    advection (velocity s) x i = 0 := by
  simp [advection, coordDeriv_velocity]

/-- A stationary, unforced Euler solution with constant pressure, in the
existing spatial PDE interface. This holds for every real parameter `s`. -/
theorem stationary_euler (s t : ℝ) (x : Space) :
    SatisfiesAt 0 (fun _ => velocity s) (fun _ _ => 0) (fun _ _ => 0) t x := by
  constructor
  · exact divergence_velocity s x
  · intro i
    simp [advection_velocity]

@[simp] theorem flow_zero (s : ℝ) (x : Space) : flow s 0 x = x := by
  ext i
  fin_cases i <;> simp [flow]

theorem flow_add (s t r : ℝ) (x : Space) :
    flow s t (flow s r x) = flow s (t + r) x := by
  ext i
  fin_cases i <;> simp [flow] <;> ring

@[simp] theorem flow_neg_flow (s t : ℝ) (x : Space) :
    flow s (-t) (flow s t x) = x := by
  rw [flow_add]
  simp

@[simp] theorem flow_flow_neg (s t : ℝ) (x : Space) :
    flow s t (flow s (-t) x) = x := by
  rw [flow_add]
  simp

/-- The inverse is the same explicit particle flow at negative time. -/
def flowEquiv (s t : ℝ) : Space ≃ Space where
  toFun := flow s t
  invFun := flow s (-t)
  left_inv := flow_neg_flow s t
  right_inv := flow_flow_neg s t

@[simp] theorem flowEquiv_apply (s t : ℝ) (x : Space) :
    flowEquiv s t x = flow s t x := rfl

@[simp] theorem flowEquiv_symm_apply (s t : ℝ) (x : Space) :
    (flowEquiv s t).symm x = flow s (-t) x := rfl

@[simp] theorem velocity_flow (s t : ℝ) (x : Space) :
    velocity s (flow s t x) = velocity s x := by
  rfl

/-- The explicit trajectories satisfy the actual vector-valued particle ODE. -/
theorem hasDerivAt_flow (s t : ℝ) (x : Space) :
    HasDerivAt (fun r => flow s r x) (velocity s (flow s t x)) t := by
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · change HasDerivAt (fun r : ℝ => x 0 + r * Real.cos (x 2))
      (Real.cos (x 2)) t
    simpa using
      (hasDerivAt_const t (x 0)).fun_add
        ((hasDerivAt_id t).mul_const (Real.cos (x 2)))
  · change HasDerivAt (fun r : ℝ => x 1 - s * r * Real.sin (x 2))
      (-s * Real.sin (x 2)) t
    simpa using
      (hasDerivAt_const t (x 1)).fun_sub
        (((hasDerivAt_id t).const_mul s).mul_const (Real.sin (x 2)))
  · simpa [flow, velocity] using hasDerivAt_const t (x 2)

/-- The continuous linear spatial derivative of the particle flow. -/
def flowDerivative (s t : ℝ) (x : Space) : Space →L[ℝ] Space :=
  ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj 0 +
        (-t * Real.sin (x 2)) • ContinuousLinearMap.proj 2,
      ContinuousLinearMap.proj 1 +
        (-s * t * Real.cos (x 2)) • ContinuousLinearMap.proj 2,
      ContinuousLinearMap.proj 2]

theorem flowDerivative_apply (s t : ℝ) (x v : Space) :
    flowDerivative s t x v =
      ![v 0 - t * Real.sin (x 2) * v 2,
        v 1 - s * t * Real.cos (x 2) * v 2, v 2] := by
  ext i
  fin_cases i <;> simp [flowDerivative] <;> ring

/-- The derivative is derived by the native Fréchet chain and product rules. -/
theorem hasFDerivAt_flow (s t : ℝ) (x : Space) :
    HasFDerivAt (flow s t) (flowDerivative s t x) x := by
  unfold flowDerivative
  apply hasFDerivAt_pi.2
  intro i
  fin_cases i
  · change HasFDerivAt (fun y : Space => y 0 + t * Real.cos (y 2))
      (ContinuousLinearMap.proj 0 +
        (-t * Real.sin (x 2)) • ContinuousLinearMap.proj 2) x
    convert (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) x).fun_add
      ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x).cos.fun_const_smul t) using 1
    ext v
    simp
    ring
  · change HasFDerivAt (fun y : Space => y 1 - s * t * Real.sin (y 2))
      (ContinuousLinearMap.proj 1 +
        (-s * t * Real.cos (x 2)) • ContinuousLinearMap.proj 2) x
    convert (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) x).fun_sub
      ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x).sin.fun_const_smul (s * t)) using 1
    ext v
    simp
    ring
  · simpa [flow] using hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x

theorem fderiv_flow (s t : ℝ) (x : Space) :
    fderiv ℝ (flow s t) x = flowDerivative s t x :=
  (hasFDerivAt_flow s t x).fderiv

/-- Matrix of the actual derivative in the native coordinate basis. -/
def flowJacobian (s t : ℝ) (x : Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, -t * Real.sin (x 2);
     0, 1, -s * t * Real.cos (x 2);
     0, 0, 1]

theorem flowJacobian_eq_coordDeriv (s t : ℝ) (x : Space) (i j : Fin 3) :
    flowJacobian s t x i j = coordDeriv j (fun y => flow s t y i) x := by
  fin_cases i <;> fin_cases j <;>
    simp [flowJacobian, flow, coordDeriv,
      Real.deriv_sin, Real.deriv_cos]

theorem flowJacobian_mulVec (s t : ℝ) (x v : Space) :
    (flowJacobian s t x).mulVec v = flowDerivative s t x v := by
  rw [flowDerivative_apply]
  ext i
  fin_cases i <;>
    simp [flowJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

@[simp] theorem flowJacobian_det (s t : ℝ) (x : Space) :
    (flowJacobian s t x).det = 1 := by
  simp [flowJacobian, Matrix.det_fin_three]

end InfoGeometry.Canonical.ArnoldBeltramiFlow
