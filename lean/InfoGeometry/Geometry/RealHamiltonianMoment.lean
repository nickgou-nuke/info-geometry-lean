/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.RealMirrorComplexStructure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Real Hamiltonian rotations from an endogenous complex structure

The scalar field is `ℝ`.  A bounded real operator `J` with `J² = -id`
generates the actual operator flow `cos t • id + sin t • J`; no centrality
condition on `J` is imposed.  If `star J = -J` on a real Hilbert space,
the continuous bilinear form `ω(u,v) = -2 ⟪Ju,v⟫` is alternating and
nondegenerate, the flow preserves it, and the literal Fréchet derivative of
`μ(x) = ‖x‖²` is `ω(Jx, ·)`.

This is the linear Hamiltonian model and sign convention of §§2.1–2.3 of
Cassia--Longhi--Zabzine, *Symplectic Cuts and Open/Closed Strings I*.
It does not construct a quotient manifold or a descended symplectic form.
-/

noncomputable section

namespace InfoGeometry.Geometry.RealHamiltonianMoment

open InfoGeometry.Canonical

section Rotation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The existing real complex-structure predicate, evaluated pointwise. -/
theorem square_apply (J : V →L[ℝ] V)
    (hJ : IsRealComplexStructure J.toLinearMap) (x : V) :
    J (J x) = -x :=
  realComplexStructure_apply_sq J.toLinearMap hJ x

/-- A full bounded-operator rotation, with real coefficients. -/
def rotation (J : V →L[ℝ] V) (t : ℝ) : V →L[ℝ] V :=
  Real.cos t • ContinuousLinearMap.id ℝ V + Real.sin t • J

@[simp] theorem rotation_apply (J : V →L[ℝ] V) (t : ℝ) (x : V) :
    rotation J t x = Real.cos t • x + Real.sin t • J x :=
  rfl

@[simp] theorem rotation_zero (J : V →L[ℝ] V) :
    rotation J 0 = ContinuousLinearMap.id ℝ V := by
  ext x
  simp

theorem rotation_add (J : V →L[ℝ] V)
    (hJ : IsRealComplexStructure J.toLinearMap) (s t : ℝ) :
    rotation J (s + t) = (rotation J s).comp (rotation J t) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, rotation_apply,
    map_add, map_smul, square_apply J hJ, Real.cos_add, Real.sin_add]
  module

theorem rotation_neg_left (J : V →L[ℝ] V)
    (hJ : IsRealComplexStructure J.toLinearMap) (t : ℝ) :
    (rotation J (-t)).comp (rotation J t) = ContinuousLinearMap.id ℝ V := by
  rw [← rotation_add J hJ, neg_add_cancel, rotation_zero]

theorem rotation_neg_right (J : V →L[ℝ] V)
    (hJ : IsRealComplexStructure J.toLinearMap) (t : ℝ) :
    (rotation J t).comp (rotation J (-t)) = ContinuousLinearMap.id ℝ V := by
  rw [← rotation_add J hJ, add_neg_cancel, rotation_zero]

theorem rotation_periodic (J : V →L[ℝ] V) :
    Function.Periodic (rotation J) (2 * Real.pi) := by
  intro t
  ext x
  simp only [rotation_apply, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- `J` commutes with its generated rotation, not with arbitrary operators. -/
theorem map_rotation (J : V →L[ℝ] V) (t : ℝ) (x : V) :
    J (rotation J t x) = rotation J t (J x) := by
  simp only [rotation_apply, map_add, map_smul]

/-- The derivative of the orbit is its Hamiltonian generator at the orbit point. -/
theorem hasDerivAt_rotation (J : V →L[ℝ] V)
    (hJ : IsRealComplexStructure J.toLinearMap) (t : ℝ) (x : V) :
    HasDerivAt (fun s => rotation J s x) (J (rotation J t x)) t := by
  have hvalue : (-Real.sin t) • x + Real.cos t • J x =
      J (rotation J t x) := by
    simp only [rotation_apply, map_add, map_smul, square_apply J hJ]
    module
  change HasDerivAt (fun s => Real.cos s • x + Real.sin s • J x)
    (J (rotation J t x)) t
  rw [← hvalue]
  exact ((Real.hasDerivAt_cos t).smul_const x).add
    ((Real.hasDerivAt_sin t).smul_const (J x))

/-- Reparametrization by a real weight produces the weighted generator. -/
theorem hasDerivAt_weightedRotation (J : V →L[ℝ] V)
    (hJ : IsRealComplexStructure J.toLinearMap) (q t : ℝ) (x : V) :
    HasDerivAt (fun s => rotation J (q * s) x)
      (q • J (rotation J (q * t) x)) t := by
  have hscalar : HasDerivAt (fun s : ℝ => q * s) q t := by
    simpa using (hasDerivAt_id t).const_mul q
  simpa only [Function.comp_apply] using
    (hasDerivAt_rotation J hJ (q * t) x).scomp t hscalar

end Rotation

section Hilbert

variable {E : Type*} [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The paper's normalization, as a native continuous bilinear form. -/
def omega (J : E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (-2 : ℝ) • (innerSL ℝ).comp J

@[simp] theorem omega_apply (J : E →L[ℝ] E) (u v : E) :
    omega J u v = -2 * inner ℝ (J u) v :=
  rfl

theorem inner_map_left (J : E →L[ℝ] E) (hstar : star J = -J) (u v : E) :
    inner ℝ (J u) v = -inner ℝ u (J v) := by
  calc
    inner ℝ (J u) v = inner ℝ u ((star J) v) :=
      (J.adjoint_inner_right u v).symm
    _ = -inner ℝ u (J v) := by rw [hstar]; simp

theorem inner_map_map (J : E →L[ℝ] E)
    (hJ : IsRealComplexStructure J.toLinearMap) (hstar : star J = -J)
    (u v : E) : inner ℝ (J u) (J v) = inner ℝ u v := by
  rw [inner_map_left J hstar, square_apply J hJ]
  simp

theorem omega_skew (J : E →L[ℝ] E) (hstar : star J = -J) (u v : E) :
    omega J u v = -omega J v u := by
  rw [omega_apply, omega_apply, inner_map_left J hstar,
    real_inner_comm u (J v)]
  ring

theorem omega_self (J : E →L[ℝ] E) (hstar : star J = -J) (u : E) :
    omega J u u = 0 := by
  have h := omega_skew J hstar u u
  linarith

/-- Nondegeneracy uses the square law; finite dimension is not required. -/
theorem omega_nondegenerate (J : E →L[ℝ] E)
    (hJ : IsRealComplexStructure J.toLinearMap) (u : E)
    (hu : ∀ v, omega J u v = 0) : u = 0 := by
  have hinner : inner ℝ (J u) (J u) = 0 := by
    have h := hu (J u)
    rw [omega_apply] at h
    linarith
  have hJu : J u = 0 := inner_self_eq_zero.mp hinner
  have hsq := square_apply J hJ u
  rw [hJu, map_zero] at hsq
  exact neg_eq_zero.mp hsq.symm

/-- The real quadratic moment; no external complex scalar is introduced. -/
def quadraticMoment (x : E) : ℝ := ‖x‖ ^ 2

theorem omega_generator (J : E →L[ℝ] E)
    (hJ : IsRealComplexStructure J.toLinearMap) (x : E) :
    omega J (J x) = 2 • innerSL ℝ x := by
  ext v
  simp only [omega_apply, square_apply J hJ, inner_neg_left,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- The literal Hamiltonian identity `dμ = ι_(Jx) ω`. -/
theorem hasFDerivAt_quadraticMoment (J : E →L[ℝ] E)
    (hJ : IsRealComplexStructure J.toLinearMap) (x : E) :
    HasFDerivAt quadraticMoment (omega J (J x)) x := by
  rw [omega_generator J hJ]
  exact (hasStrictFDerivAt_norm_sq x).hasFDerivAt

theorem fderiv_quadraticMoment (J : E →L[ℝ] E)
    (hJ : IsRealComplexStructure J.toLinearMap) (x v : E) :
    fderiv ℝ quadraticMoment x v = omega J (J x) v := by
  rw [(hasFDerivAt_quadraticMoment J hJ x).fderiv]

theorem inner_rotation (J : E →L[ℝ] E)
    (hJ : IsRealComplexStructure J.toLinearMap) (hstar : star J = -J)
    (t : ℝ) (u v : E) :
    inner ℝ (rotation J t u) (rotation J t v) = inner ℝ u v := by
  simp only [rotation_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    inner_map_map J hJ hstar, inner_map_left J hstar]
  calc
    _ = (Real.sin t ^ 2 + Real.cos t ^ 2) * inner ℝ u v := by ring
    _ = inner ℝ u v := by rw [Real.sin_sq_add_cos_sq]; ring

theorem quadraticMoment_rotation (J : E →L[ℝ] E)
    (hJ : IsRealComplexStructure J.toLinearMap) (hstar : star J = -J)
    (t : ℝ) (x : E) :
    quadraticMoment (rotation J t x) = quadraticMoment x := by
  unfold quadraticMoment
  calc
    ‖rotation J t x‖ ^ 2 = inner ℝ (rotation J t x) (rotation J t x) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ x x := inner_rotation J hJ hstar t x x
    _ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x

theorem norm_rotation (J : E →L[ℝ] E)
    (hJ : IsRealComplexStructure J.toLinearMap) (hstar : star J = -J)
    (t : ℝ) (x : E) : ‖rotation J t x‖ = ‖x‖ := by
  have hs := quadraticMoment_rotation J hJ hstar t x
  unfold quadraticMoment at hs
  nlinarith [norm_nonneg (rotation J t x), norm_nonneg x]

theorem omega_rotation (J : E →L[ℝ] E)
    (hJ : IsRealComplexStructure J.toLinearMap) (hstar : star J = -J)
    (t : ℝ) (u v : E) :
    omega J (rotation J t u) (rotation J t v) = omega J u v := by
  rw [omega_apply, map_rotation, inner_rotation J hJ hstar, omega_apply]

end Hilbert

end InfoGeometry.Geometry.RealHamiltonianMoment
