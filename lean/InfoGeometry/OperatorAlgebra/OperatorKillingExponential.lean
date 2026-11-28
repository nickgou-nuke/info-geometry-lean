/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.ContinuousDerivationExponential
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Integrating bounded real Killing derivations

The exponential and its orbit derivative are those already constructed in
`ContinuousDerivationExponential`. A bounded continuous Leibniz operator on
a complete real normed algebra integrates to actual algebra automorphisms.
The inverse is the negative-time exponential, and the family is bundled as
a native homomorphism from `Multiplicative ℝ`.

An annihilated continuous linear functional and a continuous bilinear form
for which the generator is skew are preserved by these automorphisms. The
proof differentiates the actual exponential orbits and applies the real
mean-value theorem. Positivity of the functional or form is not needed.

Conversely, differentiation of an actual automorphism flow and its conserved
continuous data recovers the Leibniz, functional, and bilinear equations.
This reverse direction assumes the orbit derivatives explicitly and does
not need completeness.

Completeness and boundedness are explicit hypotheses. This result does not
integrate unbounded derivations, construct Type III modular dynamics, or
assert that every algebraic derivation has an exponential automorphism flow.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorKillingExponential

open InfoGeometry.Lie.ContinuousDerivationExponential

section LinearInvariants

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]

/-- Forget only continuity in the two slots of a continuous bilinear form.
The underlying pointwise function is unchanged. -/
def continuousBilinForm (g : A →L[ℝ] A →L[ℝ] ℝ) : LinearMap.BilinForm ℝ A :=
  (ContinuousLinearMap.coeLM ℝ).comp g.toLinearMap

@[simp] theorem continuousBilinForm_apply
    (g : A →L[ℝ] A →L[ℝ] ℝ) (x y : A) :
    continuousBilinForm g x y = g x y := rfl

/-- Differentiation of the actual functional along the exponential orbit. -/
theorem hasDerivAt_functional_orbit_zero
    (D : A →L[ℝ] A) (ω : A →L[ℝ] ℝ)
    (hω : ∀ a : A, ω (D a) = 0) (x : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ω (flow D s x)) 0 t := by
  have h := ω.hasFDerivAt.comp_hasDerivAt t
    (hasStrictDerivAt_orbit D x t).hasDerivAt
  simpa only [Function.comp_apply, hω] using h

/-- A functional annihilating the generator is preserved for every real time. -/
theorem flow_preserves_functional
    (D : A →L[ℝ] A) (ω : A →L[ℝ] ℝ)
    (hω : ∀ a : A, ω (D a) = 0) (t : ℝ) (x : A) :
    ω (flow D t x) = ω x := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun r : ℝ => ω (flow D r x)) 0 s :=
    fun s => hasDerivAt_functional_orbit_zero D ω hω x s
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt)
    (fun s => (hderiv s).deriv) t 0
  simpa using hconst

/-- The native bilinear product rule computes the derivative of the form
on two simultaneously evolving exponential orbits. -/
theorem hasDerivAt_bilinForm_orbit_zero
    (D : A →L[ℝ] A) (g : A →L[ℝ] A →L[ℝ] ℝ)
    (hg : ∀ x y : A, g (D x) y + g x (D y) = 0)
    (x y : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g (flow D s x) (flow D s y)) 0 t := by
  have h := g.hasStrictDerivAt_of_bilinear
    (hasStrictDerivAt_orbit D x t) (hasStrictDerivAt_orbit D y t)
  have hz : g (flow D t x) (D (flow D t y)) +
      g (D (flow D t x)) (flow D t y) = 0 := by
    rw [add_comm]
    exact hg (flow D t x) (flow D t y)
  simpa only [hz] using h.hasDerivAt

/-- Skewness of the bounded generator preserves the full bilinear form. -/
theorem flow_preserves_bilinForm
    (D : A →L[ℝ] A) (g : A →L[ℝ] A →L[ℝ] ℝ)
    (hg : ∀ x y : A, g (D x) y + g x (D y) = 0)
    (t : ℝ) (x y : A) :
    g (flow D t x) (flow D t y) = g x y := by
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => g (flow D r x) (flow D r y)) 0 s :=
    fun s => hasDerivAt_bilinForm_orbit_zero D g hg x y s
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt)
    (fun s => (hderiv s).deriv) t 0
  simpa using hconst

end LinearInvariants

section AlgebraAutomorphisms

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The unit is killed by a genuine product derivation. -/
theorem derivation_map_one
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D) : D 1 = 0 := by
  have h : D (1 : A) = D 1 + D 1 := by
    simpa using hD (1 : A) 1
  apply add_left_cancel (a := D (1 : A))
  simpa only [add_zero] using h.symm

/-- The existing exponential linear equivalence is an actual real algebra
equivalence because its product and unit preservation have been proved. -/
def flowAlgEquiv
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D) (t : ℝ) :
    A ≃ₐ[ℝ] A :=
  AlgEquiv.ofLinearEquiv (flowLinearEquiv D t)
    (flowLinearEquiv_fixed_of_derivation_eq_zero D 1 (derivation_map_one D hD) t)
    (fun x y => flow_map_mul (ContinuousLinearMap.mul ℝ A) D hD t x y)

@[simp] theorem flowAlgEquiv_apply
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D) (t : ℝ) (x : A) :
    flowAlgEquiv D hD t x = flow D t x := rfl

/-- The inverse uses the existing exponential of the negative generator. -/
@[simp] theorem flowAlgEquiv_symm_apply
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D) (t : ℝ) (x : A) :
    (flowAlgEquiv D hD t).symm x = flow (-D) t x := rfl

@[simp] theorem flowAlgEquiv_zero
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D) :
    flowAlgEquiv D hD 0 = 1 := by
  ext x
  simp

/-- Composition order is the native automorphism multiplication order. -/
theorem flowAlgEquiv_add
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D) (s t : ℝ) :
    flowAlgEquiv D hD (s + t) = flowAlgEquiv D hD s * flowAlgEquiv D hD t := by
  ext x
  exact flow_add_apply D s t x

/-- The bounded derivation integrates to a genuine one-parameter group of
algebra automorphisms, including all positive and negative times. -/
def flowAlgEquivHom
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D) :
    Multiplicative ℝ →* (A ≃ₐ[ℝ] A) where
  toFun t := flowAlgEquiv D hD t.toAdd
  map_one' := flowAlgEquiv_zero D hD
  map_mul' s t := flowAlgEquiv_add D hD s.toAdd t.toAdd

@[simp] theorem flowAlgEquivHom_apply
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D)
    (t : Multiplicative ℝ) (x : A) :
    flowAlgEquivHom D hD t x = flow D t.toAdd x := rfl

/-- The derivative of the bundled automorphism orbit is the original
continuous generator acting on that orbit. -/
theorem hasDerivAt_flowAlgEquiv
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D) (x : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flowAlgEquiv D hD s x)
      (D (flowAlgEquiv D hD t x)) t :=
  (hasStrictDerivAt_orbit D x t).hasDerivAt

/-- In particular, differentiating at the identity recovers the specified
generator rather than merely an abstract automorphism group. -/
theorem hasDerivAt_flowAlgEquiv_zero
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D) (x : A) :
    HasDerivAt (fun s : ℝ => flowAlgEquiv D hD s x) (D x) 0 := by
  simpa using hasDerivAt_flowAlgEquiv D hD x 0

theorem flowAlgEquiv_preserves_functional
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D)
    (ω : A →L[ℝ] ℝ) (hω : ∀ a : A, ω (D a) = 0) (t : ℝ) (x : A) :
    ω (flowAlgEquiv D hD t x) = ω x :=
  flow_preserves_functional D ω hω t x

theorem flowAlgEquiv_preserves_bilinForm
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D)
    (g : A →L[ℝ] A →L[ℝ] ℝ)
    (hg : ∀ x y : A, g (D x) y + g x (D y) = 0) (t : ℝ) (x y : A) :
    g (flowAlgEquiv D hD t x) (flowAlgEquiv D hD t y) = g x y :=
  flow_preserves_bilinForm D g hg t x y

/-- Pointwise preservation in the algebraic carriers of the invariant
Erlangen action, obtained by forgetting continuity without altering values. -/
theorem flowAlgEquivHom_preserves_invariants
    (D : A →L[ℝ] A)
    (hD : IsDerivation (ContinuousLinearMap.mul ℝ A) D)
    (ω : A →L[ℝ] ℝ) (g : A →L[ℝ] A →L[ℝ] ℝ)
    (hω : ∀ a : A, ω (D a) = 0)
    (hg : ∀ x y : A, g (D x) y + g x (D y) = 0)
    (t : Multiplicative ℝ) :
    (∀ x : A, ω.toLinearMap (flowAlgEquivHom D hD t x) = ω.toLinearMap x) ∧
      (∀ x y : A,
        continuousBilinForm g (flowAlgEquivHom D hD t x) (flowAlgEquivHom D hD t y) =
          continuousBilinForm g x y) := by
  exact ⟨flow_preserves_functional D ω hω t.toAdd,
    flow_preserves_bilinForm D g hg t.toAdd⟩

end AlgebraAutomorphisms

section DifferentiateAutomorphismFlows

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- A genuine one-parameter homomorphism acts as the identity at time zero. -/
@[simp] theorem automorphismFlow_zero_apply
    (Φ : Multiplicative ℝ →* (A ≃ₐ[ℝ] A)) (x : A) :
    Φ (Multiplicative.ofAdd (0 : ℝ)) x = x := by
  change (Φ 1) x = x
  rw [map_one]
  rfl

/-- Differentiating the actual multiplicative identity of an automorphism
flow proves that its specified continuous linear generator is a derivation.
Neither the Leibniz rule nor multiplicativity of an exponential is assumed. -/
theorem isDerivation_of_hasDerivAt_automorphismFlow
    (Φ : Multiplicative ℝ →* (A ≃ₐ[ℝ] A)) (D : A →L[ℝ] A)
    (hΦ : ∀ x : A,
      HasDerivAt (fun t : ℝ => Φ (Multiplicative.ofAdd t) x) (D x) 0) :
    IsDerivation (ContinuousLinearMap.mul ℝ A) D := by
  intro x y
  change D (x * y) = D x * y + x * D y
  have hproduct :
      HasDerivAt (fun t : ℝ => Φ (Multiplicative.ofAdd t) (x * y))
        (D x * y + x * D y) 0 := by
    simpa only [map_mul, Pi.mul_apply, automorphismFlow_zero_apply] using
      (hΦ x).mul (hΦ y)
  exact (hΦ (x * y)).unique hproduct

/-- Conservation of a continuous linear functional by an actual differentiable
automorphism flow forces that functional to annihilate the generator. -/
theorem functional_generator_eq_zero_of_flow_invariant
    (Φ : Multiplicative ℝ →* (A ≃ₐ[ℝ] A)) (D : A →L[ℝ] A)
    (hΦ : ∀ x : A,
      HasDerivAt (fun t : ℝ => Φ (Multiplicative.ofAdd t) x) (D x) 0)
    (ω : A →L[ℝ] ℝ)
    (hω : ∀ (t : Multiplicative ℝ) (x : A), ω (Φ t x) = ω x)
    (x : A) : ω (D x) = 0 := by
  have hderivative :
      HasDerivAt (fun _ : ℝ => ω x) (ω (D x)) 0 := by
    simpa only [Function.comp_apply, hω] using
      ω.hasFDerivAt.comp_hasDerivAt 0 (hΦ x)
  exact hderivative.unique (hasDerivAt_const (0 : ℝ) (ω x))

/-- Conservation of a continuous bilinear form by an actual differentiable
automorphism flow forces the generator to satisfy its Killing equation.
Symmetry, positivity, and nondegeneracy of the form are not required. -/
theorem bilinForm_generator_skew_of_flow_invariant
    (Φ : Multiplicative ℝ →* (A ≃ₐ[ℝ] A)) (D : A →L[ℝ] A)
    (hΦ : ∀ x : A,
      HasDerivAt (fun t : ℝ => Φ (Multiplicative.ofAdd t) x) (D x) 0)
    (B : A →L[ℝ] A →L[ℝ] ℝ)
    (hB : ∀ (t : Multiplicative ℝ) (x y : A), B (Φ t x) (Φ t y) = B x y)
    (x y : A) : B (D x) y + B x (D y) = 0 := by
  have hderivative :
      HasDerivAt (fun _ : ℝ => B x y) (B x (D y) + B (D x) y) 0 := by
    simpa only [hB, automorphismFlow_zero_apply] using
      B.hasDerivAt_of_bilinear (fun _ => hΦ x) (fun _ => hΦ y)
  have hzero := hderivative.unique (hasDerivAt_const (0 : ℝ) (B x y))
  simpa only [add_comm] using hzero

end DifferentiateAutomorphismFlows

end InfoGeometry.OperatorAlgebra.OperatorKillingExponential
