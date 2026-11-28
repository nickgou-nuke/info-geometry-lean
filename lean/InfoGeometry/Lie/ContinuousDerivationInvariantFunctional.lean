/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.ContinuousDerivationExponential
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Continuous functionals invariant under a bounded real flow

A continuous real linear functional is fixed by every time of the existing
bounded operator flow exactly when it annihilates the generator. Annihilation
implies invariance by the orbit derivative and the zero-derivative theorem on
`ℝ`; invariance implies annihilation by differentiating the readout at time zero.

The carrier is a complete real normed vector space. Neither multiplication nor
a Leibniz hypothesis is needed for these functional identities. When the
generator is also a derivation of a continuous bilinear multiplication,
`flow_map_mul` in `ContinuousDerivationExponential` independently supplies
multiplicativity of the same flow. Unbounded generators and weights outside a
specified finite domain are not treated here.
-/

noncomputable section

namespace InfoGeometry.Lie.ContinuousDerivationExponential

variable {A : Type*}
variable [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]

/-- An annihilating continuous functional is constant along every orbit of
the bounded real exponential flow. -/
theorem functional_flow_eq_self
    (ω : A →L[ℝ] ℝ) (D : A →L[ℝ] A)
    (hω : ω.comp D = 0) (t : ℝ) (x : A) :
    ω (flow D t x) = ω x := by
  let f : ℝ → ℝ := fun s => ω (flow D s x)
  have hderiv : ∀ s : ℝ, HasDerivAt f 0 s := by
    intro s
    have hz : ω (D (flow D s x)) = 0 := by
      exact congrArg (fun T : A →L[ℝ] ℝ => T (flow D s x)) hω
    have horbit := ω.hasFDerivAt.comp_hasDerivAt s
      (hasStrictDerivAt_orbit D x s).hasDerivAt
    change HasDerivAt f (ω (D (flow D s x))) s at horbit
    rw [hz] at horbit
    exact horbit
  have hdiff : Differentiable ℝ f := fun s => (hderiv s).differentiableAt
  have hzero : ∀ s : ℝ, deriv f s = 0 := fun s => (hderiv s).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hzero t 0
  simpa [f] using hconst

/-- Functional invariance as an equality of continuous linear maps. -/
theorem functional_comp_flow_eq_self
    (ω : A →L[ℝ] ℝ) (D : A →L[ℝ] A)
    (hω : ω.comp D = 0) (t : ℝ) :
    ω.comp (flow D t) = ω := by
  ext x
  exact functional_flow_eq_self ω D hω t x

/-- Invariance at every time forces the functional to annihilate the
infinitesimal generator. -/
theorem functional_comp_eq_zero_of_flow_invariant
    (ω : A →L[ℝ] ℝ) (D : A →L[ℝ] A)
    (hflow : ∀ t : ℝ, ω.comp (flow D t) = ω) :
    ω.comp D = 0 := by
  ext x
  change ω (D x) = 0
  have hderiv :
      HasDerivAt (fun t : ℝ => ω (flow D t x)) (ω (D x)) 0 := by
    have horbit := ω.hasFDerivAt.comp_hasDerivAt 0
      (hasStrictDerivAt_orbit D x 0).hasDerivAt
    change HasDerivAt (fun t : ℝ => ω (flow D t x))
      (ω (D (flow D 0 x))) 0 at horbit
    rw [flow_zero] at horbit
    exact horbit
  have hfun :
      (fun t : ℝ => ω (flow D t x)) = (fun _ : ℝ => ω x) := by
    funext t
    exact congrArg (fun T : A →L[ℝ] ℝ => T x) (hflow t)
  rw [hfun] at hderiv
  exact hderiv.unique (hasDerivAt_const 0 (ω x))

/-- Exact equivalence between flow invariance and infinitesimal
annihilation of the bounded generator. -/
theorem functional_flow_invariant_iff
    (ω : A →L[ℝ] ℝ) (D : A →L[ℝ] A) :
    (∀ t : ℝ, ω.comp (flow D t) = ω) ↔ ω.comp D = 0 := by
  constructor
  · exact functional_comp_eq_zero_of_flow_invariant ω D
  · intro hω t
    exact functional_comp_flow_eq_self ω D hω t

end InfoGeometry.Lie.ContinuousDerivationExponential

end
