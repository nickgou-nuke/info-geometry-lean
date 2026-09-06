import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import InfoGeometry.Convex.Bregman

/-!
# Abstract Fenchel-Legendre Duality

This file provides an abstract convex-duality layer on real inner product spaces:

- convex differentiable functionals (`ConvexFunctional`)
- gradient map (`grad`)
- Fenchel conjugate (`legendre`)
- Fenchel-Young inequality
- equality case under a supporting-hyperplane hypothesis
- gradient injectivity under strict monotonicity

The file is intentionally abstract and separates assumptions from derived theorems.

For `ConvexFunctional.legendre`, this is a real-valued `sSup` model; theorems use
explicit bounded-above hypotheses where needed. A fully general conjugate is usually
formulated in `EReal`.
-/

namespace InfoGeometry.Convex

open Set
open scoped Classical

/-- A convex differentiable functional on a real inner product space. -/
structure ConvexFunctional
    (V : Type _)
    [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    [CompleteSpace V] where
  F : V → ℝ
  convex : ConvexOn ℝ Set.univ F
  diff : Differentiable ℝ F

namespace ConvexFunctional

variable
  {V : Type _}
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [CompleteSpace V]

/-- Gradient of a convex functional. -/
noncomputable def grad (Φ : ConvexFunctional V) (x : V) : V :=
  gradient Φ.F x

/-- Affine support set used to define the Fenchel conjugate at `y`. -/
def affineSet (Φ : ConvexFunctional V) (y : V) : Set ℝ :=
  { r : ℝ | ∃ x : V, r = inner ℝ x y - Φ.F x }

/-- Fenchel conjugate (`Legendre` transform). -/
noncomputable def legendre (Φ : ConvexFunctional V) (y : V) : ℝ :=
  sSup (Φ.affineSet y)

lemma affineSet_nonempty (Φ : ConvexFunctional V) (y : V) :
    (Φ.affineSet y).Nonempty := by
  refine ⟨inner ℝ (0 : V) y - Φ.F 0, ?_⟩
  exact ⟨0, rfl⟩

/-- Fenchel-Young inequality:
`Φ(x) + Φ*(y) ≥ ⟪x,y⟫` when the conjugate-defining set is bounded above. -/
theorem fenchel_young
    (Φ : ConvexFunctional V)
    (x y : V)
    (hbounded : BddAbove (Φ.affineSet y)) :
    Φ.F x + Φ.legendre y ≥ inner ℝ x y := by
  have hx : inner ℝ x y - Φ.F x ∈ Φ.affineSet y := by
    exact ⟨x, rfl⟩
  have hle : inner ℝ x y - Φ.F x ≤ Φ.legendre y := by
    exact le_csSup hbounded hx
  linarith

/-- First-order supporting-hyperplane inequality for convex differentiable functionals. -/
theorem supporting_ineq_of_convex_differentiable
    (Φ : ConvexFunctional V)
    (x z : V) :
    Φ.F z ≥ Φ.F x + inner ℝ (Φ.grad x) (z - x) := by
  let g : ℝ → ℝ := fun t => Φ.F (AffineMap.lineMap x z t)
  have hconv : ConvexOn ℝ Set.univ g := by
    simpa [g] using (Φ.convex.comp_affineMap (AffineMap.lineMap x z))
  have hcomp :
      HasDerivAt g ((fderiv ℝ Φ.F x) (z - x)) 0 := by
    simpa [g] using
      (Φ.diff x).hasFDerivAt.comp_hasDerivAt_of_eq
        (0 : ℝ)
        (AffineMap.hasDerivAt_lineMap (a := x) (b := z))
        (by simp)
  have hgrad :
      inner ℝ (Φ.grad x) (z - x) = (fderiv ℝ Φ.F x) (z - x) := by
    simpa [grad] using
      (inner_gradient_left (𝕜 := ℝ) (f := Φ.F) (x := x) (y := z - x) (h := Φ.diff x))
  have hderiv :
      deriv g 0 = inner ℝ (Φ.grad x) (z - x) := by
    calc
      deriv g 0 = (fderiv ℝ Φ.F x) (z - x) := hcomp.deriv
      _ = inner ℝ (Φ.grad x) (z - x) := hgrad.symm
  have hslope :
      deriv g 0 ≤ slope g 0 1 := by
    exact hconv.deriv_le_slope (by simp) (by simp) (by norm_num) hcomp.differentiableAt
  have hslopeEval : slope g 0 1 = Φ.F z - Φ.F x := by
    simp [g, slope_def_field]
  have hmain : inner ℝ (Φ.grad x) (z - x) ≤ Φ.F z - Φ.F x := by
    calc
      inner ℝ (Φ.grad x) (z - x) = deriv g 0 := by simpa using hderiv.symm
      _ ≤ slope g 0 1 := hslope
      _ = Φ.F z - Φ.F x := hslopeEval
  linarith

/-- Equality case in Fenchel-Young under a supporting-hyperplane hypothesis. -/
theorem fenchel_young_eq_of_supporting
    (Φ : ConvexFunctional V)
    (x : V)
    (hbounded : BddAbove (Φ.affineSet (Φ.grad x)))
    (hsupport : ∀ z : V, Φ.F z ≥ Φ.F x + inner ℝ (Φ.grad x) (z - x)) :
    Φ.F x + Φ.legendre (Φ.grad x) = inner ℝ x (Φ.grad x) := by
  let g : V := Φ.grad x
  have hlower : inner ℝ x g - Φ.F x ≤ Φ.legendre g := by
    exact le_csSup hbounded ⟨x, rfl⟩
  have hupp : Φ.legendre g ≤ inner ℝ x g - Φ.F x := by
    unfold legendre
    refine csSup_le (Φ.affineSet_nonempty g) ?_
    intro r hr
    rcases hr with ⟨z, rfl⟩
    have hinner : inner ℝ g (z - x) = inner ℝ z g - inner ℝ x g := by
      simp [inner_sub_right, real_inner_comm]
    have hs : Φ.F z ≥ Φ.F x + (inner ℝ z g - inner ℝ x g) := by
      simpa [g, hinner] using hsupport z
    linarith
  have hge : Φ.F x + Φ.legendre g ≥ inner ℝ x g := by
    linarith
  have hle : Φ.F x + Φ.legendre g ≤ inner ℝ x g := by
    linarith
  exact le_antisymm hle hge

/-- Equality case in Fenchel-Young at `y = ∇Φ(x)`, derived from convex first-order support. -/
theorem fenchel_young_eq_of_grad
    (Φ : ConvexFunctional V)
    (x : V)
    (hbounded : BddAbove (Φ.affineSet (Φ.grad x))) :
    Φ.F x + Φ.legendre (Φ.grad x) = inner ℝ x (Φ.grad x) := by
  exact
    Φ.fenchel_young_eq_of_supporting x hbounded
      (Φ.supporting_ineq_of_convex_differentiable x)

/-- Strict convexity predicate (global, on `Set.univ`). -/
def StrictConvex (Φ : ConvexFunctional V) : Prop :=
  StrictConvexOn ℝ Set.univ Φ.F

/-- Strict monotonicity of the gradient map. -/
def StrictMonotoneGrad (Φ : ConvexFunctional V) : Prop :=
  ∀ ⦃x y : V⦄, x ≠ y → 0 < inner ℝ (Φ.grad x - Φ.grad y) (x - y)

/-- Injectivity of gradient from strict monotonicity. -/
theorem grad_injective_of_strictMonotone
    (Φ : ConvexFunctional V)
    (hmono : Φ.StrictMonotoneGrad) :
    Function.Injective (Φ.grad) := by
  intro x y hxy
  by_contra hne
  have hpos : 0 < inner ℝ (Φ.grad x - Φ.grad y) (x - y) := hmono hne
  have hzero : inner ℝ (Φ.grad x - Φ.grad y) (x - y) = 0 := by
    simp [hxy]
  linarith

end ConvexFunctional

/-!
## One-Dimensional Legendre Potentials

This layer packages a smooth strictly convex real potential with the standard
1D geometric objects: derivative coordinate map, Fisher scalar, and a
structural Legendre transform.
-/

/-- A `C²` strictly convex potential on `ℝ`. -/
structure LegendrePotential where
  f : ℝ → ℝ
  smooth : ContDiff ℝ 2 f
  strict_convex : StrictConvexOn ℝ Set.univ f

namespace LegendrePotential

lemma differentiable (L : LegendrePotential) :
    Differentiable ℝ L.f :=
  L.smooth.differentiable (by norm_num)

lemma differentiableOn (L : LegendrePotential) :
    DifferentiableOn ℝ L.f Set.univ :=
  L.differentiable.differentiableOn

/-!
### Gradient monotonicity and injectivity
-/

lemma deriv_strictMono (L : LegendrePotential) :
    StrictMono (deriv L.f) := by
  intro x y hxy
  have hmonoOn : StrictMonoOn (deriv L.f) Set.univ :=
    L.strict_convex.strictMonoOn_deriv
      (fun z _hz => L.differentiable z)
  exact hmonoOn (by simp) (by simp) hxy

lemma grad_injective (L : LegendrePotential) :
    Function.Injective (deriv L.f) :=
  L.deriv_strictMono.injective

/-!
### Fisher information (1D)
-/

/-- Fisher scalar in natural coordinates, given by the second derivative. -/
noncomputable def fisher (L : LegendrePotential) (θ : ℝ) : ℝ :=
  deriv (deriv L.f) θ

/-!
### Dual coordinate map
-/

/-- Dual coordinate map `η(θ) = f'(θ)`. -/
noncomputable def eta (L : LegendrePotential) : ℝ → ℝ :=
  deriv L.f

lemma eta_strictMono (L : LegendrePotential) :
    StrictMono (eta L) :=
  L.deriv_strictMono

lemma eta_injective (L : LegendrePotential) :
    Function.Injective (eta L) :=
  L.eta_strictMono.injective

/-- Inverse map selected by `Function.invFun`. -/
noncomputable def thetaOfEta (L : LegendrePotential) : ℝ → ℝ :=
  Function.invFun (eta L)

lemma theta_eta_leftInverse (L : LegendrePotential) :
    Function.LeftInverse (thetaOfEta L) (eta L) :=
  Function.leftInverse_invFun L.eta_injective

@[simp]
lemma thetaOfEta_eta (L : LegendrePotential) (θ : ℝ) :
    thetaOfEta L (eta L θ) = θ :=
  L.theta_eta_leftInverse θ

/--
One-dimensional inverse-Hessian/Fisher relation for Legendre coordinates.

This is the analytic core of the informal statement
`Hess(S) = Fisher⁻¹` in the scalar Legendre lane.  The theorem does not assert
that the inverse coordinate is differentiable for free: it takes the required
derivative witnesses explicitly.  Differentiating
`thetaOfEta (eta θ) = θ` gives `a * fisher θ = 1`; away from the spinodal
surface `fisher θ = 0`, the inverse-coordinate derivative is the reciprocal
Fisher scalar.
-/
theorem thetaOfEta_deriv_eq_inv_fisher_of_hasDerivAt
    (L : LegendrePotential) (θ a : ℝ)
    (hEta : HasDerivAt (eta L) (L.fisher θ) θ)
    (hTheta : HasDerivAt (thetaOfEta L) a (eta L θ))
    (hFisher : L.fisher θ ≠ 0) :
    a = (L.fisher θ)⁻¹ := by
  have hcomp :
      deriv (fun x : ℝ => thetaOfEta L (eta L x)) θ =
        a * L.fisher θ := by
    simpa [Function.comp_def] using (hTheta.comp θ hEta).deriv
  have hfun :
      (fun x : ℝ => thetaOfEta L (eta L x)) = fun x : ℝ => x := by
    funext x
    simp [thetaOfEta_eta]
  rw [hfun] at hcomp
  have hid : deriv (fun x : ℝ => x) θ = 1 := by
    simp
  have hmul : a * L.fisher θ = 1 := by
    linarith
  calc
    a = (a * L.fisher θ) / L.fisher θ := by
      field_simp [hFisher]
    _ = (L.fisher θ)⁻¹ := by
      rw [hmul]
      field_simp [hFisher]

/-!
### Legendre transform (structural)
-/

/-- Bregman divergence generated by the potential `f`. -/
noncomputable abbrev bregman (L : LegendrePotential) (θ θ' : ℝ) : ℝ :=
  InfoGeometry.bregmanDiv L.f θ θ'

@[simp] lemma bregman_def (L : LegendrePotential) (θ θ' : ℝ) :
    L.bregman θ θ' = InfoGeometry.bregmanDiv L.f θ θ' := rfl

/-- Compatibility alias for `bregman` as divergence energy gap. -/
@[deprecated bregman (since := "2026-02-18")]
noncomputable def divergence (L : LegendrePotential) (θ θ' : ℝ) : ℝ :=
  L.bregman θ θ'

/-- Structural Legendre transform using the chosen inverse dual coordinate. -/
noncomputable def legendreTransform (L : LegendrePotential) (η : ℝ) : ℝ :=
  η * thetaOfEta L η - L.f (thetaOfEta L η)

/-- On the image of `η = f'`, the structural transform has the expected pointwise form. -/
@[simp] lemma legendreTransform_eta (L : LegendrePotential) (θ : ℝ) :
    legendreTransform L (eta L θ) = θ * eta L θ - L.f θ := by
  calc
    legendreTransform L (eta L θ)
        = eta L θ * thetaOfEta L (eta L θ) - L.f (thetaOfEta L (eta L θ)) := by
            simp [legendreTransform]
    _ = eta L θ * θ - L.f θ := by
          simp [thetaOfEta_eta]
    _ = θ * eta L θ - L.f θ := by
          ring

/-- Compatibility alias for `legendreTransform`. -/
@[deprecated legendreTransform (since := "2026-02-18")]
noncomputable def legendre (L : LegendrePotential) (η : ℝ) : ℝ :=
  L.legendreTransform η

/-!
### Bridge to the abstract convex-functional layer
-/

/-- `LegendrePotential` as an abstract `ConvexFunctional` on `ℝ`. -/
noncomputable def toConvexFunctional (L : LegendrePotential) : ConvexFunctional ℝ where
  F := L.f
  convex := L.strict_convex.convexOn
  diff := L.differentiable

/-- 1D Fenchel-Young equality at gradient points, via `ConvexFunctional`. -/
theorem fenchel_young_eq_of_grad
    (L : LegendrePotential)
    (θ : ℝ)
    (hbounded :
      BddAbove ((toConvexFunctional L).affineSet ((toConvexFunctional L).grad θ))) :
    (toConvexFunctional L).F θ
      + (toConvexFunctional L).legendre ((toConvexFunctional L).grad θ)
      = inner ℝ θ ((toConvexFunctional L).grad θ) := by
  simpa using
    (ConvexFunctional.fenchel_young_eq_of_grad
      (Φ := toConvexFunctional L) (x := θ) hbounded)

/-- Nonnegativity of the 1D Fisher scalar from strict convexity. -/
lemma fisher_nonneg (L : LegendrePotential) (θ : ℝ) :
    0 ≤ fisher L θ := by
  have hmono : Monotone (deriv L.f) := L.deriv_strictMono.monotone
  unfold fisher
  simpa using (Monotone.deriv_nonneg (g := deriv L.f) (x := θ) hmono)

end LegendrePotential

end InfoGeometry.Convex
