import InfoGeometry.Convex.Bregman
import Mathlib.Order.Closure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bregman Divergence and Fenchel Duality (1D)

This file develops a minimal, fully self-contained 1D
dually-flat information geometry layer:

• Bregman divergence
• Three-point identity
• Pythagorean inequality
• Fenchel–Young inequality
• Fenchel gap
• Equality characterization
• Dual-flat potential structure

No supremum machinery is used.
-/

namespace InfoGeometry
namespace Convex
namespace OneD

/-- Compatibility alias to the canonical three-point identity in `InfoGeometry.Convex.Bregman`. -/
lemma bregmanDiv_three_point
    (f : ℝ → ℝ) (x y z : ℝ) :
    bregmanDiv f x z
      =
      bregmanDiv f x y
        + bregmanDiv f y z
        + (deriv f y - deriv f z) * (x - y) := by
  simpa using bregmanThreePoint f x y z

/-- Compatibility alias to the canonical Pythagorean inequality in `InfoGeometry.Convex.Bregman`. -/
lemma bregmanDiv_pythagorean_ineq
    (f : ℝ → ℝ) (x y z : ℝ)
    (hproj : 0 ≤ (deriv f y - deriv f z) * (x - y)) :
    bregmanDiv f x z ≥
      bregmanDiv f x y + bregmanDiv f y z := by
  simpa using bregmanPythagoreanIneq f x y z hproj

-- ------------------------------------------------------------
-- Fenchel Duality Layer
-- ------------------------------------------------------------

section ConvexDuality

/-- `fStar` is a Fenchel upper bound for `f` if it upper-bounds all affine supports. -/
def IsFenchelUpperBound (f fStar : ℝ → ℝ) : Prop :=
  ∀ η θ, η * θ - f θ ≤ fStar η

/-- Compatibility alias: a weak Legendre-conjugacy interface via Fenchel upper bounds. -/
def IsLegendreConjugate (f fStar : ℝ → ℝ) : Prop :=
  IsFenchelUpperBound f fStar

/-- Fenchel gap associated to a primal/dual pair. -/
def fenchelGap (f fStar : ℝ → ℝ) (θ η : ℝ) : ℝ :=
  f θ + fStar η - η * θ

lemma fenchelYoung_ineq
    {f fStar : ℝ → ℝ}
    (hConj : IsLegendreConjugate f fStar)
    (θ η : ℝ) :
    η * θ ≤ f θ + fStar η := by
  have h := hConj η θ
  linarith

lemma fenchelGap_nonneg_of_conjugate
    {f fStar : ℝ → ℝ}
    (hConj : IsLegendreConjugate f fStar)
    (θ η : ℝ) :
    0 ≤ fenchelGap f fStar θ η := by
  unfold fenchelGap
  have h := hConj η θ
  linarith

lemma fenchelGap_eq_zero_of_equality
    {f fStar : ℝ → ℝ}
    (θ η : ℝ)
    (h : fStar η = η * θ - f θ) :
    fenchelGap f fStar θ η = 0 := by
  unfold fenchelGap
  simp [h]

lemma fenchelYoung_eq_of_gap_zero
    {f fStar : ℝ → ℝ}
    (θ η : ℝ)
    (hgap : fenchelGap f fStar θ η = 0) :
    fStar η = η * θ - f θ := by
  unfold fenchelGap at hgap
  linarith

-- ------------------------------------------------------------
-- Gradient Compatibility and Dual-Flat Structure
-- ------------------------------------------------------------

/-- Legendre identity along the gradient pairing. -/
def IsGradientDual (f fStar : ℝ → ℝ) : Prop :=
  ∀ θ, fStar (deriv f θ)
        = deriv f θ * θ - f θ

lemma fenchelGap_zero_of_gradient
    {f fStar : ℝ → ℝ}
    (hGrad : IsGradientDual f fStar)
    (θ : ℝ) :
    fenchelGap f fStar θ (deriv f θ) = 0 := by
  unfold IsGradientDual at hGrad
  have h := hGrad θ
  exact fenchelGap_eq_zero_of_equality θ (deriv f θ) h

/-- Relation between Bregman divergence and Fenchel gap. -/
lemma bregman_as_fenchelGap
    (f fStar : ℝ → ℝ)
    (x y : ℝ)
    (hGrad : IsGradientDual f fStar) :
    bregmanDiv f x y
      =
      fenchelGap f fStar x (deriv f y) := by
  unfold bregmanDiv fenchelGap
  have h := hGrad y
  simp [h]
  ring

-- ------------------------------------------------------------
-- Dual-Flat Potential Structure
-- ------------------------------------------------------------

/-- Minimal data for 1D dual-flat information geometry. -/
structure DualFlatPotential where
  primal : ℝ → ℝ
  dual : ℝ → ℝ
  conjugate : IsLegendreConjugate primal dual
  gradientDual : IsGradientDual primal dual

lemma DualFlatPotential.fenchelGap_nonneg
    (D : DualFlatPotential)
    (θ η : ℝ) :
    0 ≤ fenchelGap D.primal D.dual θ η :=
  fenchelGap_nonneg_of_conjugate D.conjugate θ η

lemma DualFlatPotential.fenchelGap_zero
    (D : DualFlatPotential)
    (θ : ℝ) :
    fenchelGap D.primal D.dual θ
      (deriv D.primal θ) = 0 :=
  fenchelGap_zero_of_gradient D.gradientDual θ

lemma DualFlatPotential.bregman_as_gap
    (D : DualFlatPotential)
    (x y : ℝ) :
    bregmanDiv D.primal x y
      =
      fenchelGap D.primal D.dual x
        (deriv D.primal y) :=
  bregman_as_fenchelGap
    D.primal D.dual x y D.gradientDual

end ConvexDuality
-- ------------------------------------------------------------
-- Fenchel–Legendre Dual Equivalence
-- ------------------------------------------------------------

/-- Equality in Fenchel–Young characterizes gradient pairing. -/
lemma fenchel_legendre_equivalence
    {f fStar : ℝ → ℝ}
    (hGrad : IsGradientDual f fStar)
    (θ η : ℝ) :
    (fStar η = deriv f θ * θ - f θ) →
    (hθ : θ ≠ 0) →
    fenchelGap f fStar θ η = 0
      ↔ η = deriv f θ := by
  intro hEqGrad hθ
  constructor
  · intro hgap
    -- equality case of Fenchel–Young
    have hEq := fenchelYoung_eq_of_gap_zero θ η hgap
    -- compare with the provided gradient-form value of `fStar η`
    have :
        η * θ - f θ
        =
        deriv f θ * θ - f θ := by
      calc
        η * θ - f θ = fStar η := by linarith [hEq]
        _ = deriv f θ * θ - f θ := hEqGrad
    have hmul : (η - deriv f θ) * θ = 0 := by
      linarith [this]
    have hdiff : η - deriv f θ = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_right hθ
    linarith
  · intro hη
    subst hη
    exact fenchelGap_zero_of_gradient hGrad θ

/-- `fenchel_legendre_equivalence` with an explicit name for its value-matching hypothesis. -/
lemma fenchelGap_zero_iff_eq_deriv_of_dual_value_match
    {f fStar : ℝ → ℝ}
    (hGrad : IsGradientDual f fStar)
    (θ η : ℝ)
    (hEqGrad : fStar η = deriv f θ * θ - f θ)
    (hθ : θ ≠ 0) :
    fenchelGap f fStar θ η = 0 ↔ η = deriv f θ :=
  fenchel_legendre_equivalence hGrad θ η hEqGrad hθ

/-- Gradient pairing realizes Fenchel–Young equality. -/
lemma fenchel_young_eq_gradient
    {f fStar : ℝ → ℝ}
    (hGrad : IsGradientDual f fStar)
    (θ : ℝ) :
    f θ + fStar (deriv f θ)
      =
      θ * deriv f θ := by
  unfold IsGradientDual at hGrad
  have h := hGrad θ
  simp [h]
  ring

/-!
## Pure Order-Theoretic Kernel Closure

This section isolates a purely lattice-level closure package induced by a
self-adjoint Galois connection.

No convexity, topology, or analytic hypotheses are used.
-/

section OrderKernel

universe u v

variable {α : Type u} [CompleteLattice α]
variable {X : Type v}

/-- Kernel transform on function lattices: pointwise supremum of kernel-meets. -/
noncomputable def KernelOp (Φ : X → X → α) (f : X → α) : X → α :=
  fun y => ⨆ x : X, Φ x y ⊓ f x

lemma kernelOp_monotone (Φ : X → X → α) :
    Monotone (KernelOp Φ) := by
  intro f g hfg y
  refine iSup_le ?_
  intro x
  exact le_iSup_of_le x (inf_le_inf_left _ (hfg x))

/-- Symmetry rewrites the kernel operator against the transposed kernel. -/
lemma kernelOp_eq_transpose (Φ : X → X → α)
    (hΦ : ∀ x y, Φ x y = Φ y x) :
    KernelOp Φ = KernelOp (fun x y => Φ y x) := by
  funext f
  funext y
  simp [KernelOp, hΦ]

/-- Closure induced by double application of `KernelOp`. -/
noncomputable def KernelClosure (Φ : X → X → α) (f : X → α) : X → α :=
  KernelOp Φ (KernelOp Φ f)

lemma kernelClosure_monotone (Φ : X → X → α)
    (hgc : GaloisConnection (KernelOp Φ) (KernelOp Φ)) :
    Monotone (KernelClosure Φ) := by
  simpa [KernelClosure, Function.comp] using
    (GaloisConnection.monotone_u hgc).comp (GaloisConnection.monotone_l hgc)

lemma kernel_le_closure (Φ : X → X → α)
    (hgc : GaloisConnection (KernelOp Φ) (KernelOp Φ)) (f : X → α) :
    f ≤ KernelClosure Φ f :=
  GaloisConnection.le_u_l hgc f

lemma kernel_idempotent (Φ : X → X → α)
    (hgc : GaloisConnection (KernelOp Φ) (KernelOp Φ)) (f : X → α) :
    KernelClosure Φ (KernelClosure Φ f) = KernelClosure Φ f := by
  simpa [KernelClosure, Function.comp] using
    GaloisConnection.u_l_u_eq_u hgc (KernelOp Φ f)

/-- Bundled closure operator induced by a self-adjoint Galois connection. -/
noncomputable def KernelClosureOperator (Φ : X → X → α)
    (hgc : GaloisConnection (KernelOp Φ) (KernelOp Φ)) :
    ClosureOperator (X → α) where
  toOrderHom :=
    { toFun := KernelClosure Φ
      monotone' := kernelClosure_monotone Φ hgc }
  le_closure' := kernel_le_closure Φ hgc
  idempotent' := kernel_idempotent Φ hgc

/-- Closed points for the kernel closure. -/
def IsKernelClosed (Φ : X → X → α) (f : X → α) : Prop :=
  KernelClosure Φ f = f

/-- Type of closed elements for a fixed kernel. -/
abbrev KernelClosedFunctions (Φ : X → X → α) :=
  {f : X → α // IsKernelClosed Φ f}

/-- Closed elements inherit a complete lattice structure. -/
noncomputable instance kernelClosedFunctionsCompleteLattice (Φ : X → X → α)
    (hgc : GaloisConnection (KernelOp Φ) (KernelOp Φ)) :
    CompleteLattice (KernelClosedFunctions Φ) := by
  simpa [KernelClosedFunctions, IsKernelClosed, KernelClosureOperator, KernelClosure]
    using (KernelClosureOperator Φ hgc).gi.liftCompleteLattice

end OrderKernel

end OneD
end Convex
end InfoGeometry
