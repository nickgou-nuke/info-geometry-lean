/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Connection-corrected derivatives on real vector bundles

This module isolates the bundle-level algebra needed by a spinorial Lie
derivative. It works over a genuine Mathlib vector bundle and covariant
derivative. The correction is a one-form with values in continuous fiber
endomorphisms. Consequently the corrected operator is linear in its tangent
direction and satisfies the scalar Leibniz rule in the section argument.

This is an intermediate result, not the full Kosmann construction: identifying
the correction with the Clifford lift of the skew covariant derivative of a
Killing field requires a spinor bundle, a compatible Clifford action, and the
relevant metric and connection compatibility theorems.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace InfoGeometry.Canonical.SpinorBundleKosmannDerivative

variable {E H M F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V]

/-- A covariant derivative corrected by a pointwise endomorphism field.
The argument order of `cov` is Mathlib's: `cov ψ x (X x)` is `∇_X ψ` at `x`.
-/
def connectionCorrectedDerivative
    (cov : CovariantDerivative I F V)
    (X : ∀ x : M, TangentSpace I x)
    (C : ∀ x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    (ψ : ∀ x : M, V x) : ∀ x : M, V x :=
  fun x => cov ψ x (X x) - C x (ψ x) (X x)

/-- The pointwise endomorphism correction assembled into an actual Mathlib
covariant derivative on the same real vector bundle.  The minus sign is part
of the convention in `connectionCorrectedDerivative`; its type is exactly
Mathlib's endomorphism-valued one-form type. -/
def connectionCorrectedCovariantDerivative
    (cov : CovariantDerivative I F V)
    (C : ∀ x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x) :
    CovariantDerivative I F V :=
  cov.addOneForm (fun x => -(C x))

/-- Evaluation of the corrected bundle connection is exactly the directional
operator defined above.  This identifies the one-form construction with its
actual covariant-derivative action, rather than merely asserting the Leibniz
law for an unrelated pointwise formula. -/
theorem connectionCorrectedCovariantDerivative_apply
    (cov : CovariantDerivative I F V)
    (C : ∀ x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    (X : ∀ x : M, TangentSpace I x)
    (ψ : ∀ x : M, V x) (x : M) :
    connectionCorrectedCovariantDerivative I cov C ψ x (X x) =
      connectionCorrectedDerivative I cov X C ψ x := by
  simp [connectionCorrectedCovariantDerivative, connectionCorrectedDerivative,
    CovariantDerivative.addOneForm]
  abel

/-- The actual corrected bundle connection satisfies the covariant scalar
Leibniz identity, including the derivative term, on every smooth section and
scalar field. -/
theorem connectionCorrectedCovariantDerivative_leibniz
    (cov : CovariantDerivative I F V)
    (C : ∀ x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    {ψ : ∀ x : M, V x} {g : M → ℝ} {x : M}
    (hψ : MDiffAt (T% ψ) x) (hg : MDiffAt g x) :
    connectionCorrectedCovariantDerivative I cov C (g • ψ) x =
      g x • connectionCorrectedCovariantDerivative I cov C ψ x +
        (d% g x).smulRight (ψ x) := by
  exact (connectionCorrectedCovariantDerivative I cov C).isCovariantDerivativeOnUniv.leibniz
    hψ hg

/-- The correction is tensorial in the vector-field direction: both the
covariant derivative and its one-form correction are linear in `X x`. -/
theorem connectionCorrectedDerivative_tangent_smul
    (cov : CovariantDerivative I F V)
    (X : ∀ x : M, TangentSpace I x)
    (C : ∀ x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    (ψ : ∀ x : M, V x) (r : ℝ) (x : M) :
    connectionCorrectedDerivative I cov (fun y => r • X y) C ψ x =
      r • connectionCorrectedDerivative I cov X C ψ x := by
  simp [connectionCorrectedDerivative]
  module

/-- Additivity in the tangent direction, the other half of tensoriality. -/
theorem connectionCorrectedDerivative_tangent_add
    (cov : CovariantDerivative I F V)
    (X Y : ∀ x : M, TangentSpace I x)
    (C : ∀ x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    (ψ : ∀ x : M, V x) (x : M) :
    connectionCorrectedDerivative I cov (fun y => X y + Y y) C ψ x =
      connectionCorrectedDerivative I cov X C ψ x +
        connectionCorrectedDerivative I cov Y C ψ x := by
  simp [connectionCorrectedDerivative]
  abel

/-- The connection-corrected derivative obeys the scalar Leibniz rule.
The correction contributes no derivative term because each `C x` is a
continuous linear map on the fiber. -/
theorem connectionCorrectedDerivative_smul
    (cov : CovariantDerivative I F V)
    (X : ∀ x : M, TangentSpace I x)
    (C : ∀ x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    {ψ : ∀ x : M, V x} {g : M → ℝ} {x : M}
    (hψ : MDiffAt (T% ψ) x) (hg : MDiffAt g x) :
    connectionCorrectedDerivative I cov X C (g • ψ) x =
      g x • connectionCorrectedDerivative I cov X C ψ x +
        (d% g x (X x)) • ψ x := by
  simp only [connectionCorrectedDerivative]
  rw [cov.isCovariantDerivativeOn.leibniz hψ hg]
  change (g x • cov ψ x (X x) + (d% g x (X x)) • ψ x) -
      C x (g x • ψ x) (X x) =
    g x • (cov ψ x (X x) - C x (ψ x) (X x)) +
      (d% g x (X x)) • ψ x
  rw [ContinuousLinearMap.map_smul]
  simp only [smul_apply]
  module



end InfoGeometry.Canonical.SpinorBundleKosmannDerivative

end
