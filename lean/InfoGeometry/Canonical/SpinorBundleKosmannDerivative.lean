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
    (C : ∀ x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x)
    (ψ : ∀ x : M, V x) : ∀ x : M, V x :=
  fun x => cov ψ x (X x) - C x (X x) (ψ x)

/-- The correction is tensorial in the vector-field direction: both the
covariant derivative and its one-form correction are linear in `X x`. -/
theorem connectionCorrectedDerivative_tangent_smul
    (cov : CovariantDerivative I F V)
    (X : ∀ x : M, TangentSpace I x)
    (C : ∀ x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x)
    (ψ : ∀ x : M, V x) (r : ℝ) (x : M) :
    connectionCorrectedDerivative I cov (fun y => r • X y) C ψ x =
      r • connectionCorrectedDerivative I cov X C ψ x := by
  simp [connectionCorrectedDerivative]
  module

/-- Additivity in the tangent direction, the other half of tensoriality. -/
theorem connectionCorrectedDerivative_tangent_add
    (cov : CovariantDerivative I F V)
    (X Y : ∀ x : M, TangentSpace I x)
    (C : ∀ x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x)
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
    (C : ∀ x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x)
    {ψ : ∀ x : M, V x} {g : M → ℝ} {x : M}
    (hψ : MDiffAt (T% ψ) x) (hg : MDiffAt g x) :
    connectionCorrectedDerivative I cov X C (g • ψ) x =
      g x • connectionCorrectedDerivative I cov X C ψ x +
        (d% g x (X x)) • ψ x := by
  simp only [connectionCorrectedDerivative]
  rw [cov.isCovariantDerivativeOn.leibniz hψ hg]
  change (g x • cov ψ x (X x) + (d% g x (X x)) • ψ x) -
      C x (X x) (g x • ψ x) =
    g x • (cov ψ x (X x) - C x (X x) (ψ x)) +
      (d% g x (X x)) • ψ x
  rw [ContinuousLinearMap.map_smul]
  module



end InfoGeometry.Canonical.SpinorBundleKosmannDerivative

end
