/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationGaugeTransport
import InfoGeometry.OperatorAlgebra.DerivationCurvatureVariation
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Cyclic trace action and its exact quartic variation

The pairing is a native bilinear form on the existing operator-valued
two-cochain space. Only the trace is cyclic; the coefficient algebra and the
derivation directions are not assumed to commute. The finite family of
directions is not assumed to be a basis or orthonormal frame. This is a finite
algebraic trace-square functional, with no positivity or integral claim.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra
open LieModule.Cohomology

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)
variable {ι : Type*} [Fintype ι]

/-- The finite cyclic trace pairing on native operator-valued two-cochains. -/
def curvatureTracePairing (τ : A →ₗ[R] R) (frame : ι → K.L) :
    LinearMap.BilinForm R (TwoForm K) :=
  LinearMap.mk₂ R
    (fun F G => ∑ i, ∑ j, τ (F (frame i) (frame j) * G (frame i) (frame j)))
    (by
      intro F G H
      simp only [add_apply_apply, add_mul, map_add, Finset.sum_add_distrib])
    (by
      intro t F G
      simp only [smul_apply_apply, smul_mul_assoc, map_smul, Finset.smul_sum])
    (by
      intro F G H
      simp only [add_apply_apply, mul_add, map_add, Finset.sum_add_distrib])
    (by
      intro t F G
      simp only [smul_apply_apply, mul_smul_comm, map_smul, Finset.smul_sum])

@[simp] theorem curvatureTracePairing_apply
    (τ : A →ₗ[R] R) (frame : ι → K.L) (F G : TwoForm K) :
    curvatureTracePairing K τ frame F G =
      ∑ i, ∑ j, τ (F (frame i) (frame j) * G (frame i) (frame j)) := rfl

/-- Cyclicity of the trace supplies symmetry of the pairing. -/
theorem curvatureTracePairing_comm
    (τ : A →ₗ[R] R) (frame : ι → K.L)
    (hcyclic : ∀ a b, τ (a * b) = τ (b * a)) (F G : TwoForm K) :
    curvatureTracePairing K τ frame F G =
      curvatureTracePairing K τ frame G F := by
  simp only [curvatureTracePairing_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact hcyclic _ _

/-- The trace-square functional of the actual noncommutative curvature. -/
def curvatureTraceAction (τ : A →ₗ[R] R) (frame : ι → K.L) (Γ : OneForm K) : R :=
  curvatureTracePairing K τ frame (connectionCurvature K Γ) (connectionCurvature K Γ)

/-- Full invertible gauge transport preserves this cyclic trace action. -/
theorem curvatureTraceAction_gaugeOneForm
    (τ : A →ₗ[R] R) (frame : ι → K.L)
    (hcyclic : ∀ a b, τ (a * b) = τ (b * a)) (Γ : OneForm K) (u : Aˣ) :
    curvatureTraceAction K τ frame (gaugeOneForm K Γ u) =
      curvatureTraceAction K τ frame Γ := by
  simp only [curvatureTraceAction, curvatureTracePairing_apply,
    connectionCurvature_gaugeOneForm,
    InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate_mul,
    InfoGeometry.Geometry.AssociativeGaugeConnection.cyclic_conjugate τ hcyclic]

/-- Exact quartic expansion of a symmetric bilinear form on a quadratic path.
Symmetry is used only after the bilinear evaluations have been formed. -/
theorem symmetricBilinear_quartic_expansion
    {V : Type*} [AddCommMonoid V] [Module R V]
    (B : LinearMap.BilinForm R V) (hB : ∀ v w, B v w = B w v)
    (F G Q : V) (t : R) :
    B (F + t • G + t ^ 2 • Q) (F + t • G + t ^ 2 • Q) =
      B F F + 2 * t * B F G +
        t ^ 2 * (B G G + 2 * B F Q) +
        2 * t ^ 3 * B G Q + t ^ 4 * B Q Q := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  rw [hB G F, hB Q F, hB Q G]
  noncomm_ring

/-- The complete action polynomial retains the quadratic curvature term and
all quartic contributions. -/
theorem curvatureTraceAction_add_smul
    (τ : A →ₗ[R] R) (frame : ι → K.L)
    (hcyclic : ∀ a b, τ (a * b) = τ (b * a))
    (Γ α : OneForm K) (t : R) :
    let B := curvatureTracePairing K τ frame
    let F := connectionCurvature K Γ
    let G := covariantExteriorDerivativeOne K Γ α
    let Q := connectionWedgeSquare K α
    curvatureTraceAction K τ frame (Γ + t • α) =
      curvatureTraceAction K τ frame Γ + 2 * t * B F G +
        t ^ 2 * (B G G + 2 * B F Q) +
        2 * t ^ 3 * B G Q + t ^ 4 * B Q Q := by
  dsimp only
  unfold curvatureTraceAction
  rw [connectionCurvature_add_smul]
  exact symmetricBilinear_quartic_expansion (R := R) (V := TwoForm K)
    (curvatureTracePairing K τ frame)
    (curvatureTracePairing_comm K τ frame hcyclic) _ _ _ t

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
