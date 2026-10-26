/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearComplementaryResolvent
import InfoGeometry.Physics.NuclearEffectiveObservables
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite Hilbert realization of the exact Feshbach wave map

Restrict the algebraic wave operator to the actual model submodule `range P`.
Finite dimension supplies continuity and completeness; projection of the
reconstructed vector proves injectivity. Thus the induced normalization
theorems apply to a constructed wave embedding, not an assumed injective map.
This finite realization makes no Hilbert-space assertion about the countable
algebraic CAR--phonon carrier.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiniteEffectiveModel

open InfoGeometry.Physics.NuclearFeshbachReduction
open InfoGeometry.Physics.NuclearComplementaryResolvent
open InfoGeometry.Physics.NuclearEffectiveObservables

variable {K V : Type*} [RCLike K] [NormedAddCommGroup V] [InnerProductSpace K V]
variable [FiniteDimensional K V]

/-- The actual resolvent graph, restricted to its model domain and made
continuous by native finite-dimensional linear-map conversion. -/
def waveEmbedding (P H : Module.End K V) (hP : P * P = P)
    (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P) : LinearMap.range P →L[K] V :=
  LinearMap.toContinuousLinearMap
    ((waveOperator P H (liftInverse P hP e)).comp (LinearMap.range P).subtype)

@[simp] theorem waveEmbedding_apply (P H : Module.End K V) (hP : P * P = P)
    (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P) (v : LinearMap.range P) :
    waveEmbedding P H hP e v = waveOperator P H (liftInverse P hP e) (v : V) := rfl

theorem waveEmbedding_projection (P H : Module.End K V) (hP : P * P = P)
    (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P) (v : LinearMap.range P) :
    P (waveEmbedding P H hP e v) = (v : V) := by
  have hpv : P (v : V) = (v : V) :=
    (LinearMap.IsIdempotentElem.mem_range_iff hP).mp v.property
  have h := LinearMap.congr_fun (projection_mul_waveOperator P H _ hP
    (complement_mul_liftInverse P hP e)) (v : V)
  exact h.trans hpv

theorem waveEmbedding_injective (P H : Module.End K V) (hP : P * P = P)
    (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P) :
    Function.Injective (waveEmbedding P H hP e) := by
  intro v w h
  apply Subtype.ext
  have hp := congrArg P h
  simpa only [waveEmbedding_projection] using hp

/-- The native finite Hilbert wave map satisfies precisely the same nonlinear
spectral-parameter equation as the algebraic Feshbach reduction. -/
theorem waveEmbedding_eigen_equation_iff (P H : Module.End K V) (E : K)
    (hP : P * P = P) (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P)
    (he : e.toLinearMap = complementShift P hP H E) (v : LinearMap.range P) :
    H (waveEmbedding P H hP e v) = E • waveEmbedding P H hP e v ↔
      effectiveHamiltonian P H (liftInverse P hP e) (v : V) = E • (v : V) :=
  eigen_equation_iff_of_equiv P H E hP e he v
    ((LinearMap.IsIdempotentElem.mem_range_iff hP).mp v.property)

/-- Strict normalization positivity is derived for the constructed embedding. -/
theorem waveEmbedding_metricWeight_pos (P H : Module.End K V) (hP : P * P = P)
    (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P)
    {v : LinearMap.range P} (hv : v ≠ 0) :
    letI : CompleteSpace V := FiniteDimensional.complete K V
    letI : CompleteSpace (LinearMap.range P) := FiniteDimensional.complete K _
    0 < metricWeight (waveEmbedding P H hP e) v := by
  let : CompleteSpace V := FiniteDimensional.complete K V
  let : CompleteSpace (LinearMap.range P) := FiniteDimensional.complete K _
  exact metricWeight_pos _ (waveEmbedding_injective P H hP e) hv

/-- Every nonzero model vector has a correctly normalized reconstructed state. -/
theorem waveEmbedding_normalized_norm (P H : Module.End K V) (hP : P * P = P)
    (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P)
    {v : LinearMap.range P} (hv : v ≠ 0) :
    letI : CompleteSpace V := FiniteDimensional.complete K V
    letI : CompleteSpace (LinearMap.range P) := FiniteDimensional.complete K _
    ‖normalizedState (waveEmbedding P H hP e) v‖ = 1 := by
  let : CompleteSpace V := FiniteDimensional.complete K V
  let : CompleteSpace (LinearMap.range P) := FiniteDimensional.complete K _
  exact norm_normalizedState _ (waveEmbedding_injective P H hP e) hv

end InfoGeometry.Physics.NuclearFiniteEffectiveModel
