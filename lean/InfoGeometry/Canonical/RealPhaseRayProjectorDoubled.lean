/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealPhaseRayProjector
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Phase projectors on the native doubled real carrier

The existing doubled-space clock axis and positive observer pairing instantiate
the real phase-ray construction. On the full four-dimensional real carrier,
two normalized directions with overlap `3/5` give actual noncommuting phase
projectors. Their native real trace pairing is `18/25`.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealPhaseRayProjectorDoubled

open InfoGeometry.Krein
open RealPhaseRayProjector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The existing clock axis, viewed as a real linear endomorphism. -/
abbrev phaseAxis : Module.End ℝ (DoubledSpace E) :=
  (clockAxis (E := E)).toLinearMap

theorem phaseAxis_isRealComplexStructure :
    IsRealComplexStructure (phaseAxis (E := E)) := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun T : DoubledSpace E →L[ℝ] DoubledSpace E => T x)
    (clockAxis_sq E)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply] using h

theorem observerForm_isSymm : (doubledHilbertBilin (E := E)).IsSymm := by
  constructor
  intro x y
  change inner ℝ x y = inner ℝ y x
  exact real_inner_comm y x

theorem phaseAxis_observer_skew (x y : DoubledSpace E) :
    doubledHilbertBilin (phaseAxis x) y = -doubledHilbertBilin x (phaseAxis y) := by
  change inner ℝ (clockAxis x) y = -inner ℝ x (clockAxis y)
  rw [clockAxis_apply, clockAxis_apply]
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_toLp, WithLp.ofLp_fst,
    WithLp.ofLp_snd, inner_neg_left, inner_neg_right]
  ring

/-- The phase projector keeps the native doubled carrier and positive observer form. -/
abbrev phaseProjector (u : DoubledSpace E) : Module.End ℝ (DoubledSpace E) :=
  rayProjector doubledHilbertBilin phaseAxis u

theorem phaseProjector_idempotent (u : DoubledSpace E)
    (hu : doubledHilbertBilin u u = 1) :
    IsIdempotentElem (phaseProjector u) :=
  rayProjector_idempotent doubledHilbertBilin phaseAxis observerForm_isSymm
    phaseAxis_isRealComplexStructure phaseAxis_observer_skew u hu

theorem phaseProjector_adjoint (u : DoubledSpace E) :
    LinearMap.IsAdjointPair doubledHilbertBilin doubledHilbertBilin
      (phaseProjector u) (phaseProjector u) :=
  rayProjector_adjoint doubledHilbertBilin phaseAxis observerForm_isSymm u

section Concrete

/-- The full native doubled real carrier of dimension four. -/
abbrev ProbeSpace := DoubledSpace (EuclideanSpace ℝ (Fin 2))

theorem probeSpace_finrank : Module.finrank ℝ ProbeSpace = 4 := by
  calc
    Module.finrank ℝ ProbeSpace =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
      (WithLp.linearEquiv (2 : ENNReal) ℝ _).finrank_eq
    _ = 4 := by simp [Module.finrank_prod]

def probeU : ProbeSpace :=
  to_doubled (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0

def probeV : ProbeSpace :=
  to_doubled ((3 / 5 : ℝ) • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
    (4 / 5 : ℝ) • EuclideanSpace.basisFun (Fin 2) ℝ 1) 0

theorem probeU_unit : doubledHilbertBilin probeU probeU = 1 := by
  rw [probeU, doubledHilbertBilin_to_doubled]
  simp

theorem probeV_unit : doubledHilbertBilin probeV probeV = 1 := by
  rw [probeV, doubledHilbertBilin_to_doubled]
  norm_num [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]

theorem probe_overlap : doubledHilbertBilin probeU probeV = 3 / 5 := by
  rw [probeU, probeV, doubledHilbertBilin_to_doubled]
  norm_num [inner_add_right, real_inner_smul_right]

theorem probe_phase_overlap : doubledHilbertBilin (phaseAxis probeU) probeV = 0 := by
  change doubledHilbertBilin (clockAxis probeU) probeV = 0
  rw [probeU, clockAxis_to_doubled, probeV, doubledHilbertBilin_to_doubled]
  simp

/-- Actual normalized projectors on the native real carrier do not commute. -/
theorem probe_projectors_noncommute :
    ¬ Commute (phaseProjector probeU) (phaseProjector probeV) := by
  apply rayProjectors_noncommute doubledHilbertBilin phaseAxis observerForm_isSymm
    phaseAxis_observer_skew probeU probeV probeU_unit probeV_unit probe_phase_overlap
  · rw [probe_overlap]
    norm_num
  · rw [probe_overlap]
    norm_num

theorem probe_projectors_distinct : phaseProjector probeU ≠ phaseProjector probeV := by
  intro h
  apply probe_projectors_noncommute
  simpa only [h] using Commute.refl (phaseProjector probeV)

/-- The real trace is twice the squared overlap `9/25`. -/
theorem probe_trace_overlap :
    LinearMap.trace ℝ ProbeSpace (phaseProjector probeU * phaseProjector probeV) =
      18 / 25 := by
  rw [trace_rayProjector_mul doubledHilbertBilin phaseAxis observerForm_isSymm
    phaseAxis_isRealComplexStructure phaseAxis_observer_skew probeU probeV,
    probe_overlap, probe_phase_overlap]
  norm_num

end Concrete

end InfoGeometry.Canonical.RealPhaseRayProjectorDoubled
