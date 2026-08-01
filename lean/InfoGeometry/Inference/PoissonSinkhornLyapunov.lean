/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Inference.PoissonSinkhornPotentials

/-!
# Poisson Sinkhorn Lyapunov bridge

This owner module names the existing finite Sinkhorn contraction theorem in
the Poisson transport namespace. It certifies one admissible normalization
step and does not assert convergence of a numerical implementation.
-/

open InfoGeometry.Canonical.MoE

namespace InfoGeometry.Inference

variable {n : Nat} [Nonempty (Fin n)]

/-- An admissible row or column normalization step for a Poisson coupling. -/
def poissonSinkhornStep
    (phase : SinkhornPhase)
    (M M' : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  SinkhornStep n phase M M'

omit [Nonempty (Fin n)] in
theorem poissonSinkhornStep_lyapunov_nonincrease
    {phase : SinkhornPhase} {M M' : Matrix (Fin n) (Fin n) ℝ}
    (hstep : poissonSinkhornStep phase M M') :
    phaseLyapunovAfter n phase M' ≤ phaseLyapunovBefore n phase M := by
  exact sinkhornStep_phaseLyapunov_monotone (n := n) hstep

omit [Nonempty (Fin n)] in
theorem poissonSinkhornStep_rnBarrier_nonincrease
    {phase : SinkhornPhase} {M M' : Matrix (Fin n) (Fin n) ℝ}
    (hstep : poissonSinkhornStep phase M M') :
    phaseRNBarrierAfter n phase M' ≤ phaseRNBarrierBefore n phase M := by
  exact sinkhornStep_phaseRNBarrier_monotone (n := n) hstep

end InfoGeometry.Inference
