/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.QuantumContext.MarkovGroupInversePetzSupport

/-!
# Stationary projector identities from the Markov group inverse

For `L = 1 - P` and a group inverse `G`, the complementary idempotent
`Q = 1 - L * G` is annihilated by `L` on both sides. Consequently `Q * P = Q`
and `P * Q = Q`. These are matrix-level left- and right-stationarity
identities. They do not assert positivity, normalization, uniqueness of a
stationary probability vector, or convergence of powers of `P`.
-/

namespace InfoGeometry.QuantumContext

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complementary group-inverse projection associated with the stationary
kernel of `1 - P`. -/
def markovStationaryProjector (P G : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  1 - markovRangeIdempotent P G

/-- The stationary projector is annihilated by the Markov Laplacian on the
right. -/
theorem markovStationaryProjector_mul_laplacian_eq_zero
    (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    markovStationaryProjector P G * (1 - P) = 0 := by
  change (1 - ((1 - P) * G)) * (1 - P) = 0
  calc
    (1 - ((1 - P) * G)) * (1 - P) =
        (1 - P) - ((1 - P) * G * (1 - P)) := by noncomm_ring
    _ = (1 - P) - (1 - P) := by rw [hG.1]
    _ = 0 := sub_self _

/-- The Markov Laplacian annihilates the stationary projector on the left. -/
theorem laplacian_mul_markovStationaryProjector_eq_zero
    (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    (1 - P) * markovStationaryProjector P G = 0 := by
  change (1 - P) * (1 - ((1 - P) * G)) = 0
  calc
    (1 - P) * (1 - ((1 - P) * G)) =
        (1 - P) - ((1 - P) * (1 - P) * G) := by noncomm_ring
    _ = (1 - P) - ((1 - P) * G * (1 - P)) := by
      congr 1
      calc
        (1 - P) * (1 - P) * G = (1 - P) * ((1 - P) * G) := by rw [mul_assoc]
        _ = (1 - P) * (G * (1 - P)) := by rw [hG.2.2]
        _ = (1 - P) * G * (1 - P) := by rw [mul_assoc]
    _ = 0 := by rw [hG.1]; exact sub_self _

/-- The rows of the complementary projection are stationary row vectors:
`Q * P = Q`. -/
theorem markovStationaryProjector_mul_transition_eq_self
    (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    markovStationaryProjector P G * P = markovStationaryProjector P G := by
  have hzero := markovStationaryProjector_mul_laplacian_eq_zero P G hG
  change markovStationaryProjector P G * (1 - P) = 0 at hzero
  calc
    markovStationaryProjector P G * P =
        markovStationaryProjector P G -
          markovStationaryProjector P G * (1 - P) := by noncomm_ring
    _ = markovStationaryProjector P G := by rw [hzero]; noncomm_ring

/-- The columns of the complementary projection are right fixed observables:
`P * Q = Q`. -/
theorem transition_mul_markovStationaryProjector_eq_self
    (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    P * markovStationaryProjector P G = markovStationaryProjector P G := by
  have hzero := laplacian_mul_markovStationaryProjector_eq_zero P G hG
  change (1 - P) * markovStationaryProjector P G = 0 at hzero
  calc
    P * markovStationaryProjector P G =
        markovStationaryProjector P G -
          (1 - P) * markovStationaryProjector P G := by noncomm_ring
    _ = markovStationaryProjector P G := by rw [hzero]; noncomm_ring

/-- On the full matrix carrier, left multiplication by the complementary
group-inverse projection has range exactly the kernel of left multiplication
by the Markov Laplacian. -/
theorem markovStationaryProjector_leftRange_eq_laplacian_leftKernel
    (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    (mulLeftLinearMap ι ℝ (markovStationaryProjector P G)).range =
      (mulLeftLinearMap ι ℝ (1 - P)).ker := by
  let A : Module.End ℝ (Matrix ι ι ℝ) := mulLeftLinearMap ι ℝ (1 - P)
  let D : Module.End ℝ (Matrix ι ι ℝ) := mulLeftLinearMap ι ℝ G
  have hLift : IsGroupInverse A D := by
    simpa [A, D] using mulLeftLinearMap_groupInverse (1 - P) G hG
  have hComplement :=
    InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_range_eq_drazinCore
      hLift.toDrazin
  have hRange : LinearMap.range (1 - A * D) = A.ker := by
    simpa [InfoGeometry.Canonical.Drazin.IsDrazinInverse.drazinCore,
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection,
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection] using hComplement
  have hMap :
      mulLeftLinearMap ι ℝ (markovStationaryProjector P G) = 1 - A * D := by
    apply LinearMap.ext
    intro X
    change (1 - ((1 - P) * G)) * X = X - (1 - P) * (G * X)
    noncomm_ring
  rw [hMap, hRange]

end InfoGeometry.QuantumContext
