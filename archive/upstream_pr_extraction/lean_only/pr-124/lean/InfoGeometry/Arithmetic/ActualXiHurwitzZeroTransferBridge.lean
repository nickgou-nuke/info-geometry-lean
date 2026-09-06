import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Canonical.PrimeCliffordWaveletActualXiBridge
import InfoGeometry.Canonical.HurwitzAsanoColimitLimitBridge

/-!
# Hurwitz zero transfer into the entire completed xi representative

This is a thin consumer of the generic moving-zero theorem.  It does not
assert that a particular finite prime partition system converges to `ξ`; that
analytic realization remains an explicit hypothesis of the datum below.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ActualXiHurwitzZeroTransfer

open Filter Set Topology
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.PrimeCliffordWaveletActualXiBridge
open InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit
open InfoGeometry.Canonical.HurwitzAsano

/-- Finite approximants with a moving zero converging to a zero of entire `ξ`.

  The radius, continuity at the target, and local-uniform convergence are
  deliberately fields: this consumer packages the exact analytic arrow still
  needed from a concrete finite/colimit construction.
-/
structure EntireXiMovingZeroData where
  approximant : ℕ → ℂ → ℂ
  zeroSeq : ℕ → ℂ
  boundary : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  locally_uniform :
    TendstoUniformlyOn approximant entireRiemannXi atTop
      (Metric.closedBall boundary radius)
  zero_at_stage : ∀ n, approximant n (zeroSeq n) = 0
  zeroSeq_tendsto : Tendsto zeroSeq atTop (𝓝 boundary)

/-- A moving sequence of zeros of finite approximants is a zero of entire `ξ`.

This theorem is unconditional once the displayed uniform-limit data are
provided; in particular, it does not identify the approximants with prime
Euler products and it is not a proof of the Hurwitz theorem.
-/
theorem entireRiemannXi_eq_zero_of_moving_zero
    (D : EntireXiMovingZeroData) :
    entireRiemannXi D.boundary = 0 := by
  let data : MovingZeroUniformLimitData :=
    { approximant := D.approximant
      limit := entireRiemannXi
      zeroSeq := D.zeroSeq
      boundary := D.boundary
      radius := D.radius
      radius_pos := D.radius_pos
      limit_continuousAt := differentiable_entireRiemannXi.continuous.continuousAt
      locally_uniform := D.locally_uniform
      zero_at_stage := D.zero_at_stage
      zeroSeq_tendsto := D.zeroSeq_tendsto }
  exact continuous_limit_eq_zero_of_moving_zero data

/-- The existing prime-wavelet readout is the entire representative away from
the two removable-singularity coordinates.  This is a readback theorem only;
the realization's convergence field remains an explicit hypothesis. -/
theorem waveletLimit_eq_entireRiemannXi_on_regular_locus
    (W : InfoGeometry.Analysis.CliffordWaveletTransform.CliffordWaveletModel)
    (A : PrimeLeeYangApproximants)
    (R : PrimeCliffordWaveletRealization W A actualCompletedXiFunction)
    (z : ℂ)
    (hz0 : cayleyInv z ≠ 0)
    (hz1 : cayleyInv z ≠ 1) :
    R.waveletLimit z = entireRiemannXi (cayleyInv z) := by
  rw [wavelet_reconstruction_eq_actual_riemannXi W A R z]
  exact entireRiemannXi_eq_riemannXi_on_regular_locus hz0 hz1

end InfoGeometry.Arithmetic.ActualXiHurwitzZeroTransfer
