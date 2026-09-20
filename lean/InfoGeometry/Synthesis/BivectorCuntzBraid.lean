import InfoGeometry.Canonical.SplitOctonionRightRegularBraid
import InfoGeometry.Lie.SplitOctonionRegularActionIntertwiner
import InfoGeometry.Topology.CantorBoundaryRealClockShift

noncomputable section

namespace InfoGeometry.Synthesis.BivectorCuntzBraid

open InfoGeometry.Canonical (RealSplitOctonionAut SplitOctonionAutCandidate)
open InfoGeometry.Lie.SplitOctonionRegularActionIntertwiner
  (CZ EndCZ conjugateEnd automorphism_conjugates_leftRegular
    automorphism_conjugates_rightRegular)
open InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading (leftRegular)
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge (rightRegular)
open InfoGeometry.Canonical.SplitOctonionRightRegularBraid
  (majorana bivector bivector_sq braidUnit braidUnit_artin)
open InfoGeometry.Lie.SplitOctonionEllPolarization (rootPlus rootMinus)

theorem conjugateEnd_eq_self_of_commute
    (automorphism : RealSplitOctonionAut) (phase : EndCZ)
    (commutes : Commute (automorphism : SplitOctonionAutCandidate ℝ).toLinearMap phase) :
    conjugateEnd automorphism phase = phase := by
  apply LinearMap.ext
  intro state
  change (automorphism : SplitOctonionAutCandidate ℝ)
    (phase ((automorphism : SplitOctonionAutCandidate ℝ).symm state)) = phase state
  have evaluation := congrArg
    (fun operator : EndCZ => operator ((automorphism : SplitOctonionAutCandidate ℝ).symm state))
    commutes.eq
  change
    (automorphism : SplitOctonionAutCandidate ℝ)
        (phase ((automorphism : SplitOctonionAutCandidate ℝ).symm state)) =
      phase ((automorphism : SplitOctonionAutCandidate ℝ)
        ((automorphism : SplitOctonionAutCandidate ℝ).symm state)) at evaluation
  simpa only [LinearEquiv.apply_symm_apply] using evaluation

theorem phase_leftRegular_covariance
    (automorphism : RealSplitOctonionAut) (phase : EndCZ) (label : CZ)
    (commutes : Commute (automorphism : SplitOctonionAutCandidate ℝ).toLinearMap phase) :
    conjugateEnd automorphism (1 + phase * leftRegular label) =
      1 + phase * leftRegular ((automorphism : SplitOctonionAutCandidate ℝ) label) := by
  change (automorphism : SplitOctonionAutCandidate ℝ).conjAlgEquiv ℝ
    (1 + phase * leftRegular label) = _
  rw [map_add, map_one, map_mul]
  change 1 + conjugateEnd automorphism phase *
    conjugateEnd automorphism (leftRegular label) = _
  rw [conjugateEnd_eq_self_of_commute automorphism phase commutes,
    automorphism_conjugates_leftRegular]

theorem majorana_covariance (automorphism : RealSplitOctonionAut) (mode : Fin 3) :
    conjugateEnd automorphism (majorana mode) =
      rightRegular ((automorphism : SplitOctonionAutCandidate ℝ) (rootPlus mode)) +
        rightRegular ((automorphism : SplitOctonionAutCandidate ℝ) (rootMinus mode)) := by
  change (automorphism : SplitOctonionAutCandidate ℝ).conjAlgEquiv ℝ
    (rightRegular (rootPlus mode) + rightRegular (rootMinus mode)) = _
  rw [map_add]
  change conjugateEnd automorphism (rightRegular (rootPlus mode)) +
    conjugateEnd automorphism (rightRegular (rootMinus mode)) = _
  rw [automorphism_conjugates_rightRegular, automorphism_conjugates_rightRegular]

theorem bivector_covariance (automorphism : RealSplitOctonionAut) (index : Fin 2) :
    conjugateEnd automorphism (bivector index) =
      (rightRegular ((automorphism : SplitOctonionAutCandidate ℝ) (rootPlus index.castSucc)) +
        rightRegular ((automorphism : SplitOctonionAutCandidate ℝ) (rootMinus index.castSucc))) *
      (rightRegular ((automorphism : SplitOctonionAutCandidate ℝ) (rootPlus index.succ)) +
        rightRegular ((automorphism : SplitOctonionAutCandidate ℝ) (rootMinus index.succ))) := by
  change (automorphism : SplitOctonionAutCandidate ℝ).conjAlgEquiv ℝ
    (majorana index.castSucc * majorana index.succ) = _
  rw [map_mul]
  change conjugateEnd automorphism (majorana index.castSucc) *
    conjugateEnd automorphism (majorana index.succ) = _
  rw [majorana_covariance, majorana_covariance]

theorem transported_bivector_sq (automorphism : RealSplitOctonionAut) (index : Fin 2) :
    conjugateEnd automorphism (bivector index) *
        conjugateEnd automorphism (bivector index) = -1 := by
  simpa only [map_mul, map_neg, map_one] using
    congrArg ((automorphism : SplitOctonionAutCandidate ℝ).conjAlgEquiv ℝ) (bivector_sq index)

theorem braidUnit_covariance (automorphism : RealSplitOctonionAut) (index : Fin 2) :
    conjugateEnd automorphism (braidUnit index : EndCZ) =
      1 + conjugateEnd automorphism (majorana index.castSucc) *
        conjugateEnd automorphism (majorana index.succ) := by
  change (automorphism : SplitOctonionAutCandidate ℝ).conjAlgEquiv ℝ
    (1 + majorana index.castSucc * majorana index.succ) = _
  rw [map_add, map_one, map_mul]

theorem transported_artin (automorphism : RealSplitOctonionAut) :
    conjugateEnd automorphism (braidUnit 0 : EndCZ) *
        conjugateEnd automorphism (braidUnit 1 : EndCZ) *
        conjugateEnd automorphism (braidUnit 0 : EndCZ) =
      conjugateEnd automorphism (braidUnit 1 : EndCZ) *
        conjugateEnd automorphism (braidUnit 0 : EndCZ) *
        conjugateEnd automorphism (braidUnit 1 : EndCZ) := by
  simpa only [Units.val_mul, map_mul] using
    congrArg (fun unit : EndCZˣ =>
      (automorphism : SplitOctonionAutCandidate ℝ).conjAlgEquiv ℝ (unit : EndCZ))
      braidUnit_artin

end InfoGeometry.Synthesis.BivectorCuntzBraid
