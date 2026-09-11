import InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ActualXiHardyZRealizationBridge

/-!
# Actual centered `riemannXi` Hardy-Z factorization bridge

This owner transports the existing explicit factorization hypothesis to the
topology-side `ConcreteHardyZDatum`.  The factorization remains an input: no
independent construction of the classical Hardy `Z` function or of the
Riemann--Siegel phase is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualXiHardyZFactorizationBridge

open InfoGeometry.Canonical.ActualXiSymmetryDatumBridge
open InfoGeometry.Canonical.ConcreteHardyZNormalizationBridge
open InfoGeometry.Topology.ActualXiHardyZRealization
open InfoGeometry.Topology.XiHardyZNormalizationBridge

/-! ## The actual candidate readout -/

/-!
The preceding normalization owner constructs `candidateHardyZ` directly from
Mathlib's completed `riemannXi`.  This constructor exposes that same object
through the topology-side interface.  Its name remains explicit: it is an
actual normalized candidate, not an identification with the classical Hardy
`Z` function.
-/

def actualCandidateConcreteHardyZDatum : ConcreteHardyZDatum where
  Z := candidateHardyZ
  r := hardyNormalizationFactor
  r_ne_zero := hardyNormalizationFactor_ne_zero
  Xi_eval := fun t => centeredRiemannXi 0 t
  Xi_eq_r_mul_Z := by
    intro t
    calc
      centeredRiemannXi 0 t = (actualXiCriticalReadout t : ℂ) :=
        actualXiSymmetryDatum_criticalLine_real
          actualXiSchwarzHypothesis_concrete t
      _ = ((hardyNormalizationFactor t * candidateHardyZ t : ℝ) : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ))
          (actualXiCriticalReadout_eq_factor_mul_candidateHardyZ t)
      _ = (hardyNormalizationFactor t : ℂ) *
          (candidateHardyZ t : ℂ) := by
        push_cast
        rfl

theorem actualCandidateConcreteHardyZDatum_zero_iff (t : ℝ) :
    actualCandidateConcreteHardyZDatum.Xi_eval t = 0 ↔
      actualCandidateConcreteHardyZDatum.Z t = 0 := by
  exact hardy_z_zero_equivalence actualCandidateConcreteHardyZDatum t

theorem actualCandidateConcreteHardyZDatum_Z_even (t : ℝ) :
    actualCandidateConcreteHardyZDatum.Z (-t) =
      actualCandidateConcreteHardyZDatum.Z t := by
  exact candidateHardyZ_neg t

def actualConcreteHardyZDatum
    (hSchwarz : ActualXiSchwarzHypothesis)
    (H : HardyZFactorizationHypothesis) : ConcreteHardyZDatum where
  Z := H.Z
  r := H.r
  r_ne_zero := H.r_ne_zero
  Xi_eval := fun t => centeredRiemannXi 0 t
  Xi_eq_r_mul_Z := by
    intro t
    calc
      centeredRiemannXi 0 t =
          (actualXiCriticalReadout t : ℂ) :=
        actualXiSymmetryDatum_criticalLine_real
          hSchwarz t
      _ = ((H.r t * H.Z t : ℝ) : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ)) (H.factorization t)
      _ = (H.r t : ℂ) * (H.Z t : ℂ) := by
        push_cast
        rfl

theorem actualConcreteHardyZDatum_zero_iff
    (hSchwarz : ActualXiSchwarzHypothesis)
    (H : HardyZFactorizationHypothesis) (t : ℝ) :
    (actualConcreteHardyZDatum hSchwarz H).Xi_eval t = 0 ↔ H.Z t = 0 := by
  exact hardy_z_zero_equivalence (actualConcreteHardyZDatum hSchwarz H) t

end InfoGeometry.Canonical.ActualXiHardyZFactorizationBridge
