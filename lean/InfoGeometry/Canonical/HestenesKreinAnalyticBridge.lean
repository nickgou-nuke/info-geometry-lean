import InfoGeometry.Canonical.HestenesKreinColimitRealBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PositiveHomogeneousBarrier

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinAnalyticBridge

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesKreinColimitRealBoundary
open InfoGeometry.Canonical.PositiveHomogeneousBarrier
open InfoGeometry.Krein

theorem determinant_stage_eq_target
    {C : HestenesKreinCone}
    (stage : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limit : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, stage n x = limit (C.ι n x))
    (coordinate : DoubledSpace C.LimitBase → ℝ)
    (target : ℝ → ℝ)
    (hcal : ∀ x, limit x = target (coordinate x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stage n x = target (coordinate (C.ι n x)) := by
  rw [hreadout n x, hcal]

theorem determinant_stage_bond
    {C : HestenesKreinCone}
    (stage : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limit : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, stage n x = limit (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stage (n + 1) (C.bond n x) = stage n x := by
  rw [hreadout (n + 1), hreadout n, C.ι_bond_apply]

theorem determinant_stage_bondIterate
    {C : HestenesKreinCone}
    (stage : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limit : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, stage n x = limit (C.ι n x))
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stage (n + m) (C.toFilteredPhaseCone.bondIterate n m x) = stage n x := by
  rw [hreadout (n + m), hreadout n]
  exact congrArg limit (C.toFilteredPhaseCone.ι_bondIterate_apply n m x)

def criticalThroat (x : PositiveHomogeneousCone) : Prop :=
  homogeneousSwap x = x

theorem criticalThroat_iff_equal_lanes (x : PositiveHomogeneousCone) :
    criticalThroat x ↔ x.1.1 = x.1.2 := by
  constructor
  · intro h
    have hcoord := congrArg (fun y : PositiveHomogeneousCone => y.1.1) h
    simpa [homogeneousSwap] using hcoord.symm
  · intro h
    apply Subtype.ext
    ext <;> simp [homogeneousSwap, h]

theorem criticalThroat_swap_invariant (x : PositiveHomogeneousCone) :
    criticalThroat (homogeneousSwap x) ↔ criticalThroat x := by
  rw [criticalThroat, criticalThroat]
  constructor <;> intro h
  · simpa [homogeneousSwap_involutive] using congrArg homogeneousSwap h
  · simpa [homogeneousSwap_involutive] using congrArg homogeneousSwap h

theorem criticalThroat_barrier_readout (x : PositiveHomogeneousCone) :
    barrier (homogeneousSwap x) = barrier x :=
  barrier_homogeneousSwap_invariant x

theorem lower_stage_bondIterate
    {C : HestenesKreinCone} (R : RealBoundaryReadout C)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    R.lowerStage (n + m) (C.toFilteredPhaseCone.bondIterate n m x) =
      R.lowerStage n x :=
  R.lower_bondIterate n m x

theorem upper_stage_bondIterate
    {C : HestenesKreinCone} (R : RealBoundaryReadout C)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    R.upperStage (n + m) (C.toFilteredPhaseCone.bondIterate n m x) =
      R.upperStage n x :=
  R.upper_bondIterate n m x

end InfoGeometry.Canonical.HestenesKreinAnalyticBridge
