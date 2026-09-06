import InfoGeometry.Algebra.ChiralDoubledRealBlock
import InfoGeometry.Clifford.CliffordBott

/-!
# Real doubled carrier into the split-Clifford Bott colimit

This is a transport bridge only.  It does not identify a Nambu--Gorkov block
with a Clifford module automatically: the stage map is supplied explicitly.
What is proved is that every such `Cl(5,5)` readout has a canonical direct-limit
lift and that finite tails, including the 8-step Bott subsequence, preserve
the represented element.
-/

noncomputable section

namespace InfoGeometry.Topology

open InfoGeometry.Algebra
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.CliffordBott

def splitCliffordStageFiveLift :
    SplitClNNAlg 5 →ₗ[ℝ] ClInfty where
  toFun := ofStage 5
  map_add' x y := ofStage_add 5 x y
  map_smul' c x := ofStage_smul 5 c x

def chiralCliffordBottLift
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (stageReadout : DoubledRealCarrier H →ₗ[ℝ] SplitClNNAlg 5) :
    DoubledRealCarrier H →ₗ[ℝ] ClInfty :=
  splitCliffordStageFiveLift.comp stageReadout

@[simp] theorem chiralCliffordBottLift_apply
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (stageReadout : DoubledRealCarrier H →ₗ[ℝ] SplitClNNAlg 5)
    (x : DoubledRealCarrier H) :
    chiralCliffordBottLift stageReadout x = ofStage 5 (stageReadout x) :=
  rfl

theorem chiralCliffordBottLift_tail
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (stageReadout : DoubledRealCarrier H →ₗ[ℝ] SplitClNNAlg 5)
    (x : DoubledRealCarrier H) (k : ℕ) :
    ofStage (5 + k)
        (splitCliffordMap 5 (5 + k) (Nat.le_add_right 5 k)
          (stageReadout x)) =
      chiralCliffordBottLift stageReadout x := by
  rw [ofStage_map]
  rfl

theorem chiralCliffordBottLift_bott_tail
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (stageReadout : DoubledRealCarrier H →ₗ[ℝ] SplitClNNAlg 5)
    (x : DoubledRealCarrier H) (k : ℕ) :
    ofStage (5 + 8 * k)
        (splitCliffordMap 5 (5 + 8 * k) (Nat.le_add_right 5 (8 * k))
          (stageReadout x)) =
      chiralCliffordBottLift stageReadout x := by
  rw [ofStage_map]
  rfl

theorem chiralCliffordBottLift_eq_ofStage
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (stageReadout : DoubledRealCarrier H →ₗ[ℝ] SplitClNNAlg 5)
    (x : DoubledRealCarrier H) :
    chiralCliffordBottLift stageReadout x =
      ofStage 5 (stageReadout x) :=
  rfl

end InfoGeometry.Topology
