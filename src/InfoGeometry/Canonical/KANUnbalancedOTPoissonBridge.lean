import InfoGeometry.Canonical.ArnoldMajoranaNetwork
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.RegularizedPoissonDeviance
import InfoGeometry.Inference.PoissonUnbalancedSinkhornTopological
import InfoGeometry.Inference.PoissonUnbalancedSinkhornCouplingTopological
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Finite KAN/UOT/Poisson readout bridge

This module records only finite scalar readouts.  `uotMassBalance` is the
algebraic source/sink balance; it is not a continuum continuity equation.
The Poisson loss is the existing inference-layer deviance, so its positivity
and boundary conventions are inherited rather than duplicated.
-/

namespace InfoGeometry.Canonical

def kanEdgeMorphism (phi : ℝ → ℝ) (x : ℝ) : ℝ :=
  phi x

noncomputable def kanEdgeContinuousMap
    (phi : ℝ → ℝ) (hphi : Continuous phi) : C(ℝ, ℝ) :=
  ContinuousMap.mk phi hphi

@[simp] theorem kanEdgeContinuousMap_apply
    (phi : ℝ → ℝ) (hphi : Continuous phi) (x : ℝ) :
    kanEdgeContinuousMap phi hphi x = phi x :=
  rfl

def uotMassBalance (mIn mCreated mDestroyed : ℝ) : ℝ :=
  mIn + mCreated - mDestroyed

noncomputable def uotMassBalanceContinuousMap
    (mCreated mDestroyed : ℝ) : C(ℝ, ℝ) :=
  ContinuousMap.mk
    (fun mIn => uotMassBalance mIn mCreated mDestroyed)
    ((continuous_id.add continuous_const).sub continuous_const)

@[simp] theorem uotMassBalanceContinuousMap_apply
    (mCreated mDestroyed mIn : ℝ) :
    uotMassBalanceContinuousMap mCreated mDestroyed mIn =
      uotMassBalance mIn mCreated mDestroyed :=
  rfl

noncomputable def uotMassBalanceJointContinuousMap :
    C(((ℝ × ℝ) × ℝ), ℝ) :=
  ContinuousMap.mk
    (fun p => uotMassBalance p.1.1 p.1.2 p.2)
    (by
      unfold uotMassBalance
      fun_prop)

@[simp] theorem uotMassBalanceJointContinuousMap_apply
    (p : (ℝ × ℝ) × ℝ) :
    uotMassBalanceJointContinuousMap p =
      uotMassBalance p.1.1 p.1.2 p.2 :=
  rfl

theorem uot_reduces_to_classical_ot (mIn : ℝ) :
    uotMassBalance mIn 0 0 = mIn := by
  simp [uotMassBalance]

noncomputable def kanPoissonLoss (observed mean : ℝ) : ℝ :=
  InfoGeometry.Inference.poissonDeviance observed mean

theorem kanPoissonLoss_nonneg
    {observed mean : ℝ} (hObserved : 0 ≤ observed) (hMean : 0 < mean) :
    0 ≤ kanPoissonLoss observed mean := by
  exact InfoGeometry.Inference.poissonDeviance_nonneg hObserved hMean

theorem kanPoissonLoss_self_zero (mean : ℝ) (hMean : 0 < mean) :
    kanPoissonLoss mean mean = 0 := by
  unfold kanPoissonLoss InfoGeometry.Inference.poissonDeviance
  unfold InfoGeometry.Inference.poissonBregman
  rw [if_neg hMean.ne', div_self hMean.ne', Real.log_one]
  ring

noncomputable def kanPoissonLossContinuousMap
    (observed : ℝ) (hObserved : 0 < observed) :
    C({mean : ℝ // 0 < mean}, ℝ) :=
  ContinuousMap.mk
    (fun mean => kanPoissonLoss observed mean.1)
    (by
      unfold kanPoissonLoss InfoGeometry.Inference.poissonDeviance
      simp only [InfoGeometry.Inference.poissonBregman, if_neg hObserved.ne']
      fun_prop (disch := aesop))

@[simp] theorem kanPoissonLossContinuousMap_apply
    (observed : ℝ) (hObserved : 0 < observed)
    (mean : {mean : ℝ // 0 < mean}) :
    kanPoissonLossContinuousMap observed hObserved mean =
      kanPoissonLoss observed mean.1 :=
  rfl

theorem master_kan_uot_poisson_synthesis
    (phi : ℝ → ℝ) (x mIn mean : ℝ) (hMean : 0 < mean) :
    (kanEdgeMorphism phi x = phi x) ∧
    (uotMassBalance mIn 0 0 = mIn) ∧
    (kanPoissonLoss mean mean = 0) := by
  exact ⟨rfl, uot_reduces_to_classical_ot mIn,
    kanPoissonLoss_self_zero mean hMean⟩

end InfoGeometry.Canonical
