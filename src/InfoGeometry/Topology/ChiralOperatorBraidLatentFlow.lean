import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThreeColorOperatorBraidSigmaTransport
import InfoGeometry.Topology.ChiralOperatorSageLatentChart

/-!
# Cyclic colour action on the operator-valued latent chart

This is the topological/action layer for the existing cyclic colour transport.
It does not identify the cyclic action with Zorn multiplication and does not
assert a Yang--Baxter law.  It only transports the verified order-three colour
permutation to the finite product carrier and its operator-valued observations.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra
open InfoGeometry.Canonical

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

def chiralOperatorCycle
    (X : OperatorSageTopologicalCarrier A) :
    OperatorSageTopologicalCarrier A :=
  (X.1, X.2.1, operatorCycleVec X.2.2.1, operatorCycleVec X.2.2.2)

@[simp] theorem chiralOperatorCycle_apply
    (X : OperatorSageTopologicalCarrier A) :
    chiralOperatorCycle X =
      (X.1, X.2.1, operatorCycleVec X.2.2.1, operatorCycleVec X.2.2.2) := rfl

theorem continuous_chiralOperatorCycle :
    Continuous (chiralOperatorCycle (A := A)) := by
  change Continuous (fun X : OperatorSageTopologicalCarrier A =>
    (X.1, X.2.1,
      (fun i => X.2.2.1 (operatorCycle.symm i)),
      (fun i => X.2.2.2 (operatorCycle.symm i))))
  refine continuous_fst.prodMk ?_
  refine (continuous_fst.comp continuous_snd).prodMk ?_
  refine (continuous_pi ?_).prodMk (continuous_pi ?_)
  · intro i
    exact (continuous_apply (operatorCycle.symm i)).comp
      continuous_operatorSage_sigmaPlus
  · intro i
    exact (continuous_apply (operatorCycle.symm i)).comp
      continuous_operatorSage_sigmaMinus

@[simp] theorem chiralOperatorCycle_three
    (X : OperatorSageTopologicalCarrier A) :
    chiralOperatorCycle (chiralOperatorCycle (chiralOperatorCycle X)) = X := by
  rcases X with ⟨nPlus, nMinus, sigmaPlus, sigmaMinus⟩
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

def operatorSageFeatureCycle : Fin 8 ≃ Fin 8 where
  toFun
    | 0 => 0
    | 1 => 3
    | 2 => 1
    | 3 => 2
    | 4 => 4
    | 5 => 7
    | 6 => 5
    | 7 => 6
  invFun
    | 0 => 0
    | 1 => 2
    | 2 => 3
    | 3 => 1
    | 4 => 4
    | 5 => 6
    | 6 => 7
    | 7 => 5
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem operatorSageObservation_cycle_intertwines
    (X : OperatorSageTopologicalCarrier A) (i : Fin 8) :
    operatorSageObservationMap (chiralOperatorCycle X) i =
      operatorSageObservationMap X (operatorSageFeatureCycle i) := by
  fin_cases i <;> rfl

theorem operatorSageObservation_cycle_intertwines_map
    (X : OperatorSageTopologicalCarrier A) :
    operatorSageObservationMap (chiralOperatorCycle X) =
      fun i => operatorSageObservationMap X (operatorSageFeatureCycle i) := by
  funext i
  exact operatorSageObservation_cycle_intertwines X i

end
end InfoGeometry.Topology
