import InfoGeometry.Clifford.MatToCantorOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.RealCantorOpLimit
import InfoGeometry.Clifford.Cl11TensorTowerLimit

noncomputable section

namespace InfoGeometry.Recovered.CantorCliffordLimitBridge

open InfoGeometry.Clifford
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/--
Recovered forward direct-limit bridge from the finite `Cl(1,1)` tensor-tower
limit to the real Cantor-operator limit.

Source fragment: `archive/scratch_recovery/test_limit.lean`.
The key compatibility input is
`MatToCantorOperator.cantorOpEmbed_matToCantor`, together with the generic
direct-limit bonding equation `directLimitOf_bond`.
-/
def fwdHom : Cl11TensorTowerLimit.Limit →+* RealCantorOpLimit.Limit :=
  directLimitLift Cl11TensorTowerLimit.stageBond
    (fun n => (RealCantorOpLimit.ofStage n).comp
      (MatToCantorOperator.matToCantor n).toRingHom)
    (by
      intro n x
      simp only [RingHom.comp_apply]
      have h := MatToCantorOperator.cantorOpEmbed_matToCantor n x
      change RealCantorOpLimit.ofStage (n + 1)
          (MatToCantorOperator.matToCantor (n + 1)
            (Cl11TensorTower.matStageEmbed n x)) =
        RealCantorOpLimit.ofStage n (MatToCantorOperator.matToCantor n x)
      rw [← h]
      exact directLimitOf_bond RealCantorOpLimit.stageBond n
        (MatToCantorOperator.matToCantor n x))

/--
Recovered reverse direct-limit bridge from the real Cantor-operator limit back
to the finite `Cl(1,1)` tensor-tower limit.
-/
def revHom : RealCantorOpLimit.Limit →+* Cl11TensorTowerLimit.Limit :=
  directLimitLift RealCantorOpLimit.stageBond
    (fun n => (Cl11TensorTowerLimit.ofStage n).comp
      (MatToCantorOperator.matToCantor n).symm.toRingHom)
    (by
      intro n x
      simp only [RingHom.comp_apply]
      have h1 := MatToCantorOperator.cantorOpEmbed_matToCantor n
        ((MatToCantorOperator.matToCantor n).symm x)
      simp only [AlgEquiv.apply_symm_apply] at h1
      have h2 :
          (MatToCantorOperator.matToCantor (n + 1)).symm
              (MatToCantorOperator.cantorOpEmbed n x) =
            Cl11TensorTower.matStageEmbed n
              ((MatToCantorOperator.matToCantor n).symm x) := by
        rw [h1]
        exact (MatToCantorOperator.matToCantor (n + 1)).symm_apply_apply _
      change Cl11TensorTowerLimit.ofStage (n + 1)
          ((MatToCantorOperator.matToCantor (n + 1)).symm
            (MatToCantorOperator.cantorOpEmbed n x)) =
        Cl11TensorTowerLimit.ofStage n
          ((MatToCantorOperator.matToCantor n).symm x)
      rw [h2]
      exact directLimitOf_bond Cl11TensorTowerLimit.stageBond n
        ((MatToCantorOperator.matToCantor n).symm x))

end InfoGeometry.Recovered.CantorCliffordLimitBridge
