import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge
import InfoGeometry.Canonical.BRSTGaugeEquivalentStatesSameClassBridge
import InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge
import InfoGeometry.Canonical.GhostNumberGradedBRSTCohomologyBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.GradedBRSTOperatorSequenceBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge
open InfoGeometry.Canonical.GhostNumberGradedBRSTCohomologyBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Graded BRST Linear Map Q_g : E_g →ₗ[R] E_{g+1} between Ghost Eigenspace Submodules. -/
def gradedBRSTMap
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g_num : R) :
    ghostEigenspace g_op g_num →ₗ[R] ghostEigenspace g_op (g_num + 1) where
  toFun x := ⟨q x.1, by
    have h_mem : q x.1 ∈ Submodule.map q (ghostEigenspace g_op g_num) := Submodule.mem_map_of_mem x.2
    exact q_maps_ghostEigenspace_succ q g_op h_comm g_num h_mem⟩
  map_add' x y := by ext; exact LinearMap.map_add q x.1 y.1
  map_smul' c x := by ext; exact LinearMap.map_smul q c x.1

/-- **Theorem**: Graded BRST Operator Nilpotency Q_{g+1} ∘ Q_g = 0 under Q² = 0. -/
theorem gradedBRSTMap_comp_eq_zero
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g_num : R) :
    (gradedBRSTMap q g_op h_comm (g_num + 1)).comp (gradedBRSTMap q g_op h_comm g_num) = 0 := by
  ext x
  dsimp [gradedBRSTMap]
  exact LinearMap.congr_fun hq2 x.1


end InfoGeometry.Canonical.GradedBRSTOperatorSequenceBridge
