import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge
import InfoGeometry.Canonical.BRSTGaugeEquivalentStatesSameClassBridge
import InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.GhostNumberGradedBRSTCohomologyBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Ghost Number Eigenspace Submodule ker(G - g • id). -/
def ghostEigenspace
    (g_op : Module.End R (ExteriorAlgebra R V))
    (g_num : R) : Submodule R (ExteriorAlgebra R V) :=
  LinearMap.ker (g_op - g_num • LinearMap.id)

/-- **Theorem**: BRST Charge Maps Ghost-Number Eigenspace g to Ghost-Number Eigenspace (g + 1): Q(E_g) ⊆ E_{g+1}. -/
theorem q_maps_ghostEigenspace_succ
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g_num : R) :
    Submodule.map q (ghostEigenspace g_op g_num) ≤ ghostEigenspace g_op (g_num + 1) := by
  intro x hx
  rw [Submodule.mem_map] at hx
  rcases hx with ⟨chi, h_chi, rfl⟩
  rw [ghostEigenspace, LinearMap.mem_ker] at h_chi ⊢
  rw [LinearMap.sub_apply] at h_chi ⊢
  rw [sub_eq_zero] at h_chi
  rw [LinearMap.smul_apply, LinearMap.id_apply] at h_chi
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  rw [sub_eq_zero]
  exact ghost_number_raising q g_op h_comm g_num chi h_chi

/-- **Theorem**: Master Ghost-Number Graded BRST Submodule Synthesis.
    Unifies:
    1. Ghost number eigenspace submodule E_g = ker(G - g • id) definition.
    2. Submodule map inclusion Q(E_g) ⊆ E_{g+1}.
    3. Structural transformation of BRST physical state spaces across ghost-number sectors. -/
theorem master_ghost_number_graded_brst_synthesis
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g_num : R) :
    (ghostEigenspace g_op g_num = LinearMap.ker (g_op - g_num • LinearMap.id)) ∧
    (Submodule.map q (ghostEigenspace g_op g_num) ≤ ghostEigenspace g_op (g_num + 1)) := ⟨
  rfl,
  q_maps_ghostEigenspace_succ q g_op h_comm g_num
⟩

end InfoGeometry.Canonical.GhostNumberGradedBRSTCohomologyBridge
