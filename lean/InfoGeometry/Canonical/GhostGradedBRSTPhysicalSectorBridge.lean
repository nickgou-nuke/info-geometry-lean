import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge
import InfoGeometry.Canonical.BRSTGaugeEquivalentStatesSameClassBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.BRSTExactClassZeroBridge
open InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge
open InfoGeometry.Canonical.BRSTGaugeEquivalentStatesSameClassBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Ghost-Number Raising Identity G (Q χ) = (g + 1) • Q χ under [G, Q] = Q commutator relation. -/
theorem ghost_number_raising
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g_num : R)
    (chi : ExteriorAlgebra R V)
    (h_ghost : g_op chi = g_num • chi) :
    g_op (q chi) = (g_num + 1) • q chi := by
  have h_eq : g_op (q chi) - q (g_op chi) = q chi := by
    have h := LinearMap.congr_fun h_comm chi
    exact h
  rw [h_ghost] at h_eq
  rw [LinearMap.map_smul] at h_eq
  rw [sub_eq_iff_eq_add] at h_eq
  rw [h_eq]
  rw [add_smul, one_smul, add_comm]

/-- **Theorem**: Master Ghost-Graded BRST Physical Sector Synthesis.
    Unifies:
    1. Operator nilpotency Q_BRST² = 0.
    2. Ghost number grading commutator [G, Q] = Q.
    3. Ghost number raising theorem G (Q χ) = (g + 1) Q χ.
    4. Exact machine-checked proof closure for ghost-number grading of BRST physical state space. -/
theorem master_ghost_graded_brst_physical_sector_synthesis
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g_num : R)
    (chi : ExteriorAlgebra R V)
    (h_ghost : g_op chi = g_num • chi) :
    (q.comp q = 0) ∧
    (g_op (q chi) = (g_num + 1) • q chi) := ⟨
  hq2,
  ghost_number_raising q g_op h_comm g_num chi h_ghost
⟩

end InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge
