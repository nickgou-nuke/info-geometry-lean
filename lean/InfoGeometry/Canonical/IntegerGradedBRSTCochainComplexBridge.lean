import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge
import InfoGeometry.Canonical.GhostNumberGradedBRSTCohomologyBridge
import InfoGeometry.Canonical.GradedBRSTOperatorSequenceBridge
import InfoGeometry.Canonical.GradedBRSTCochainComplexBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.IntegerGradedBRSTCochainComplexBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge
open InfoGeometry.Canonical.GhostNumberGradedBRSTCohomologyBridge
open InfoGeometry.Canonical.GradedBRSTOperatorSequenceBridge
open InfoGeometry.Canonical.GradedBRSTCochainComplexBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: Integer-Indexed Ghost Eigenspace E^g for Integer Ghost Numbers g : ℤ. -/
def integerGhostEigenspace
    (g_op : Module.End R (ExteriorAlgebra R V)) (g : ℤ) :=
  ghostEigenspace g_op (g : R)

/-- **Definition**: Integer-Indexed Restricted BRST Map Q_g : E^g → E^{g+1}. -/
def integerGradedBRSTMap
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g : ℤ) : integerGhostEigenspace g_op g →ₗ[R] integerGhostEigenspace g_op (g + 1) := by
  have h_map := gradedBRSTMap q g_op h_comm (g : R)
  have h_cast : ((g + 1 : ℤ) : R) = (g : R) + 1 := by push_cast; rfl
  exact LinearMap.codRestrict (ghostEigenspace g_op ((g + 1 : ℤ) : R)) (h_map.toFun) (by
    intro ⟨x, hx⟩
    dsimp [integerGhostEigenspace] at hx ⊢
    rw [h_cast]
    exact (gradedBRSTMap q g_op h_comm (g : R) ⟨x, hx⟩).2)

/-- **Theorem**: Integer-Indexed BRST Composition Nilpotency Q_{g+1} ∘ Q_g = 0. -/
theorem integer_graded_brst_composition_zero
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g : ℤ) :
    (integerGradedBRSTMap q g_op h_comm (g + 1)).comp (integerGradedBRSTMap q g_op h_comm g) = 0 := by
  ext ⟨x, hx⟩
  dsimp [integerGradedBRSTMap]
  ext
  dsimp
  have hq2_fun := LinearMap.congr_fun hq2 x
  exact hq2_fun

/-- **Definition**: Integer-Graded BRST Cohomology Module H^{g+1}_Q = Ker(Q_{g+1}) / Im(Q_g). -/
def integerGradedBRSTCohomologyDegree
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g : ℤ) :=
  LinearMap.ker (integerGradedBRSTMap q g_op h_comm (g + 1)) ⧸
    (LinearMap.range (integerGradedBRSTMap q g_op h_comm g)).comap
      (LinearMap.ker (integerGradedBRSTMap q g_op h_comm (g + 1))).subtype

/-- **Theorem**: Range-Kernel Inclusion Im(Q_g) ⊆ Ker(Q_{g+1}) for Integer Ghost Numbers g : ℤ. -/
theorem integer_graded_brst_range_le_ker
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g : ℤ)
    (chi : integerGhostEigenspace g_op g) :
    integerGradedBRSTMap q g_op h_comm g chi ∈ LinearMap.ker (integerGradedBRSTMap q g_op h_comm (g + 1)) := by
  rw [LinearMap.mem_ker]
  have h_comp := integer_graded_brst_composition_zero q g_op hq2 h_comm g
  exact LinearMap.congr_fun h_comp chi

/-- **Theorem**: Integer-Graded Exact State Class Zero [Q_g χ_g] = 0 ∈ H^{g+1}_Q. -/
theorem integer_graded_brst_exact_state_class_zero
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g : ℤ)
    (chi : integerGhostEigenspace g_op g) :
    Submodule.Quotient.mk ⟨integerGradedBRSTMap q g_op h_comm g chi, integer_graded_brst_range_le_ker q g_op hq2 h_comm g chi⟩ =
      (Submodule.Quotient.mk 0 : integerGradedBRSTCohomologyDegree q g_op hq2 h_comm g) := by
  rw [Submodule.Quotient.eq]
  rw [sub_zero]
  rw [Submodule.mem_comap]
  dsimp
  rw [LinearMap.mem_range]
  use chi

/-- **Theorem**: Master Integer-Graded BRST Cochain Complex Synthesis H^g_Q for g : ℤ.
    Unifies:
    1. Integer ghost number indexing g : ℤ for ghost eigenspaces E^g.
    2. Restricted integer BRST map Q_g : E^g → E^{g+1} and composition nilpotency Q_{g+1} ∘ Q_g = 0.
    3. Integer-graded BRST cohomology module H^{g+1}_Q = Ker(Q_{g+1}) / Im(Q_g) definition.
    4. Integer-graded exact state zero class [Q_g χ_g] = 0 ∈ H^{g+1}_Q proof closure. -/
theorem master_integer_graded_brst_cochain_complex_synthesis
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g : ℤ)
    (chi : integerGhostEigenspace g_op g) :
    ((integerGradedBRSTMap q g_op h_comm (g + 1)).comp (integerGradedBRSTMap q g_op h_comm g) = 0) ∧
    (Submodule.Quotient.mk ⟨integerGradedBRSTMap q g_op h_comm g chi, integer_graded_brst_range_le_ker q g_op hq2 h_comm g chi⟩ =
      (Submodule.Quotient.mk 0 : integerGradedBRSTCohomologyDegree q g_op hq2 h_comm g)) := ⟨
  integer_graded_brst_composition_zero q g_op hq2 h_comm g,
  integer_graded_brst_exact_state_class_zero q g_op hq2 h_comm g chi
⟩

end InfoGeometry.Canonical.IntegerGradedBRSTCochainComplexBridge
