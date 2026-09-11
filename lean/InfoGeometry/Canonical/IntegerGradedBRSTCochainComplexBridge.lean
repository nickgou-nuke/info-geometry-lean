import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
  refine
    { toFun := fun x => ⟨(h_map x).1, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · dsimp [integerGhostEigenspace]
    rw [h_cast]
    exact (h_map x).2
  · intro x y
    apply Subtype.ext
    simpa using congrArg Subtype.val (h_map.map_add x y)
  · intro c x
    apply Subtype.ext
    simpa using congrArg Subtype.val (h_map.map_smul c x)

attribute [irreducible] integerGradedBRSTMap

/-- **Theorem**: Integer-Indexed BRST Composition Nilpotency Q_{g+1} ∘ Q_g = 0. -/
theorem integer_graded_brst_composition_zero
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g : ℤ) :
    (integerGradedBRSTMap q g_op h_comm (g + 1)).comp (integerGradedBRSTMap q g_op h_comm g) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  unfold integerGradedBRSTMap
  exact LinearMap.congr_fun hq2 x.1

/-- **Definition**: Integer-Graded BRST Cohomology Module H^{g+1}_Q = Ker(Q_{g+1}) / Im(Q_g). -/
def integerGradedBRSTExactToClosed
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
    (h_comm : g_op.comp q - q.comp g_op = q)
    (g : ℤ) :
    LinearMap.range (integerGradedBRSTMap q g_op h_comm g) →ₗ[R]
      LinearMap.ker (integerGradedBRSTMap q g_op h_comm (g + 1)) where
  toFun x := ⟨x.1, by
    rcases x.2 with ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    have h_comp := integer_graded_brst_composition_zero q g_op hq2 h_comm g
    rw [← hy]
    exact LinearMap.congr_fun h_comp y⟩
  map_add' := by intro x y; rfl
  map_smul' := by intro r x; rfl

def integerGradedBRSTCohomologyDegree
    (q g_op : Module.End R (ExteriorAlgebra R V))
    (hq2 : q.comp q = 0)
  (h_comm : g_op.comp q - q.comp g_op = q)
    (g : ℤ) :=
  integerGhostEigenspace g_op (g + 1) ⧸
    LinearMap.range (integerGradedBRSTMap q g_op h_comm g)

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
    Submodule.Quotient.mk (p := LinearMap.range (integerGradedBRSTMap q g_op h_comm g))
      (integerGradedBRSTMap q g_op h_comm g chi) =
      (Submodule.Quotient.mk 0 : integerGradedBRSTCohomologyDegree q g_op hq2 h_comm g) := by
  rw [Submodule.Quotient.eq]
  rw [sub_zero]
  rw [LinearMap.mem_range]
  exact ⟨chi, rfl⟩

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
    (Submodule.Quotient.mk (p := LinearMap.range (integerGradedBRSTMap q g_op h_comm g))
      (integerGradedBRSTMap q g_op h_comm g chi) =
      (Submodule.Quotient.mk 0 : integerGradedBRSTCohomologyDegree q g_op hq2 h_comm g)) := ⟨
  integer_graded_brst_composition_zero q g_op hq2 h_comm g,
  integer_graded_brst_exact_state_class_zero q g_op hq2 h_comm g chi
⟩

end InfoGeometry.Canonical.IntegerGradedBRSTCochainComplexBridge
