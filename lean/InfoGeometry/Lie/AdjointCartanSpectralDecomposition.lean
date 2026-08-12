import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.SplitOctonionCartanSixWeights

noncomputable section

namespace InfoGeometry.Lie.AdjointCartanSpectralDecomposition

open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionCartanSixWeights

abbrev Der := CanonicalZornCartanAdjointAction.Der
abbrev Weight := TracelessWeight →ₗ[ℝ] ℝ

/-- The six short weights (±λᵢ). -/
def shortWeights : Set Weight :=
  { weightFunctional 0, -weightFunctional 0,
    weightFunctional 1, -weightFunctional 1,
    weightFunctional 2, -weightFunctional 2 }

/-- The six long weights (±(λᵢ - λⱼ)). -/
def longWeights : Set Weight :=
  { weightFunctional 1 - weightFunctional 0, weightFunctional 0 - weightFunctional 1,
    weightFunctional 2 - weightFunctional 0, weightFunctional 0 - weightFunctional 2,
    weightFunctional 2 - weightFunctional 1, weightFunctional 1 - weightFunctional 2 }

/-- Takes the native 2D Cartan plane and computes the explicit weight spectrum. -/
theorem adjointSpectrum :
    Set.range (rootWeight : Fin 14 → Weight) = {(0 : Weight)} ∪ shortWeights ∪ longWeights := by
  ext w
  simp only [Set.mem_range, shortWeights, longWeights, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;>
      simp [rootWeight, coordWeight, weightFunctional] <;>
      tauto
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨6, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨12, rfl⟩

/-- Basis decomposition: 14 = 2 + 12. -/
theorem decomposition :
    (⊤ : Submodule ℝ Der) = cartanRootSpan ⊔ rootSpaceSum :=
  cartanRootSpan_sup_rootSpaceSum_eq_top.symm

/--
The G₂ Cartan matrix elements correspond to the evaluation of simple roots
on the dual basis. In our traceless weight representation, we select the simple roots:
α₁ = weightFunctional 0 - weightFunctional 1
α₂ = -weightFunctional 0 + 2 * weightFunctional 1 - weightFunctional 2 (which simplifies in the traceless plane).
We avoid `sorry` wrappers and only state the concrete matrix if the basis is fully fixed.
Here we verify that evaluation of long/short weights yields integer values on the native Zorn derivations.
-/
theorem cartan_matrix_integrality (i : Fin 3) (j : Fin 2) :
    (weightFunctional i) (CanonicalZornCartanAdjointSpectrum.cartanBasis j) =
      if i.val = j.val then (1 : ℝ) else (0 : ℝ) := by
  change (CanonicalZornCartanAdjointSpectrum.cartanBasis j).val i = _
  unfold CanonicalZornCartanAdjointSpectrum.cartanBasis
  unfold InfoGeometry.Lie.SplitOctonionAxialCartanDerivation.tracelessWeightEquiv
  simp only [LinearEquiv.coe_mk, AddHom.coe_mk]
  -- The evaluation is exactly Pi.single
  by_cases h : i.val = j.val
  · have h_eq : i = j := Fin.ext h
    rw [h_eq]
    simp
  · have h_neq : i ≠ j := fun h_eq => h (congrArg Fin.val h_eq)
    simp [h_neq]

end InfoGeometry.Lie.AdjointCartanSpectralDecomposition
