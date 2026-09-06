import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.RingTheory.SimpleModule.Basic
import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.CanonicalZornCartanCentralizer

/-!
# Native prerequisites for the Mathlib root-system bridge

The concrete adjoint decomposition and Cartan centralizer are owned by their
respective files.  The Mathlib `IsKilling.rootSystem` construction remains
downstream until finite-dimensionality, triangularizability, and
nondegeneracy of the native Killing form have genuine proofs.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornCartanRootSystem

open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Der := CanonicalZornCartanAdjointRootDecomposition.Der

instance der_finiteDimensional : FiniteDimensional ℝ Der :=
  rootDerivationBasis.finiteDimensional_of_finite

instance der_moduleFinite : Module.Finite ℝ Der :=
  Module.Finite.of_basis rootDerivationBasis

instance axialCartan_isTriangularizable :
    LieModule.IsTriangularizable ℝ axialCartanLieSubalgebra Der := by
  refine ⟨fun x ↦ ?_⟩
  let k : TracelessWeight := axialCartanLieEquiv.symm x
  apply (Submodule.eq_top_iff_forall_basis_mem rootDerivationBasis).mpr
  intro j
  apply Submodule.mem_iSup_of_mem (rootWeight j k)
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff]
  change ⁅(x : Der), rootDerivationBasis j⁆ =
    ((rootWeight j k : ℝ) • (rootDerivationBasis j : Der) : Der)
  rw [rootDerivationBasis_apply, ← adCartan_rootDerivation k j]
  rw [adCartan_apply, axialCartanLieEquiv.apply_symm_apply]
  change ⁅(x : Der), rootDerivation j⁆ = ⁅(x : Der), rootDerivation j⁆
  rfl

def nativeRootWeight (j : nonzeroIndex) :
    axialCartanLieSubalgebra → ℝ :=
  fun x => rootWeight j.1 (axialCartanLieEquiv.symm x)

theorem nativeRootWeights_separate
    {H : axialCartanLieSubalgebra} (hH : H ≠ 0) :
    ∃ j : nonzeroIndex, nativeRootWeight j H ≠ 0 := by
  let k : TracelessWeight := axialCartanLieEquiv.symm H
  have hk : k ≠ 0 := by
    intro hk
    apply hH
    have hHk : axialCartanLieEquiv k = H := by simp [k]
    rw [← hHk]
    simpa using congrArg axialCartanLieEquiv hk
  by_contra hsep
  push_neg at hsep
  have hcoord : ∀ i : Fin 3, k.1 i = 0 := by
    intro i
    fin_cases i
    · have h := hsep ⟨10, by decide, by decide⟩
      simpa [nativeRootWeight, k, rootWeight, coordWeight] using h
    · have h := hsep ⟨9, by decide, by decide⟩
      simpa [nativeRootWeight, k, rootWeight, coordWeight] using h
    · have h := hsep ⟨4, by decide, by decide⟩
      simpa [nativeRootWeight, k, rootWeight, coordWeight] using h
  apply hk
  apply Subtype.ext
  funext i
  exact hcoord i

theorem rootDerivation_mem_rootSpace (j : nonzeroIndex) :
    rootDerivation j.1 ∈
      LieAlgebra.rootSpace axialCartanLieSubalgebra (nativeRootWeight j) := by
  rw [LieAlgebra.rootSpace, LieModule.mem_genWeightSpace]
  intro x
  refine ⟨1, ?_⟩
  simp only [pow_one]
  change ⁅(x : Der), rootDerivation j.1⁆ -
    nativeRootWeight j x • (rootDerivation j.1 : Der) = 0
  change ⁅(x : Der), rootDerivation j.1⁆ -
    (rootWeight j.1 (axialCartanLieEquiv.symm x) : ℝ) •
      (rootDerivation j.1 : Der) = 0
  rw [← adCartan_rootDerivation (axialCartanLieEquiv.symm x) j.1]
  rw [adCartan_apply, axialCartanLieEquiv.apply_symm_apply]
  exact sub_self _

theorem nativeCartan_le_mathlib_rootSpace_zero :
    axialCartanLieSubalgebra.toLieSubmodule ≤
      LieAlgebra.rootSpace axialCartanLieSubalgebra 0 :=
  LieAlgebra.toLieSubmodule_le_rootSpace_zero ℝ Der axialCartanLieSubalgebra

theorem mathlib_rootSpace_zero_eq_nativeCartan :
    LieAlgebra.rootSpace axialCartanLieSubalgebra 0 =
      axialCartanLieSubalgebra.toLieSubmodule := by
  letI : IsNoetherian ℝ Der := IsNoetherian.iff_fg.mpr inferInstance
  simp

theorem mathlib_zeroRootSubalgebra_eq_nativeCartan :
    LieAlgebra.zeroRootSubalgebra ℝ Der axialCartanLieSubalgebra =
      axialCartanLieSubalgebra := by
  letI : IsNoetherian ℝ Der := IsNoetherian.iff_fg.mpr inferInstance
  exact LieAlgebra.zeroRootSubalgebra_eq_of_is_cartan
    ℝ Der axialCartanLieSubalgebra

end InfoGeometry.Lie.CanonicalZornCartanRootSystem
