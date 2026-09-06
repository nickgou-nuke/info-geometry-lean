import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Physics.Algebra.LinearTripotentTrifactor
import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import Mathlib.Data.Matrix.Basic

/-!
# Axial grading in the genuine circular Peirce basis

The upstream `EllCircularPeirceBasis` owner proves the eigenvalue equations
for the native commutator by `ell`.  This file only packages those equations
as a normalized grading and transports the result to the corresponding
coordinate module.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularAxialGrading

open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Physics.Algebra
open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout

abbrev CZ := CanonicalZorn
abbrev Coord := Fin 8 → ℝ

def axialWeight : Fin 8 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 0
  | 5 => -1
  | 6 => -1
  | 7 => -1

noncomputable def axialGrading : Module.End ℝ CZ :=
  (1 / 2 : ℝ) • ellCommutator

noncomputable def circularAxialGrading : Module.End ℝ Coord :=
  circularPeirceBasis.equivFun.conjAlgEquiv ℝ axialGrading

theorem circularAxialGrading_apply (X : CZ) :
    circularAxialGrading (circularPeirceBasis.equivFun X) =
      circularPeirceBasis.equivFun (axialGrading X) := by
  rw [circularAxialGrading, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply]
  change circularPeirceBasis.equivFun
    (axialGrading (circularPeirceBasis.equivFun.symm
      (circularPeirceBasis.equivFun X))) = _
  have hx : circularPeirceBasis.equivFun.symm
      (circularPeirceBasis.equivFun X) = X :=
    circularPeirceBasis.equivFun.symm_apply_apply X
  rw [hx]

theorem axialGrading_basis (i : Fin 8) :
    axialGrading (circularPeirceBasis i) =
      axialWeight i • circularPeirceBasis i := by
  fin_cases i
  · rw [axialGrading, LinearMap.smul_apply]
    simp only [circularPeirceBasis_apply, frame]
    rw [ellCommutator_uPlus]
    simp [axialWeight]
    have hzero : ({a := 0, b := 0, x := 0, y := 0} : CZ) = 0 := by rfl
    rw [hzero, smul_zero]
  · rw [axialGrading, LinearMap.smul_apply]
    simp only [circularPeirceBasis_apply, frame]
    rw [ellCommutator_rootPlus]
    simp [axialWeight]
  · rw [axialGrading, LinearMap.smul_apply]
    simp only [circularPeirceBasis_apply, frame]
    rw [ellCommutator_rootPlus]
    simp [axialWeight]
  · rw [axialGrading, LinearMap.smul_apply]
    simp only [circularPeirceBasis_apply, frame]
    rw [ellCommutator_rootPlus]
    simp [axialWeight]
  · rw [axialGrading, LinearMap.smul_apply]
    simp only [circularPeirceBasis_apply, frame]
    rw [ellCommutator_uMinus]
    simp [axialWeight]
    have hzero : ({a := 0, b := 0, x := 0, y := 0} : CZ) = 0 := by rfl
    rw [hzero, smul_zero]
  · rw [axialGrading, LinearMap.smul_apply]
    simp only [circularPeirceBasis_apply, frame]
    rw [ellCommutator_rootMinus]
    simp only [axialWeight]
    module

  · rw [axialGrading, LinearMap.smul_apply]
    simp only [circularPeirceBasis_apply, frame]
    rw [ellCommutator_rootMinus]
    simp only [axialWeight]
    module
  · rw [axialGrading, LinearMap.smul_apply]
    simp only [circularPeirceBasis_apply, frame]
    rw [ellCommutator_rootMinus]
    simp only [axialWeight]
    module

theorem circularPeirceBasis_mem_eigenspace (i : Fin 8) :
    circularPeirceBasis i ∈
      Module.End.eigenspace axialGrading (axialWeight i) := by
  rw [Module.End.mem_eigenspace_iff]
  exact axialGrading_basis i

theorem axialGrading_tripotent : axialGrading ^ 3 = axialGrading := by
  apply circularPeirceBasis.ext
  intro i
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply]
  simp only [axialGrading_basis, map_smul]
  fin_cases i <;> norm_num [axialWeight]

noncomputable def axialPPlus : Module.End ℝ CZ :=
  endProjPos axialGrading

noncomputable def axialPZero : Module.End ℝ CZ :=
  endProjZero axialGrading

noncomputable def axialPMinus : Module.End ℝ CZ :=
  endProjNeg axialGrading

theorem axialPPlus_range_eq_eigenspace :
    LinearMap.range axialPPlus = Module.End.eigenspace axialGrading 1 := by
  exact endProjPos_range_eq_eigenspace axialGrading axialGrading_tripotent

theorem axialPMinus_range_eq_eigenspace :
    LinearMap.range axialPMinus = Module.End.eigenspace axialGrading (-1) := by
  exact endProjNeg_range_eq_eigenspace axialGrading axialGrading_tripotent

theorem axialPZero_range_eq_ker :
    LinearMap.range axialPZero = LinearMap.ker axialGrading := by
  exact endProjZero_range_eq_ker axialGrading axialGrading_tripotent

def zeroWeightSubmodule : Submodule ℝ CZ :=
  Submodule.span ℝ ({uPlus, uMinus} : Set CZ)

def positiveWeightSubmodule : Submodule ℝ CZ :=
  Submodule.span ℝ (Set.range (fun i : Fin 3 => rootPlus i))

def negativeWeightSubmodule : Submodule ℝ CZ :=
  Submodule.span ℝ (Set.range (fun i : Fin 3 => rootMinus i))

theorem uPlus_mem_zeroWeight_eigenspace :
    uPlus ∈ Module.End.eigenspace axialGrading 0 := by
  have h := circularPeirceBasis_mem_eigenspace 0
  simpa [circularPeirceBasis_apply, frame, axialWeight] using h

theorem uMinus_mem_zeroWeight_eigenspace :
    uMinus ∈ Module.End.eigenspace axialGrading 0 := by
  have h := circularPeirceBasis_mem_eigenspace 4
  simpa [circularPeirceBasis_apply, frame, axialWeight] using h

theorem zeroWeightSubmodule_le_eigenspace_zero :
    zeroWeightSubmodule ≤ Module.End.eigenspace axialGrading 0 := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases hx with (rfl | rfl)
  · exact uPlus_mem_zeroWeight_eigenspace
  · exact uMinus_mem_zeroWeight_eigenspace

theorem positiveWeightSubmodule_le_eigenspace_one :
    positiveWeightSubmodule ≤ Module.End.eigenspace axialGrading 1 := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨i, rfl⟩
  fin_cases i
  · simpa [circularPeirceBasis_apply, frame, axialWeight] using
      circularPeirceBasis_mem_eigenspace (1 : Fin 8)
  · simpa [circularPeirceBasis_apply, frame, axialWeight] using
      circularPeirceBasis_mem_eigenspace (2 : Fin 8)
  · simpa [circularPeirceBasis_apply, frame, axialWeight] using
      circularPeirceBasis_mem_eigenspace (3 : Fin 8)

theorem negativeWeightSubmodule_le_eigenspace_neg_one :
    negativeWeightSubmodule ≤ Module.End.eigenspace axialGrading (-1) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨i, rfl⟩
  fin_cases i
  · simpa [circularPeirceBasis_apply, frame, axialWeight] using
      circularPeirceBasis_mem_eigenspace (5 : Fin 8)
  · simpa [circularPeirceBasis_apply, frame, axialWeight] using
      circularPeirceBasis_mem_eigenspace (6 : Fin 8)
  · simpa [circularPeirceBasis_apply, frame, axialWeight] using
      circularPeirceBasis_mem_eigenspace (7 : Fin 8)

theorem circularAxialGrading_basis (i : Fin 8) :
    circularAxialGrading (circularPeirceBasis.equivFun (circularPeirceBasis i)) =
      axialWeight i • circularPeirceBasis.equivFun (circularPeirceBasis i) := by
  rw [circularAxialGrading_apply, axialGrading_basis, map_smul]
noncomputable def sourceAxialDiagonal : Module.End ℝ CZ :=
  circularPeirceBasis.constr ℝ
    (fun i => axialWeight i • circularPeirceBasis i)

theorem sourceAxialDiagonal_basis (i : Fin 8) :
    sourceAxialDiagonal (circularPeirceBasis i) =
      axialWeight i • circularPeirceBasis i := by
  change (circularPeirceBasis.constr ℝ
      (fun j => axialWeight j • circularPeirceBasis j))
      (circularPeirceBasis i) = _
  exact circularPeirceBasis.constr_basis ℝ
    (fun j => axialWeight j • circularPeirceBasis j) i

theorem axialGrading_eq_sourceAxialDiagonal :
    axialGrading = sourceAxialDiagonal := by
  apply circularPeirceBasis.ext
  intro i
  rw [sourceAxialDiagonal_basis, axialGrading_basis]

theorem circularAxialGrading_coordinate (X : CZ) (i : Fin 8) :
    circularAxialGrading (circularPeirceBasis.equivFun X) i =
      axialWeight i * circularPeirceBasis.equivFun X i := by
  rw [circularAxialGrading_apply, axialGrading_eq_sourceAxialDiagonal]
  have hrepr := circularPeirceBasis.sum_repr X
  have hcoord (j k : Fin 8) :
      (circularPeirceBasis.repr (frame j)) k = if j = k then 1 else 0 := by
    have h := Module.Basis.equivFun_self circularPeirceBasis j k
    rw [circularPeirceBasis_apply] at h
    simpa [Pi.single_apply] using h
  rw [← hrepr]
  simp only [map_sum, map_smul, sourceAxialDiagonal_basis,
    circularPeirceBasis.equivFun_apply]
  simpa [hcoord, smul_eq_mul, mul_comm]

theorem circularAxialGrading_single (i : Fin 8) :
    circularAxialGrading (Pi.single i 1 : Coord) = axialWeight i • (Pi.single i 1 : Coord) := by
  ext j
  have h := circularAxialGrading_coordinate (circularPeirceBasis i) j
  have hequiv : circularPeirceBasis.equivFun (circularPeirceBasis i) = (Pi.single i 1 : Coord) := by
    ext k
    have heq := Module.Basis.equivFun_self circularPeirceBasis i k
    rw [heq, Pi.single_apply]
    by_cases hik : i = k
    · subst k; simp
    · have hki : k ≠ i := Ne.symm hik
      simp [hik, hki]
  rw [hequiv] at h
  rw [h, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs with hij
  · subst hij; simp
  · simp

noncomputable def circularAxialGradingMat : Matrix (Fin 8) (Fin 8) ℝ :=
  circularMatrix circularAxialGrading

theorem circularAxialGradingMat_eq :
    circularAxialGradingMat = Matrix.diagonal axialWeight := by
  ext i j
  change LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) circularAxialGrading i j = Matrix.diagonal axialWeight i j
  rw [LinearMap.toMatrix_apply]
  rw [Pi.basisFun_apply]
  change (circularAxialGrading (Pi.single j 1 : Coord)) i = _
  rw [circularAxialGrading_single, Pi.smul_apply, smul_eq_mul, Matrix.diagonal_apply, Pi.single_apply]
  split_ifs with hij
  · subst hij; simp
  · simp

end InfoGeometry.Lie.SplitOctonionCircularAxialGrading
