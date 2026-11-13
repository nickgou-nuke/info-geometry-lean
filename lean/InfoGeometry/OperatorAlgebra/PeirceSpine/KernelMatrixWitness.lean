/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.CayleyKernelRegularity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Real matrix witnesses for persistent Peirce kernels

These calculations occur in the full real matrix rings `M₃(ℝ)` and `M₄(ℝ)`.
The coupling does not commute with the cut. The three-dimensional example
has a nonzero idempotent metric different from the ambient identity. The
four-dimensional example has two linearly independent unpaired kernel
corners, so a single scalar kernel summand is not a universal description.
No classification of the generated ring or numerical rank theorem is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.KernelMatrixWitness

abbrev Op3 := Matrix (Fin 3) (Fin 3) ℝ

def cut3 : Op3 := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
def coupling3 : Op3 := !![0, 1, 0; 1, 0, 0; 0, 0, 0]
def paired3 : Op3 := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
def zeroMode3 : Op3 := !![0, 0, 0; 0, 0, 0; 0, 0, 1]

/-- The cut is an actual self-adjoint idempotent. -/
theorem cut3_projection : cut3 * cut3 = cut3 ∧ star cut3 = cut3 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [cut3, Matrix.mul_apply, Fin.sum_univ_three]

/-- The source coupling is self-adjoint. -/
theorem coupling3_selfAdjoint : star coupling3 = coupling3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [coupling3]

/-- The actual cut and coupling do not commute. -/
theorem coupling3_noncommuting : cut3 * coupling3 ≠ coupling3 * cut3 := by
  intro h
  have h01 := congrArg (fun M : Op3 => M 0 1) h
  norm_num [cut3, coupling3, Matrix.mul_apply, Fin.sum_univ_three] at h01

/-- The two-cycle metric is the proper paired support. -/
theorem metric3_value : genV cut3 coupling3 (star coupling3) = paired3 := by
  rw [coupling3_selfAdjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genV, anticomm, conePlus, coneMinus, cut3, coupling3, paired3,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.add_apply,
      Matrix.sub_apply, Fin.sum_univ_three]

/-- The metric is on shell while remaining nonzero and nonunit. -/
theorem metric3_idempotent :
    genV cut3 coupling3 (star coupling3) * genV cut3 coupling3 (star coupling3) =
      genV cut3 coupling3 (star coupling3) := by
  rw [metric3_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paired3, Matrix.mul_apply, Fin.sum_univ_three]

theorem metric3_ne_zero : genV cut3 coupling3 (star coupling3) ≠ 0 := by
  rw [metric3_value]
  intro h
  have h00 := congrArg (fun M : Op3 => M 0 0) h
  norm_num [paired3] at h00

theorem metric3_ne_one : genV cut3 coupling3 (star coupling3) ≠ 1 := by
  rw [metric3_value]
  intro h
  have h22 := congrArg (fun M : Op3 => M 2 2) h
  norm_num [paired3] at h22

/-- The residual is the third coordinate projection, not zero. -/
theorem kernel3_value : 1 - genV cut3 coupling3 (star coupling3) = zeroMode3 := by
  rw [metric3_value]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [paired3, zeroMode3]

theorem kernel3_ne_zero : zeroMode3 ≠ 0 := by
  intro h
  have h22 := congrArg (fun M : Op3 => M 2 2) h
  norm_num [zeroMode3] at h22

/-- Singular multiplication kills the explicit residual projection. -/
theorem metric3_kills_kernel : genV cut3 coupling3 (star coupling3) * zeroMode3 = 0 := by
  simpa only [kernel3_value] using
    (onShell_genV_kernel_products coupling3 (star coupling3) metric3_idempotent).1

/-- Shifted multiplication retains exactly that same nonzero projection. -/
theorem shifted_metric3_fixes_kernel :
    (1 + genV cut3 coupling3 (star coupling3)) * zeroMode3 = zeroMode3 := by
  simpa only [kernel3_value] using
    onShell_shift_fixes_kernel coupling3 (star coupling3) metric3_idempotent

abbrev Op4 := Matrix (Fin 4) (Fin 4) ℝ

def cut4 : Op4 := !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]
def coupling4 : Op4 := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
def kernelPlus4 : Op4 := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]
def kernelMinus4 : Op4 := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1]

/-- The four-dimensional cut is also an actual self-adjoint idempotent. -/
theorem cut4_projection : cut4 * cut4 = cut4 ∧ star cut4 = cut4 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [cut4, Matrix.mul_apply, Fin.sum_univ_four]

theorem coupling4_selfAdjoint : star coupling4 = coupling4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [coupling4]

/-- The second full matrix carrier also has an explicit noncommuting pair. -/
theorem coupling4_noncommuting : cut4 * coupling4 ≠ coupling4 * cut4 := by
  intro h
  have h01 := congrArg (fun M : Op4 => M 0 1) h
  norm_num [cut4, coupling4, Matrix.mul_apply, Fin.sum_univ_four] at h01

/-- The extra two coordinates are unpaired. -/
theorem metric4_value : genV cut4 coupling4 (star coupling4) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  rw [coupling4_selfAdjoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genV, anticomm, conePlus, coneMinus, cut4, coupling4,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.add_apply,
      Matrix.sub_apply, Fin.sum_univ_four]

/-- The paired metric remains idempotent with both residual corners present. -/
theorem metric4_idempotent :
    genV cut4 coupling4 (star coupling4) * genV cut4 coupling4 (star coupling4) =
      genV cut4 coupling4 (star coupling4) := by
  rw [metric4_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four]

/-- The upper unpaired corner survives separately. -/
theorem kernelPlus4_value :
    cut4 * (1 - genV cut4 coupling4 (star coupling4)) = kernelPlus4 := by
  rw [metric4_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cut4, kernelPlus4, Matrix.mul_apply, Fin.sum_univ_four]

/-- The lower unpaired corner survives separately. -/
theorem kernelMinus4_value :
    (1 - cut4) * (1 - genV cut4 coupling4 (star coupling4)) = kernelMinus4 := by
  rw [metric4_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cut4, kernelMinus4, Matrix.mul_apply, Fin.sum_univ_four]

/-- Both residual sectors lie in the actual generated ring. -/
theorem kernel4_corners_mem_generated :
    kernelPlus4 ∈ generatedPeirceRing cut4 coupling4 (star coupling4) ∧
    kernelMinus4 ∈ generatedPeirceRing cut4 coupling4 (star coupling4) := by
  have hp := cut_mem_generatedPeirceRing cut4 coupling4 (star coupling4)
  have hv := genV_mem_generatedPeirceRing cut4 coupling4 (star coupling4)
  have he := (generatedPeirceRing cut4 coupling4 (star coupling4)).sub_mem
    (generatedPeirceRing cut4 coupling4 (star coupling4)).one_mem hv
  constructor
  · rw [← kernelPlus4_value]
    exact (generatedPeirceRing cut4 coupling4 (star coupling4)).mul_mem hp he
  · rw [← kernelMinus4_value]
    exact (generatedPeirceRing cut4 coupling4 (star coupling4)).mul_mem
      ((generatedPeirceRing cut4 coupling4 (star coupling4)).sub_mem
        (generatedPeirceRing cut4 coupling4 (star coupling4)).one_mem hp) he

/-- Both unpaired corners are nonzero. -/
theorem kernel4_corners_nonzero : kernelPlus4 ≠ 0 ∧ kernelMinus4 ≠ 0 := by
  constructor
  · intro h
    have h22 := congrArg (fun M : Op4 => M 2 2) h
    norm_num [kernelPlus4] at h22
  · intro h
    have h33 := congrArg (fun M : Op4 => M 3 3) h
    norm_num [kernelMinus4] at h33

/-- Entry evaluation proves independence of the two kernel sectors over ℝ. -/
theorem kernel4_corners_independent (a b : ℝ)
    (h : a • kernelPlus4 + b • kernelMinus4 = 0) : a = 0 ∧ b = 0 := by
  constructor
  · have h22 := congrArg (fun M : Op4 => M 2 2) h
    simpa [kernelPlus4, kernelMinus4] using h22
  · have h33 := congrArg (fun M : Op4 => M 3 3) h
    simpa [kernelPlus4, kernelMinus4] using h33

end InfoGeometry.OperatorAlgebra.PeirceSpine.KernelMatrixWitness
