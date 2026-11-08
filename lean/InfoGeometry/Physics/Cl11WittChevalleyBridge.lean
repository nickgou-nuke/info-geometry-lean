/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Physics.ChevalleyDyadIsomorphism

/-!
# The `Cl(1,1)` Witt operators and Chevalley dyads

This bridge relates the existing Pauli-matrix Clifford equivalence to the
existing finite Witt matrix tower and the abstract CAR dyads.

The Witt creation and annihilation operators here are elements of the Clifford
algebra, formed from the bivector `J1_cl` and the negative generator. They are
not the images of the null vectors `(1, ±1)` under the vector inclusion. With
the tower convention, creation maps to the upper matrix unit and annihilation
to the lower matrix unit. The abstract Chevalley dyad convention names its
annihilator `n` and creator `p`; consequently its `E₀₁` and `E₁₀` map to the
lower and upper matrix units, respectively.
-/

noncomputable section

namespace InfoGeometry.Physics.Cl11WittChevalleyBridge

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Physics.ChevalleyDyad
open Matrix
open scoped Matrix

/-- The tower's Witt creation operator, represented inside `Cl(1,1)`. -/
def cliffordWittCreation : CliffordAlgebra q11 :=
  (1 / 2 : ℝ) • (J1_cl + CliffordAlgebra.ι q11 (0, 1))

/-- The tower's Witt annihilation operator, represented inside `Cl(1,1)`. -/
def cliffordWittAnnihilation : CliffordAlgebra q11 :=
  (1 / 2 : ℝ) • (J1_cl - CliffordAlgebra.ι q11 (0, 1))

@[simp] theorem cl11EquivMat_J1_cl :
    cl11EquivMat J1_cl = J1 := by
  simp [J1_cl, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg,
    Eplus_mul_Eminus]

/-- The Clifford creation element maps to the tower's upper Witt matrix. -/
@[simp] theorem cl11EquivMat_wittCreation :
    cl11EquivMat cliffordWittCreation = wittCreationBase := by
  simp only [cliffordWittCreation, map_smul, map_add,
    cl11EquivMat_J1_cl, cl11EquivMat_iota_neg]
  simpa [gamma_0_base, gamma_1_base] using
    wittCreationBase_eq_half_gamma_sum.symm

/-- The Clifford annihilation element maps to the tower's lower Witt matrix. -/
@[simp] theorem cl11EquivMat_wittAnnihilation :
    cl11EquivMat cliffordWittAnnihilation = wittAnnihilationBase := by
  simp only [cliffordWittAnnihilation, map_smul, map_sub,
    cl11EquivMat_J1_cl, cl11EquivMat_iota_neg]
  simpa [gamma_0_base, gamma_1_base] using
    wittAnnihilationBase_eq_half_gamma_sub.symm

theorem cliffordWittCreation_sq :
    cliffordWittCreation * cliffordWittCreation = 0 := by
  apply cl11EquivMat.injective
  rw [map_mul, cl11EquivMat_wittCreation, map_zero]
  exact wittCreationBase_sq

theorem cliffordWittAnnihilation_sq :
    cliffordWittAnnihilation * cliffordWittAnnihilation = 0 := by
  apply cl11EquivMat.injective
  rw [map_mul, cl11EquivMat_wittAnnihilation]
  rw [map_zero, ← realEncodedWittAnnihilationBase_eq]
  exact realEncodedWittAnnihilationBase_sq

/-- The Clifford Witt elements satisfy the single-mode CAR. -/
theorem cliffordWitt_car :
    cliffordWittAnnihilation * cliffordWittCreation +
      cliffordWittCreation * cliffordWittAnnihilation = 1 := by
  apply cl11EquivMat.injective
  rw [map_add, map_mul, map_mul, map_one,
    cl11EquivMat_wittAnnihilation, cl11EquivMat_wittCreation]
  simpa [realEncodedWittCreationBase_eq, realEncodedWittAnnihilationBase_eq,
    add_comm] using realEncodedWitt_anticomm

theorem wittCreationBase_eq_matrixUnit :
    wittCreationBase = !![(0 : ℝ), 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wittCreationBase]

theorem wittAnnihilationBase_eq_matrixUnit :
    wittAnnihilationBase = !![(0 : ℝ), 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wittAnnihilationBase]

theorem wittCreation_mul_wittAnnihilation_eq_matrixUnit :
    wittCreationBase * wittAnnihilationBase =
      !![(1 : ℝ), 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wittCreationBase, wittAnnihilationBase,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem wittAnnihilation_mul_wittCreation_eq_matrixUnit :
    wittAnnihilationBase * wittCreationBase =
    !![(0 : ℝ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wittCreationBase, wittAnnihilationBase,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Under the Clifford-to-matrix equivalence the Chevalley vacuum dyad is the
lower diagonal matrix unit. This index reversal follows from the chosen vacuum
`n * p` and the tower's upper-creation/lower-annihilation convention. -/
theorem chevalley_E00_matrix :
    cl11EquivMat (ChevalleyDyad.E00 cliffordWittAnnihilation
      cliffordWittCreation) = !![(0 : ℝ), 0; 0, 1] := by
  rw [ChevalleyDyad.E00_eval cliffordWittAnnihilation cliffordWittCreation
    cliffordWittAnnihilation_sq cliffordWitt_car]
  rw [map_mul, cl11EquivMat_wittAnnihilation,
    cl11EquivMat_wittCreation, wittAnnihilation_mul_wittCreation_eq_matrixUnit]

theorem chevalley_E01_matrix :
    cl11EquivMat (ChevalleyDyad.E01 cliffordWittAnnihilation
      cliffordWittCreation) = wittAnnihilationBase := by
  rw [ChevalleyDyad.E01_eval cliffordWittAnnihilation cliffordWittCreation
    cliffordWittAnnihilation_sq cliffordWitt_car]
  exact cl11EquivMat_wittAnnihilation

theorem chevalley_E10_matrix :
    cl11EquivMat (ChevalleyDyad.E10 cliffordWittAnnihilation
      cliffordWittCreation) = wittCreationBase := by
  rw [ChevalleyDyad.E10_eval cliffordWittAnnihilation cliffordWittCreation
    cliffordWittCreation_sq cliffordWitt_car]
  exact cl11EquivMat_wittCreation

/-- The excited Chevalley dyad is the upper diagonal matrix unit. -/
theorem chevalley_E11_matrix :
    cl11EquivMat (ChevalleyDyad.E11 cliffordWittAnnihilation
      cliffordWittCreation) = !![(1 : ℝ), 0; 0, 0] := by
  rw [ChevalleyDyad.E11_eval cliffordWittAnnihilation cliffordWittCreation
    cliffordWittAnnihilation_sq cliffordWittCreation_sq cliffordWitt_car]
  rw [map_mul, cl11EquivMat_wittCreation,
    cl11EquivMat_wittAnnihilation, wittCreation_mul_wittAnnihilation_eq_matrixUnit]

end InfoGeometry.Physics.Cl11WittChevalleyBridge

end
