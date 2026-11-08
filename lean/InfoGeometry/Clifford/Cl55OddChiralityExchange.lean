import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Clifford.Cl55SpinorChirality

open InfoGeometry.Clifford.SpinorRep

/-! The concrete odd Clifford generators exchange the two eigenspaces of
the validated Euler/chirality involution on the `cl55Atom` spinor carrier. -/

def cl55EulerProjectorPlus : SpinorMatrix 5 :=
  (1 / 2 : ℝ) • ((1 : SpinorMatrix 5) + cl55ChiralityOperator.rho)

def cl55EulerProjectorMinus : SpinorMatrix 5 :=
  (1 / 2 : ℝ) • ((1 : SpinorMatrix 5) - cl55ChiralityOperator.rho)

theorem cl55EulerProjectorPlus_mul_r0_eq_r0_mul_minus :
    cl55EulerProjectorPlus * cl55Atom.r0 =
      cl55Atom.r0 * cl55EulerProjectorMinus := by
  rw [cl55EulerProjectorPlus, cl55EulerProjectorMinus]
  simp only [smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    add_mul, mul_sub]
  rw [cl55ChiralityOperator_anticomm_r0]
  module

theorem cl55EulerProjectorMinus_mul_r0_eq_r0_mul_plus :
    cl55EulerProjectorMinus * cl55Atom.r0 =
      cl55Atom.r0 * cl55EulerProjectorPlus := by
  rw [cl55EulerProjectorPlus, cl55EulerProjectorMinus]
  simp only [smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    mul_add, sub_mul]
  rw [cl55ChiralityOperator_anticomm_r0]
  module

theorem cl55EulerProjectorPlus_mul_r5_eq_r5_mul_minus :
    cl55EulerProjectorPlus * cl55Atom.r5 =
      cl55Atom.r5 * cl55EulerProjectorMinus := by
  rw [cl55EulerProjectorPlus, cl55EulerProjectorMinus]
  simp only [smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    add_mul, mul_sub]
  rw [cl55ChiralityOperator_anticomm_r5]
  module

theorem cl55EulerProjectorMinus_mul_r5_eq_r5_mul_plus :
    cl55EulerProjectorMinus * cl55Atom.r5 =
      cl55Atom.r5 * cl55EulerProjectorPlus := by
  rw [cl55EulerProjectorPlus, cl55EulerProjectorMinus]
  simp only [smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
    mul_add, sub_mul]
  rw [cl55ChiralityOperator_anticomm_r5]
  module

theorem cl55EulerProjectorPlus_sq :
    cl55EulerProjectorPlus * cl55EulerProjectorPlus =
      cl55EulerProjectorPlus := by
  rw [cl55EulerProjectorPlus]
  rw [smul_mul_assoc, Algebra.mul_smul_comm]
  simp only [add_mul, mul_add, one_mul, mul_one,
    cl55ChiralityOperator_sq]
  module

theorem cl55EulerProjectorMinus_sq :
    cl55EulerProjectorMinus * cl55EulerProjectorMinus =
      cl55EulerProjectorMinus := by
  rw [cl55EulerProjectorMinus]
  rw [smul_mul_assoc, Algebra.mul_smul_comm]
  simp only [sub_mul, mul_sub, one_mul, mul_one,
    cl55ChiralityOperator_sq]
  module

theorem cl55_r0_maps_euler_plus_to_minus (ψ : SpinorSpace 5) :
    matrixApply cl55EulerProjectorMinus
        (matrixApply cl55Atom.r0
          (matrixApply cl55EulerProjectorPlus ψ)) =
      matrixApply cl55Atom.r0
        (matrixApply cl55EulerProjectorPlus ψ) := by
  rw [← matrixApply_mul, ← matrixApply_mul]
  rw [cl55EulerProjectorMinus_mul_r0_eq_r0_mul_plus]
  have hsq : cl55Atom.r0 * cl55EulerProjectorPlus *
      cl55EulerProjectorPlus = cl55Atom.r0 * cl55EulerProjectorPlus := by
    calc
      cl55Atom.r0 * cl55EulerProjectorPlus * cl55EulerProjectorPlus =
          cl55Atom.r0 * (cl55EulerProjectorPlus * cl55EulerProjectorPlus) :=
        mul_assoc _ _ _
      _ = cl55Atom.r0 * cl55EulerProjectorPlus := by
        rw [cl55EulerProjectorPlus_sq]
  rw [hsq]
  exact matrixApply_mul _ _ _

theorem cl55_r5_maps_euler_plus_to_minus (ψ : SpinorSpace 5) :
    matrixApply cl55EulerProjectorMinus
        (matrixApply cl55Atom.r5
          (matrixApply cl55EulerProjectorPlus ψ)) =
      matrixApply cl55Atom.r5
        (matrixApply cl55EulerProjectorPlus ψ) := by
  rw [← matrixApply_mul, ← matrixApply_mul]
  rw [cl55EulerProjectorMinus_mul_r5_eq_r5_mul_plus]
  have hsq : cl55Atom.r5 * cl55EulerProjectorPlus *
      cl55EulerProjectorPlus = cl55Atom.r5 * cl55EulerProjectorPlus := by
    calc
      cl55Atom.r5 * cl55EulerProjectorPlus * cl55EulerProjectorPlus =
          cl55Atom.r5 * (cl55EulerProjectorPlus * cl55EulerProjectorPlus) :=
        mul_assoc _ _ _
      _ = cl55Atom.r5 * cl55EulerProjectorPlus := by
        rw [cl55EulerProjectorPlus_sq]
  rw [hsq]
  exact matrixApply_mul _ _ _

theorem cl55_r0_maps_euler_minus_to_plus (ψ : SpinorSpace 5) :
    matrixApply cl55EulerProjectorPlus
        (matrixApply cl55Atom.r0
          (matrixApply cl55EulerProjectorMinus ψ)) =
      matrixApply cl55Atom.r0
        (matrixApply cl55EulerProjectorMinus ψ) := by
  rw [← matrixApply_mul, ← matrixApply_mul]
  rw [cl55EulerProjectorPlus_mul_r0_eq_r0_mul_minus]
  have hsq : cl55Atom.r0 * cl55EulerProjectorMinus *
      cl55EulerProjectorMinus = cl55Atom.r0 * cl55EulerProjectorMinus := by
    calc
      cl55Atom.r0 * cl55EulerProjectorMinus * cl55EulerProjectorMinus =
          cl55Atom.r0 * (cl55EulerProjectorMinus * cl55EulerProjectorMinus) :=
        mul_assoc _ _ _
      _ = cl55Atom.r0 * cl55EulerProjectorMinus := by
        rw [cl55EulerProjectorMinus_sq]
  rw [hsq]
  exact matrixApply_mul _ _ _

theorem cl55_r5_maps_euler_minus_to_plus (ψ : SpinorSpace 5) :
    matrixApply cl55EulerProjectorPlus
        (matrixApply cl55Atom.r5
          (matrixApply cl55EulerProjectorMinus ψ)) =
      matrixApply cl55Atom.r5
        (matrixApply cl55EulerProjectorMinus ψ) := by
  rw [← matrixApply_mul, ← matrixApply_mul]
  rw [cl55EulerProjectorPlus_mul_r5_eq_r5_mul_minus]
  have hsq : cl55Atom.r5 * cl55EulerProjectorMinus *
      cl55EulerProjectorMinus = cl55Atom.r5 * cl55EulerProjectorMinus := by
    calc
      cl55Atom.r5 * cl55EulerProjectorMinus * cl55EulerProjectorMinus =
          cl55Atom.r5 * (cl55EulerProjectorMinus * cl55EulerProjectorMinus) :=
        mul_assoc _ _ _
      _ = cl55Atom.r5 * cl55EulerProjectorMinus := by
        rw [cl55EulerProjectorMinus_sq]
  rw [hsq]
  exact matrixApply_mul _ _ _

end InfoGeometry.Clifford.Cl55SpinorChirality
