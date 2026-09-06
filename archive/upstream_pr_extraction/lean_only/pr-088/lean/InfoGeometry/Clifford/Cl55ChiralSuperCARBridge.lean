import Mathlib.Tactic
import InfoGeometry.Clifford.Cl55ThreeColorChiralGenerators
import InfoGeometry.Physics.ChiralSUSYBlockFactorization

/-!
# Native `Cl(5,5)` chiral super-CAR block readout

This owner combines the existing three-colour Clifford CAR generators with the
generic off-diagonal `2 x 2` block calculus.  Nilpotence of the block charges
comes from matrix support; the diagonal readout of their mixed
anticommutator is the native Clifford CAR relation.  The auxiliary block
grading is not identified with intrinsic Clifford chirality here.
-/

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Physics
open Matrix

noncomputable section

def cl55QPlus (i : Fin 3) : ChiralBlock Cl55 :=
  chiralQPlus (chiralPlus55 i)

def cl55QMinus (i : Fin 3) : ChiralBlock Cl55 :=
  chiralQMinus (chiralMinus55 i)

/-- The finite chiral Hodge--Dirac block obtained by adding the two nilpotent
channels.  This is an auxiliary block operator, not intrinsic Clifford
chirality. -/
def cl55HodgeDirac (i : Fin 3) : ChiralBlock Cl55 :=
  cl55QPlus i + cl55QMinus i

theorem cl55QPlus_mul_cl55QPlus_zero (i j : Fin 3) :
    cl55QPlus i * cl55QPlus j = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [cl55QPlus, chiralQPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem cl55QMinus_mul_cl55QMinus_zero (i j : Fin 3) :
    cl55QMinus i * cl55QMinus j = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [cl55QMinus, chiralQMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem cl55Q_mixed_anticommutator_eq_diagonal (i j : Fin 3) :
    cl55QPlus i * cl55QMinus j + cl55QMinus j * cl55QPlus i =
      !![chiralPlus55 i * chiralMinus55 j, 0;
         0, chiralMinus55 j * chiralPlus55 i] := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [cl55QPlus, cl55QMinus, chiralQPlus, chiralQMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem cl55HodgeDirac_sq (i : Fin 3) :
    cl55HodgeDirac i * cl55HodgeDirac i =
      cl55QPlus i * cl55QMinus i + cl55QMinus i * cl55QPlus i := by
  simp only [cl55HodgeDirac, add_mul, mul_add,
    cl55QPlus_mul_cl55QPlus_zero, cl55QMinus_mul_cl55QMinus_zero,
    zero_add, add_zero]
  rw [add_comm]

theorem cl55HodgeDirac_sq_eq_diagonal (i : Fin 3) :
    cl55HodgeDirac i * cl55HodgeDirac i =
      !![chiralPlus55 i * chiralMinus55 i, 0;
         0, chiralMinus55 i * chiralPlus55 i] := by
  rw [cl55HodgeDirac_sq, cl55Q_mixed_anticommutator_eq_diagonal]

theorem cl55HodgeDirac_parity_anticomm (i : Fin 3) :
    chiralParity * cl55HodgeDirac i +
        cl55HodgeDirac i * chiralParity = 0 := by
  calc
    chiralParity * cl55HodgeDirac i +
        cl55HodgeDirac i * chiralParity =
        (chiralParity * cl55QPlus i + cl55QPlus i * chiralParity) +
          (chiralParity * cl55QMinus i + cl55QMinus i * chiralParity) := by
            simp only [cl55HodgeDirac]
            noncomm_ring
    _ = 0 := by
      rw [show cl55QPlus i = chiralQPlus (chiralPlus55 i) from rfl,
        show cl55QMinus i = chiralQMinus (chiralMinus55 i) from rfl,
        chiralParity_qPlus_anticomm, chiralParity_qMinus_anticomm,
        add_zero]

theorem cl55Q_mixed_anticommutator_diagonal_mem_grade_zero (i j : Fin 3) :
    (cl55QPlus i * cl55QMinus j + cl55QMinus j * cl55QPlus i) 0 0 ∈
        cl55GradeSubmodule 0 ∧
      (cl55QPlus i * cl55QMinus j + cl55QMinus j * cl55QPlus i) 1 1 ∈
        cl55GradeSubmodule 0 := by
  rw [cl55Q_mixed_anticommutator_eq_diagonal]
  exact ⟨chiralPlus55_minus55_product_mem_grade_zero i j,
    chiralMinus55_plus55_product_mem_grade_zero j i⟩

theorem cl55Q_anticommutator_diagonal_sum (i j : Fin 3) :
    (cl55QPlus i * cl55QMinus j + cl55QMinus j * cl55QPlus i) 0 0 +
        (cl55QPlus i * cl55QMinus j + cl55QMinus j * cl55QPlus i) 1 1 =
      if i = j then 1 else 0 := by
  rw [cl55Q_mixed_anticommutator_eq_diagonal]
  by_cases h : i = j
  · subst j
    simpa [Matrix.cons_val_zero, Matrix.cons_val_one, add_comm] using
      (chiralMinus55_plus55_anticommutator i i)
  · have h' : j ≠ i := Ne.symm h
    simpa [Matrix.cons_val_zero, Matrix.cons_val_one, h, h', add_comm] using
      (chiralMinus55_plus55_anticommutator j i)

end

end InfoGeometry.Clifford.Clifford55
