import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
import InfoGeometry.Lie.SplitOctonionImaginaryThreeForm

/-!
# Circular-basis readout of the native imaginary three-form

This owner consumes the canonical Zorn circular multiplication table and the
existing trace-zero commutator three-form.  It introduces only subtype views
of the already existing diagonal and upper/lower Peirce generators.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryCircularForm

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionImaginaryThreeForm
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionEllFlowOperator
open InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable

abbrev Imaginary := SplitOctonionImaginaryAction.Imaginary

def diagonalAxis : Imaginary :=
  ⟨diagEll, by
    simp [mem_imaginary_iff, diagEll, zornPlus, zornMinus, realZornTrace]⟩

def upperAxis (i : Fin 3) : Imaginary :=
  ⟨cartesianZornLinearEquiv (rootPlus i), by
    rw [mem_imaginary_iff, cartesianZorn_rootPlus]
    simp [chiralUpperBasis, realZornTrace]⟩

def lowerAxis (i : Fin 3) : Imaginary :=
  ⟨cartesianZornLinearEquiv (rootMinus i), by
    rw [mem_imaginary_iff, cartesianZorn_rootMinus]
    simp [chiralLowerBasis, realZornTrace]⟩

@[simp] theorem imaginaryCross_diagonal_upper (i : Fin 3) :
    imaginaryCross diagonalAxis (upperAxis i) = upperAxis i := by
  apply Subtype.ext
  change (1 / 2 : ℝ) •
      (diagEll * cartesianZornLinearEquiv (rootPlus i) -
        cartesianZornLinearEquiv (rootPlus i) * diagEll) =
    cartesianZornLinearEquiv (rootPlus i)
  rw [diagEll_mul_cartesianZorn_rootPlus,
    cartesianZorn_rootPlus_mul_diagEll]
  module

@[simp] theorem imaginaryCross_diagonal_lower (i : Fin 3) :
    imaginaryCross diagonalAxis (lowerAxis i) = -lowerAxis i := by
  apply Subtype.ext
  change (1 / 2 : ℝ) •
      (diagEll * cartesianZornLinearEquiv (rootMinus i) -
        cartesianZornLinearEquiv (rootMinus i) * diagEll) =
    -(cartesianZornLinearEquiv (rootMinus i))
  rw [diagEll_mul_cartesianZorn_rootMinus,
    cartesianZorn_rootMinus_mul_diagEll]
  module

theorem imaginaryThreeForm_diagonal_upper_lower (i j : Fin 3) :
    imaginaryThreeForm diagonalAxis (upperAxis i) (lowerAxis j) =
      -(if i = j then (1 : ℝ) else 0) := by
  rw [imaginaryThreeForm, imaginaryCross_diagonal_upper,
    imaginaryPolarBilin_apply]
  unfold imaginaryPolar
  fin_cases i <;> fin_cases j <;>
  simp [upperAxis, lowerAxis, rootPlus, rootMinus, quaternionAxis,
    ellAxis, axis, cartesianZorn_rootPlus,
    cartesianZorn_rootMinus, chiralUpperBasis, chiralLowerBasis,
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ, dot, Fin.sum_univ_three,
    Pi.single_apply, Equiv.smul_def, coordEquiv] <;> norm_num

theorem imaginaryThreeForm_diagonal_lower_upper (i j : Fin 3) :
    imaginaryThreeForm diagonalAxis (lowerAxis i) (upperAxis j) =
      (if i = j then (1 : ℝ) else 0) := by
  rw [imaginaryThreeForm, imaginaryCross_diagonal_lower,
    imaginaryPolarBilin_apply]
  unfold imaginaryPolar
  fin_cases i <;> fin_cases j <;>
  simp [upperAxis, lowerAxis, rootPlus, rootMinus, quaternionAxis,
    ellAxis, axis, cartesianZorn_rootPlus,
    cartesianZorn_rootMinus, chiralUpperBasis, chiralLowerBasis,
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ, dot, Fin.sum_univ_three,
    Pi.single_apply, Equiv.smul_def, coordEquiv] <;> norm_num

theorem imaginaryThreeForm_upper_upper_upper (i j k : Fin 3) :
    imaginaryThreeForm (upperAxis i) (upperAxis j) (upperAxis k) =
      -(leviCivita3 k i j : ℝ) := by
  unfold imaginaryThreeForm
  rw [imaginaryPolarBilin_apply]
  unfold imaginaryPolar
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [imaginaryCross,
      upperAxis, rootPlus, quaternionAxis, ellAxis, axis,
      chiralUpperBasis, chiralLowerBasis,
      realZornTrace, mul_def, mul, dot, cross,
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
      leviCivita3, Fin.sum_univ_three, Pi.single_apply,
      Equiv.smul_def, coordEquiv] <;> norm_num

theorem imaginaryThreeForm_lower_lower_lower (i j k : Fin 3) :
    imaginaryThreeForm (lowerAxis i) (lowerAxis j) (lowerAxis k) =
      (leviCivita3 k i j : ℝ) := by
  unfold imaginaryThreeForm
  rw [imaginaryPolarBilin_apply]
  unfold imaginaryPolar
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [imaginaryCross,
      lowerAxis, rootMinus, quaternionAxis, ellAxis, axis,
      chiralUpperBasis, chiralLowerBasis,
      realZornTrace, mul_def, mul, dot, cross,
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
      leviCivita3, Fin.sum_univ_three, Pi.single_apply,
      Equiv.smul_def, coordEquiv] <;> norm_num

theorem imaginaryThreeForm_diagonal_upper_upper (i j : Fin 3) :
    imaginaryThreeForm diagonalAxis (upperAxis i) (upperAxis j) = 0 := by
  rw [imaginaryThreeForm, imaginaryCross_diagonal_upper,
    imaginaryPolarBilin_apply]
  unfold imaginaryPolar
  fin_cases i <;> fin_cases j <;>
    simp [upperAxis, rootPlus, quaternionAxis, ellAxis, axis,
      chiralUpperBasis, realZornTrace, mul_def, mul, dot,
      cross, InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
      Fin.sum_univ_three, Pi.single_apply, Equiv.smul_def,
      coordEquiv] <;> norm_num

theorem imaginaryThreeForm_diagonal_lower_lower (i j : Fin 3) :
    imaginaryThreeForm diagonalAxis (lowerAxis i) (lowerAxis j) = 0 := by
  rw [imaginaryThreeForm, imaginaryCross_diagonal_lower,
    imaginaryPolarBilin_apply]
  unfold imaginaryPolar
  fin_cases i <;> fin_cases j <;>
    simp [lowerAxis, rootMinus, quaternionAxis, ellAxis, axis,
      chiralLowerBasis, realZornTrace, mul_def, mul, dot,
      cross, InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
      Fin.sum_univ_three, Pi.single_apply, Equiv.smul_def,
      coordEquiv] <;> norm_num

theorem imaginaryThreeForm_upper_upper_lower (i j k : Fin 3) :
    imaginaryThreeForm (upperAxis i) (upperAxis j) (lowerAxis k) = 0 := by
  unfold imaginaryThreeForm
  rw [imaginaryPolarBilin_apply]
  unfold imaginaryPolar
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [imaginaryCross,
      upperAxis, lowerAxis, rootPlus, rootMinus, quaternionAxis, ellAxis,
      axis, chiralUpperBasis, chiralLowerBasis,
      realZornTrace, mul_def, mul, dot, cross, leviCivita3,
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
      Fin.sum_univ_three, Pi.single_apply, Equiv.smul_def, coordEquiv] <;>
    norm_num

theorem imaginaryThreeForm_lower_lower_upper (i j k : Fin 3) :
    imaginaryThreeForm (lowerAxis i) (lowerAxis j) (upperAxis k) = 0 := by
  unfold imaginaryThreeForm
  rw [imaginaryPolarBilin_apply]
  unfold imaginaryPolar
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [imaginaryCross,
      upperAxis, lowerAxis, rootPlus, rootMinus, quaternionAxis, ellAxis,
      axis, chiralUpperBasis, chiralLowerBasis,
      realZornTrace, mul_def, mul, dot, cross, leviCivita3,
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
      Fin.sum_univ_three, Pi.single_apply, Equiv.smul_def, coordEquiv] <;>
    norm_num

end InfoGeometry.Lie.SplitOctonionImaginaryCircularForm
