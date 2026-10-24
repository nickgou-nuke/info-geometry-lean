/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Algebra.ZornColorMajorana

/-! Three-mode totals and the common rotation action on both Majorana families.
All products are composition on the existing Zorn module, never octonion reassociation.
-/
namespace InfoGeometry.Algebra.ZornVectorMatrix
noncomputable section
variable {R : Type*} [CommRing R]
open scoped BigOperators

def colorMajoranaPlusTotal : Module.End R (ZornVectorMatrix R) :=
  ∑ i : Fin 3, colorMajoranaPlus i

theorem colorMajoranaPlusTotal_eq :
    colorMajoranaPlusTotal (R := R) =
      L_map (R := R) (offDiagonal (fun _ => (1 : R)) (fun _ => (1 : R))) := by
  apply LinearMap.ext
  intro X
  ext k <;> (try fin_cases k) <;>
    simp [colorMajoranaPlusTotal, colorMajoranaPlus, Fin.sum_univ_three,
      L_map, offDiagonal, mul, add, neg, ZornVec3.dot, ZornVec3.cross,
      ZornVec3.basis] <;> ring

def colorMajoranaMinusTotal : Module.End R (ZornVectorMatrix R) :=
  ∑ i : Fin 3, colorMajoranaMinus i

theorem colorMajoranaMinusTotal_eq :
    colorMajoranaMinusTotal (R := R) =
      L_map (R := R) (offDiagonal (fun _ => (1 : R)) (fun _ => (-1 : R))) := by
  apply LinearMap.ext
  intro X
  ext k <;> (try fin_cases k) <;>
    simp [colorMajoranaMinusTotal, colorMajoranaMinus, Fin.sum_univ_three,
      L_map, offDiagonal, mul, add, neg, ZornVec3.dot, ZornVec3.cross,
      ZornVec3.basis] <;> ring

theorem colorMajoranaPlusTotal_sq :
    colorMajoranaPlusTotal (R := R) * colorMajoranaPlusTotal =
      (3 : R) • (1 : Module.End R (ZornVectorMatrix R)) := by
  rw [colorMajoranaPlusTotal_eq, L_map_square_of_left_alternative zorn_left_alternative]
  apply LinearMap.ext
  intro X
  ext k <;> (try fin_cases k) <;>
    simp [L_map, offDiagonal, mul, smul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three] <;> ring

theorem colorMajoranaMinusTotal_sq :
    colorMajoranaMinusTotal (R := R) * colorMajoranaMinusTotal =
      (-3 : R) • (1 : Module.End R (ZornVectorMatrix R)) := by
  rw [colorMajoranaMinusTotal_eq, L_map_square_of_left_alternative zorn_left_alternative]
  apply LinearMap.ext
  intro X
  ext k <;> (try fin_cases k) <;>
    simp [L_map, offDiagonal, mul, smul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three] <;> ring

theorem colorMajoranaTotals_anticommutator :
    colorMajoranaPlusTotal (R := R) * colorMajoranaMinusTotal +
      colorMajoranaMinusTotal * colorMajoranaPlusTotal = 0 := by
  rw [colorMajoranaPlusTotal_eq, colorMajoranaMinusTotal_eq,
    L_map_anticommutator_of_left_alternative zorn_left_alternative]
  apply LinearMap.ext
  intro X
  ext k <;> (try fin_cases k) <;>
    simp [L_map, offDiagonal, mul, add, neg, zero, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem colorMajoranaPlusTotal_odd :
    L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) * colorMajoranaPlusTotal +
      colorMajoranaPlusTotal * L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) = 0 := by
  rw [colorMajoranaPlusTotal_eq]
  exact left_diagonal_difference_anticommutes_offDiagonal (fun _ => 1) (fun _ => (1 : R))

theorem colorMajoranaMinusTotal_odd :
    L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) * colorMajoranaMinusTotal +
      colorMajoranaMinusTotal * L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) = 0 := by
  rw [colorMajoranaMinusTotal_eq]
  exact left_diagonal_difference_anticommutes_offDiagonal (fun _ => 1) (fun _ => (-1 : R))

/-- Difference of the two signed bivectors, on the existing endomorphism ring. -/
def colorMajoranaRotation (i j : Fin 3) : Module.End R (ZornVectorMatrix R) :=
  colorMajoranaPlus i * colorMajoranaPlus j - colorMajoranaMinus i * colorMajoranaMinus j

theorem colorMajoranaRotation_Plus (i j k : Fin 3) :
    colorMajoranaRotation (R := R) i j * colorMajoranaPlus k -
      colorMajoranaPlus k * colorMajoranaRotation i j =
        (if j = k then (2 : R) • colorMajoranaPlus i else 0) -
        (if i = k then (2 : R) • colorMajoranaPlus j else 0) := by
  apply LinearMap.ext
  intro X
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    ext l <;> (try fin_cases l) <;>
    simp [colorMajoranaRotation, colorMajoranaPlus, colorMajoranaMinus,
      Module.End.mul_apply, L_map, offDiagonal, mul, add, neg, smul,
      _root_.sub_eq_add_neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis,
      Fin.sum_univ_three] <;> ring

theorem colorMajoranaRotation_Minus (i j k : Fin 3) :
    colorMajoranaRotation (R := R) i j * colorMajoranaMinus k -
      colorMajoranaMinus k * colorMajoranaRotation i j =
        (if j = k then (2 : R) • colorMajoranaMinus i else 0) -
        (if i = k then (2 : R) • colorMajoranaMinus j else 0) := by
  apply LinearMap.ext
  intro X
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    ext l <;> (try fin_cases l) <;>
    simp [colorMajoranaRotation, colorMajoranaPlus, colorMajoranaMinus,
      Module.End.mul_apply, L_map, offDiagonal, mul, add, neg, smul,
      _root_.sub_eq_add_neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis,
      Fin.sum_univ_three] <;> ring

end
end InfoGeometry.Algebra.ZornVectorMatrix
