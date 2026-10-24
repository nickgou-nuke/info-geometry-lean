/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Algebra.ZornSignedCAR
import InfoGeometry.Algebra.ZornColorParity
import InfoGeometry.Algebra.ZornLeftGrading

/-! Majoranas for Q=L(U), Qstar=L(-V), over an arbitrary commutative ring.
The names plus/minus describe the square signs, not a star operation. -/
namespace InfoGeometry.Algebra.ZornVectorMatrix
noncomputable section
variable {R : Type*} [CommRing R]

/-- Q-Qstar = L(U+V). -/
def colorMajoranaPlus (i : Fin 3) : Module.End R (ZornVectorMatrix R) :=
  L_map (R := R) (offDiagonal (ZornVec3.basis i) (ZornVec3.basis i))

/-- Q+Qstar = L(U-V). -/
def colorMajoranaMinus (i : Fin 3) : Module.End R (ZornVectorMatrix R) :=
  L_map (R := R) (offDiagonal (ZornVec3.basis i) (-ZornVec3.basis i))

theorem colorMajoranaPlus_eq_U_negV (i : Fin 3) :
    colorMajoranaPlus (R := R) i = L_map (R := R) (U i : ZornVectorMatrix R) - L_map (R := R) (-(V i : ZornVectorMatrix R)) := by
  apply LinearMap.ext
  intro X
  ext k <;> simp [colorMajoranaPlus, L_map, offDiagonal, U, V, mul,
    ZornVec3.dot, ZornVec3.cross, _root_.sub_eq_add_neg, add, neg] <;> ring

theorem colorMajoranaMinus_eq_U_negV (i : Fin 3) :
    colorMajoranaMinus (R := R) i = L_map (R := R) (U i : ZornVectorMatrix R) + L_map (R := R) (-(V i : ZornVectorMatrix R)) := by
  apply LinearMap.ext
  intro X
  ext k <;> simp [colorMajoranaMinus, L_map, offDiagonal, U, V, mul,
    ZornVec3.dot, ZornVec3.cross, _root_.sub_eq_add_neg, add, neg] <;> ring

theorem colorMajoranaPlus_sq (i : Fin 3) :
    colorMajoranaPlus (R := R) i * colorMajoranaPlus i = 1 := by
  unfold colorMajoranaPlus
  rw [L_map_square_of_left_alternative zorn_left_alternative]
  apply LinearMap.ext
  intro X
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [L_map, Module.End.one_apply, mul, offDiagonal, ZornVec3.basis,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three, neg] <;> ring

theorem colorMajoranaMinus_sq (i : Fin 3) :
    colorMajoranaMinus (R := R) i * colorMajoranaMinus i = -1 := by
  unfold colorMajoranaMinus
  rw [L_map_square_of_left_alternative zorn_left_alternative]
  apply LinearMap.ext
  intro X
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [L_map, Module.End.one_apply, mul, offDiagonal, ZornVec3.basis,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three, neg] <;> ring

theorem colorMajoranaPlus_Minus_anticommutator (i j : Fin 3) :
    colorMajoranaPlus (R := R) i * colorMajoranaMinus j +
      colorMajoranaMinus j * colorMajoranaPlus i = 0 := by
  unfold colorMajoranaPlus colorMajoranaMinus
  rw [L_map_anticommutator_of_left_alternative zorn_left_alternative]
  apply LinearMap.ext
  intro X
  fin_cases i <;> fin_cases j <;>
    ext k <;> (try fin_cases k) <;>
    simp [L_map, mul, offDiagonal, add, neg, zero, ZornVec3.basis,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem colorMajoranaPlus_Plus_anticommutator (i j : Fin 3) (hij : i ≠ j) :
    colorMajoranaPlus (R := R) i * colorMajoranaPlus j +
      colorMajoranaPlus j * colorMajoranaPlus i = 0 := by
  unfold colorMajoranaPlus
  rw [L_map_anticommutator_of_left_alternative zorn_left_alternative]
  apply LinearMap.ext
  intro X
  fin_cases i <;> fin_cases j <;> try contradiction <;>
    ext k <;> (try fin_cases k) <;>
    simp [L_map, mul, offDiagonal, add, neg, zero, ZornVec3.basis,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem colorMajoranaMinus_Minus_anticommutator (i j : Fin 3) (hij : i ≠ j) :
    colorMajoranaMinus (R := R) i * colorMajoranaMinus j +
      colorMajoranaMinus j * colorMajoranaMinus i = 0 := by
  unfold colorMajoranaMinus
  rw [L_map_anticommutator_of_left_alternative zorn_left_alternative]
  apply LinearMap.ext
  intro X
  fin_cases i <;> fin_cases j <;> try contradiction <;>
    ext k <;> (try fin_cases k) <;>
    simp [L_map, mul, offDiagonal, add, neg, zero, ZornVec3.basis,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem signedColorParity_eq_minus_mul_plus (i : Fin 3) :
    signedColorParity (R := R) i = colorMajoranaMinus i * colorMajoranaPlus i := by
  rw [signedColorParity_eq_commutator,
    colorMajoranaMinus_eq_U_negV, colorMajoranaPlus_eq_U_negV]
  have hu := L_U_square_zero (R := R) i
  have hv := L_negV_square_zero (R := R) i
  calc
    _ = (L_map (R := R) (U i : ZornVectorMatrix R) * L_map (U i) - L_map (-V i) * L_map (-V i)) +
      (L_map (-V i) * L_map (U i) - L_map (U i) * L_map (-V i)) := by rw [hu, hv]; simp
    _ = _ := by noncomm_ring

private theorem colorMajorana_swap (i : Fin 3) :
    colorMajoranaPlus (R := R) i * colorMajoranaMinus i =
      -(colorMajoranaMinus i * colorMajoranaPlus i) := by
  apply eq_neg_iff_add_eq_zero.mpr
  exact colorMajoranaPlus_Minus_anticommutator i i

theorem signedColorParity_mul_plus (i : Fin 3) :
    signedColorParity (R := R) i * colorMajoranaPlus i = colorMajoranaMinus i := by
  rw [signedColorParity_eq_minus_mul_plus, _root_.mul_assoc, colorMajoranaPlus_sq,
    _root_.mul_one]

theorem plus_mul_signedColorParity (i : Fin 3) :
    colorMajoranaPlus (R := R) i * signedColorParity i = -colorMajoranaMinus i := by
  rw [signedColorParity_eq_minus_mul_plus, ← _root_.mul_assoc, colorMajorana_swap,
    _root_.neg_mul, _root_.mul_assoc, colorMajoranaPlus_sq, _root_.mul_one]

theorem signedColorParity_mul_minus (i : Fin 3) :
    signedColorParity (R := R) i * colorMajoranaMinus i = colorMajoranaPlus i := by
  rw [signedColorParity_eq_minus_mul_plus, _root_.mul_assoc, colorMajorana_swap,
    _root_.mul_neg, ← _root_.mul_assoc, colorMajoranaMinus_sq, _root_.neg_one_mul,
    neg_neg]

theorem minus_mul_signedColorParity (i : Fin 3) :
    colorMajoranaMinus (R := R) i * signedColorParity i = -colorMajoranaPlus i := by
  rw [signedColorParity_eq_minus_mul_plus, ← _root_.mul_assoc, colorMajoranaMinus_sq,
    _root_.neg_one_mul]

/-- Explicit interleaved order; other six-factor orders may change the sign. -/
theorem colorMajorana_six_product :
    (colorMajoranaMinus (R := R) 0 * colorMajoranaPlus 0) *
      (colorMajoranaMinus 1 * colorMajoranaPlus 1) *
      (colorMajoranaMinus 2 * colorMajoranaPlus 2) =
        L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) := by
  rw [← signedColorParity_eq_minus_mul_plus, ← signedColorParity_eq_minus_mul_plus,
    ← signedColorParity_eq_minus_mul_plus, signedColorParity_product]

theorem colorMajoranaPlus_odd (i : Fin 3) :
    L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) * colorMajoranaPlus i +
      colorMajoranaPlus i * L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) = 0 :=
  left_diagonal_difference_anticommutes_offDiagonal (ZornVec3.basis i) (ZornVec3.basis i)

theorem colorMajoranaPlus_tangent (i : Fin 3) :
    L_map (R := R) (E11 : ZornVectorMatrix R) * colorMajoranaPlus i +
      colorMajoranaPlus i * L_map (R := R) (E11 : ZornVectorMatrix R) = colorMajoranaPlus i :=
  left_E11_tangent_offDiagonal (ZornVec3.basis i) (ZornVec3.basis i)

theorem colorMajoranaMinus_odd (i : Fin 3) :
    L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) * colorMajoranaMinus i +
      colorMajoranaMinus i * L_map (R := R) (diagonal 1 (-1) : ZornVectorMatrix R) = 0 :=
  left_diagonal_difference_anticommutes_offDiagonal (ZornVec3.basis i) (-ZornVec3.basis i)

theorem colorMajoranaMinus_tangent (i : Fin 3) :
    L_map (R := R) (E11 : ZornVectorMatrix R) * colorMajoranaMinus i +
      colorMajoranaMinus i * L_map (R := R) (E11 : ZornVectorMatrix R) = colorMajoranaMinus i :=
  left_E11_tangent_offDiagonal (ZornVec3.basis i) (-ZornVec3.basis i)

end
end InfoGeometry.Algebra.ZornVectorMatrix
