/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornVectorMatrix

/-! Mixed Peirce associators on the existing nonassociative Zorn carrier. -/
namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

/-- Two upper vectors and one lower vector give the vector triple-product defect. -/
theorem associator_upper_upper_lower (u v w : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal v 0) (offDiagonal 0 w) =
      offDiagonal (fun i => ZornVec3.dot v w * u i - ZornVec3.dot u w * v i) 0 := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

/-- In the signed lower convention `uStar = -V`, both contraction signs reverse. -/
theorem associator_upper_upper_signed_lower (u v w : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal v 0) (offDiagonal 0 (-w)) =
      offDiagonal (fun i => ZornVec3.dot u w * v i - ZornVec3.dot v w * u i) 0 := by
  rw [associator_upper_upper_lower]
  ext i <;> simp [offDiagonal, ZornVec3.dot, Fin.sum_univ_three]
  all_goals ring

/-- The second mixed sector, for arbitrary vectors rather than selected basis triples. -/
theorem associator_upper_lower_lower (u v w : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal 0 v) (offDiagonal 0 w) =
      offDiagonal 0 (fun i => ZornVec3.dot u w * v i - ZornVec3.dot u v * w i) := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

/-- Exact vanishing criterion, with no division or nondegeneracy assumptions. -/
theorem associator_upper_upper_lower_eq_zero_iff (u v w : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal v 0) (offDiagonal 0 w) = zero ↔
      ∀ i, ZornVec3.dot v w * u i = ZornVec3.dot u w * v i := by
  rw [associator_upper_upper_lower]
  constructor
  · intro h i
    have hi := congrArg (fun X : ZornVectorMatrix R => X.v i) h
    exact sub_eq_zero.mp hi
  · intro h
    ext i <;> simp [offDiagonal, zero, h]

/-- The mixed triple from the intake has zero associator; the three-upper
witness is already `associator_U_zero_U_one_U_two` in the native owner. -/
theorem associator_U_zero_U_one_V_two :
    associator (U 0 : ZornVectorMatrix R) (U 1) (V 2) = zero := by
  unfold associator
  rw [U_zero_mul_U_one, V_mul_self_zero, U_one_mul_V_two, mul_zero]
  ext i <;> simp [sub, add, neg, zero]

/-- Canonical conjugation exchanges the diagonal Peirce components. -/
theorem conj_diagonal (a b : R) :
    conj (diagonal a b : ZornVectorMatrix R) = diagonal b a := by
  ext i <;> simp [conj, diagonal]


/-! The remaining Peirce table, for arbitrary vectors over the base ring. -/

theorem associator_upper_upper_upper (u v w : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal v 0) (offDiagonal w 0) =
      diagonal (-ZornVec3.dot (ZornVec3.cross u v) w) (ZornVec3.dot (ZornVec3.cross u v) w) := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal, diagonal,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  all_goals ring

theorem associator_lower_lower_lower (u v w : ZornVec3 R) :
    associator (offDiagonal 0 u) (offDiagonal 0 v) (offDiagonal 0 w) =
      diagonal (-ZornVec3.dot (ZornVec3.cross u v) w) (ZornVec3.dot (ZornVec3.cross u v) w) := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal, diagonal,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  all_goals ring

theorem associator_upper_upper_E11 (u v : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal v 0) E11 =
      offDiagonal 0 (ZornVec3.cross u v) := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal, E11,
      ZornVec3.dot, ZornVec3.cross]

theorem associator_upper_upper_E22 (u v : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal v 0) E22 =
      offDiagonal 0 (-ZornVec3.cross u v) := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal, E22,
      ZornVec3.dot, ZornVec3.cross]

theorem associator_lower_lower_E11 (u v : ZornVec3 R) :
    associator (offDiagonal 0 u) (offDiagonal 0 v) E11 =
      offDiagonal (ZornVec3.cross u v) 0 := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal, E11,
      ZornVec3.dot, ZornVec3.cross]

theorem associator_lower_lower_E22 (u v : ZornVec3 R) :
    associator (offDiagonal 0 u) (offDiagonal 0 v) E22 =
      offDiagonal (-ZornVec3.cross u v) 0 := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal, E22,
      ZornVec3.dot, ZornVec3.cross]

theorem associator_upper_lower_E11 (u v : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal 0 v) E11 =
      zero := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal, E11, zero,
      ZornVec3.dot, ZornVec3.cross]

theorem associator_upper_lower_E22 (u v : ZornVec3 R) :
    associator (offDiagonal u 0) (offDiagonal 0 v) E22 =
      zero := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal, E22, zero,
      ZornVec3.dot, ZornVec3.cross]

/-- The elliptic three-plane lies in an associative quaternion subalgebra. -/
theorem associator_elliptic_vectors (u v w : ZornVec3 R) :
    associator (offDiagonal u (-u)) (offDiagonal v (-v))
      (offDiagonal w (-w)) = zero := by
  ext i <;> (try fin_cases i) <;>
    simp [associator, sub, add, neg, mul, offDiagonal, zero,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

/-- The trace orientation is positive two for the owner's Zorn convention. -/
theorem trace_elliptic_triple (u v w : ZornVec3 R) :
    trace (mul (mul (offDiagonal u (-u)) (offDiagonal v (-v)))
      (offDiagonal w (-w))) = 2 * ZornVec3.dot u (ZornVec3.cross v w) := by
  simp [trace, mul, offDiagonal, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  ring

/-- Genuine product derivations preserve the associator by a three-slot Leibniz law.
This does not assert that fixing two associator arguments gives a derivation. -/
theorem derivation_map_associator (D : Derivation (R := R))
    (X Y Z : ZornVectorMatrix R) :
    D (associator X Y Z) =
      add (add (associator (D X) Y Z) (associator X (D Y) Z))
        (associator X Y (D Z)) := by
  simp only [associator, D.map_sub, D.map_mul, add_mul, mul_add]
  ext i <;> simp [sub, add, neg] <;> ring

set_option maxHeartbeats 2000000 in
/-- Exact defect of the Filippov identity on trace-zero Zorn elements.
The two fixed arguments are `E11 - E22` and `U 0`; the three variable
arguments are `E11 - E22`, `U 1`, and `V 0`. -/
theorem associator_filippov_defect :
    let H : ZornVectorMatrix R := diagonal 1 (-1)
    sub (associator H (U 0) (associator H (U 1) (V 0)))
      (add (add (associator (associator H (U 0) H) (U 1) (V 0))
        (associator H (associator H (U 0) (U 1)) (V 0)))
        (associator H (U 1) (associator H (U 0) (V 0)))) =
      smul (-4 : R) (U 1) := by
  dsimp
  ext i <;> (try fin_cases i) <;>
    norm_num [associator, sub, add, neg, mul, diagonal, U, V, smul,
      ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

/-- If four is nonzero, the Zorn associator is not a Filippov three-bracket. -/
theorem associator_not_filippov [NeZero (4 : R)] :
    ¬ ∀ A B X Y Z : ZornVectorMatrix R,
      associator A B (associator X Y Z) =
        add (add (associator (associator A B X) Y Z)
          (associator X (associator A B Y) Z))
          (associator X Y (associator A B Z)) := by
  intro h
  have hd := associator_filippov_defect (R := R)
  dsimp only at hd
  rw [h] at hd
  have hc := congrArg (fun W : ZornVectorMatrix R => W.v 1) hd
  apply NeZero.ne (4 : R)
  simpa [sub, add, neg, smul, U, ZornVec3.basis, eq_comm] using hc

end InfoGeometry.Algebra.ZornVectorMatrix
