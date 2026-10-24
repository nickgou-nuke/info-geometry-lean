import InfoGeometry.Algebra.ZornLeftParity

/-! Native split-Clifford operators on the Zorn module. The existing real CAR
owner provides its Clifford universal-property lift; these coordinate-free
operator conclusions allow every commutative coefficient ring. -/
namespace InfoGeometry.Algebra.ZornVectorMatrix
variable {R : Type*} [CommRing R]
noncomputable section

/-- Left off-diagonal multiplication has scalar square, by alternativity. -/
theorem left_offDiagonal_square (u v : ZornVec3 R) :
    L_map (R := R) (offDiagonal u v) * L_map (R := R) (offDiagonal u v) =
      ZornVec3.dot u v • (1 : Module.End R (ZornVectorMatrix R)) := by
  apply LinearMap.ext
  intro X
  change mul (offDiagonal u v) (mul (offDiagonal u v) X) = smul (ZornVec3.dot u v) X
  ext k <;> (try fin_cases k) <;>
    simp [mul, offDiagonal, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

/-- Full polarized relation, including both isotropic directions. -/
theorem left_offDiagonal_anticommutator (u v x y : ZornVec3 R) :
    L_map (R := R) (offDiagonal u v) * L_map (R := R) (offDiagonal x y) +
      L_map (R := R) (offDiagonal x y) * L_map (R := R) (offDiagonal u v) =
      (ZornVec3.dot u y + ZornVec3.dot x v) •
        (1 : Module.End R (ZornVectorMatrix R)) := by
  apply LinearMap.ext
  intro X
  change add (mul (offDiagonal u v) (mul (offDiagonal x y) X))
    (mul (offDiagonal x y) (mul (offDiagonal u v) X)) =
      smul (ZornVec3.dot u y + ZornVec3.dot x v) X
  ext k <;> (try fin_cases k) <;>
    simp [mul, offDiagonal, add, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

/-- Vector-parametric positive-square generator. -/
def leftMajoranaPlus (u : ZornVec3 R) : Module.End R (ZornVectorMatrix R) :=
  L_map (R := R) (offDiagonal u u)

/-- Vector-parametric negative-square generator. -/
def leftMajoranaMinus (u : ZornVec3 R) : Module.End R (ZornVectorMatrix R) :=
  L_map (R := R) (offDiagonal u (-u))

theorem leftMajoranaPlus_basis (i : Fin 3) :
    leftMajoranaPlus (ZornVec3.basis (R := R) i) =
      L_map (R := R) (U (R := R) i) + L_map (R := R) (V (R := R) i) := by
  apply LinearMap.ext
  intro X
  change mul (offDiagonal _ _) X = add (mul (U i) X) (mul (V i) X)
  ext k <;> simp [mul, offDiagonal, U, V, add, ZornVec3.dot, ZornVec3.cross,
    Fin.sum_univ_three] <;> abel

theorem leftMajoranaMinus_basis (i : Fin 3) :
    leftMajoranaMinus (ZornVec3.basis (R := R) i) =
      L_map (R := R) (U (R := R) i) - L_map (R := R) (V (R := R) i) := by
  apply LinearMap.ext
  intro X
  change mul (offDiagonal _ _) X = sub (mul (U i) X) (mul (V i) X)
  ext k <;> (try fin_cases k) <;>
    simp [mul, offDiagonal, U, V, sub, add, neg, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three] <;> ring

theorem leftMajoranaPlus_square (u : ZornVec3 R) :
    leftMajoranaPlus u * leftMajoranaPlus u =
      ZornVec3.dot u u • (1 : Module.End R (ZornVectorMatrix R)) :=
  left_offDiagonal_square u u

theorem leftMajoranaMinus_square (u : ZornVec3 R) :
    leftMajoranaMinus u * leftMajoranaMinus u =
      -(ZornVec3.dot u u) • (1 : Module.End R (ZornVectorMatrix R)) := by
  rw [leftMajoranaMinus, left_offDiagonal_square]
  congr 1
  simp [ZornVec3.dot, Fin.sum_univ_three]

theorem leftMajorana_mixed_anticommutator (u v : ZornVec3 R) :
    leftMajoranaPlus u * leftMajoranaMinus v +
      leftMajoranaMinus v * leftMajoranaPlus u = 0 := by
  rw [leftMajoranaPlus, leftMajoranaMinus, left_offDiagonal_anticommutator]
  have h : ZornVec3.dot u (-v) + ZornVec3.dot v u = 0 := by
    simp [ZornVec3.dot, Fin.sum_univ_three]
    ring
  rw [h, _root_.zero_smul]

theorem leftMajoranaPlus_anticommutator (u v : ZornVec3 R) :
    leftMajoranaPlus u * leftMajoranaPlus v + leftMajoranaPlus v * leftMajoranaPlus u =
      (2 * ZornVec3.dot u v) • (1 : Module.End R (ZornVectorMatrix R)) := by
  unfold leftMajoranaPlus
  rw [left_offDiagonal_anticommutator]
  congr 1
  simp [ZornVec3.dot, Fin.sum_univ_three]
  ring

theorem leftMajoranaMinus_anticommutator (u v : ZornVec3 R) :
    leftMajoranaMinus u * leftMajoranaMinus v + leftMajoranaMinus v * leftMajoranaMinus u =
      (-2 * ZornVec3.dot u v) • (1 : Module.End R (ZornVectorMatrix R)) := by
  unfold leftMajoranaMinus
  rw [left_offDiagonal_anticommutator]
  congr 1
  simp [ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Same-mode product recovers the already established mode commutator. -/
theorem leftMajorana_mode_product (i : Fin 3) :
    leftMajoranaMinus (ZornVec3.basis (R := R) i) *
      leftMajoranaPlus (ZornVec3.basis (R := R) i) =
      L_map (R := R) (U (R := R) i) * L_map (R := R) (V (R := R) i) -
        L_map (R := R) (V (R := R) i) * L_map (R := R) (U (R := R) i) := by
  rw [leftMajoranaMinus_basis, leftMajoranaPlus_basis]
  have hu : L_map (R := R) (U (R := R) i) * L_map (R := R) (U (R := R) i) = 0 := by
    simpa [offDiagonal, U, ZornVec3.dot, Pi.zero_def] using
      left_offDiagonal_square (ZornVec3.basis (R := R) i) (0 : ZornVec3 R)
  have hv : L_map (R := R) (V (R := R) i) * L_map (R := R) (V (R := R) i) = 0 := by
    simpa [offDiagonal, V, ZornVec3.dot, Pi.zero_def] using
      left_offDiagonal_square (0 : ZornVec3 R) (ZornVec3.basis (R := R) i)
  noncomm_ring [hu, hv]

theorem leftMajorana_six_factor_product :
    (leftMajoranaMinus (ZornVec3.basis (R := R) 0) * leftMajoranaPlus (ZornVec3.basis 0)) *
      (leftMajoranaMinus (ZornVec3.basis 1) * leftMajoranaPlus (ZornVec3.basis 1)) *
      (leftMajoranaMinus (ZornVec3.basis 2) * leftMajoranaPlus (ZornVec3.basis 2)) =
      L_map (R := R) (diagonal (R := R) 1 (-1)) := by
  simp only [leftMajorana_mode_product]
  have h := left_three_mode_product (R := R)
  dsimp only at h
  simpa only [_root_.neg_mul, _root_.mul_neg, sub_neg_eq_add, _root_.sub_eq_add_neg, _root_.neg_neg, _root_.add_comm] using h

theorem leftMajoranaPlus_basis_square (i : Fin 3) :
    leftMajoranaPlus (ZornVec3.basis (R := R) i) * leftMajoranaPlus (ZornVec3.basis i) = 1 := by
  rw [leftMajoranaPlus_square]
  fin_cases i <;> simp [ZornVec3.dot, ZornVec3.basis]

theorem leftMajoranaMinus_basis_square (i : Fin 3) :
    leftMajoranaMinus (ZornVec3.basis (R := R) i) * leftMajoranaMinus (ZornVec3.basis i) = -1 := by
  rw [leftMajoranaMinus_square]
  fin_cases i <;> simp [ZornVec3.dot, ZornVec3.basis]

/-- Multiplication on the left by mode parity swaps the two generators. -/
theorem leftMajorana_mode_flip_plus (i : Fin 3) :
    (leftMajoranaMinus (ZornVec3.basis (R := R) i) * leftMajoranaPlus (ZornVec3.basis i)) *
      leftMajoranaPlus (ZornVec3.basis i) = leftMajoranaMinus (ZornVec3.basis i) := by
  rw [mul_assoc, leftMajoranaPlus_basis_square, _root_.mul_one]

theorem leftMajorana_mode_flip_minus (i : Fin 3) :
    (leftMajoranaMinus (ZornVec3.basis (R := R) i) * leftMajoranaPlus (ZornVec3.basis i)) *
      leftMajoranaMinus (ZornVec3.basis i) = leftMajoranaPlus (ZornVec3.basis i) := by
  have h := leftMajorana_mixed_anticommutator (ZornVec3.basis (R := R) i) (ZornVec3.basis i)
  have hs := leftMajoranaMinus_basis_square (R := R) i
  have ha := eq_neg_of_add_eq_zero_left h
  rw [mul_assoc, ha, _root_.mul_neg, ← mul_assoc, hs]
  simp

/-- Independent mode parities commute in the associative operator algebra. -/
theorem leftMajorana_mode_products_commute (i j : Fin 3) :
    Commute
      (leftMajoranaMinus (ZornVec3.basis (R := R) i) * leftMajoranaPlus (ZornVec3.basis i))
      (leftMajoranaMinus (ZornVec3.basis (R := R) j) * leftMajoranaPlus (ZornVec3.basis j)) := by
  rw [leftMajorana_mode_product, leftMajorana_mode_product]
  apply LinearMap.ext
  intro X
  simp only [Module.End.mul_apply, left_mode_commutator_apply]
  ext k <;> simp <;> split_ifs <;> simp

/-- The sum of the three positive generators is the all-ones vector generator. -/
theorem leftMajoranaPlus_sum_basis :
    (∑ i : Fin 3, leftMajoranaPlus (ZornVec3.basis (R := R) i)) =
      leftMajoranaPlus (fun _ => (1 : R)) := by
  apply LinearMap.ext
  intro X
  simp only [Fin.sum_univ_three, LinearMap.add_apply]
  change add (add (mul (offDiagonal _ _) X) (mul (offDiagonal _ _) X))
    (mul (offDiagonal _ _) X) = mul (offDiagonal _ _) X
  ext k <;> (try fin_cases k) <;>
    simp [mul, offDiagonal, add, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three] <;> ring

theorem leftMajoranaMinus_sum_basis :
    (∑ i : Fin 3, leftMajoranaMinus (ZornVec3.basis (R := R) i)) =
      leftMajoranaMinus (fun _ => (1 : R)) := by
  apply LinearMap.ext
  intro X
  simp only [Fin.sum_univ_three, LinearMap.add_apply]
  change add (add (mul (offDiagonal _ _) X) (mul (offDiagonal _ _) X))
    (mul (offDiagonal _ _) X) = mul (offDiagonal _ _) X
  ext k <;> (try fin_cases k) <;>
    simp [mul, offDiagonal, add, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three] <;> ring

theorem leftMajoranaPlus_total_square :
    (∑ i : Fin 3, leftMajoranaPlus (ZornVec3.basis (R := R) i)) *
      (∑ i : Fin 3, leftMajoranaPlus (ZornVec3.basis (R := R) i)) =
      (3 : R) • (1 : Module.End R (ZornVectorMatrix R)) := by
  rw [leftMajoranaPlus_sum_basis, leftMajoranaPlus_square]
  norm_num [ZornVec3.dot, Fin.sum_univ_three]

theorem leftMajoranaMinus_total_square :
    (∑ i : Fin 3, leftMajoranaMinus (ZornVec3.basis (R := R) i)) *
      (∑ i : Fin 3, leftMajoranaMinus (ZornVec3.basis (R := R) i)) =
      (-3 : R) • (1 : Module.End R (ZornVectorMatrix R)) := by
  rw [leftMajoranaMinus_sum_basis, leftMajoranaMinus_square]
  norm_num [ZornVec3.dot, Fin.sum_univ_three]

theorem leftMajorana_totals_anticommute :
    (∑ i : Fin 3, leftMajoranaPlus (ZornVec3.basis (R := R) i)) *
        (∑ i : Fin 3, leftMajoranaMinus (ZornVec3.basis (R := R) i)) +
      (∑ i : Fin 3, leftMajoranaMinus (ZornVec3.basis (R := R) i)) *
        (∑ i : Fin 3, leftMajoranaPlus (ZornVec3.basis (R := R) i)) = 0 := by
  rw [leftMajoranaPlus_sum_basis, leftMajoranaMinus_sum_basis]
  exact leftMajorana_mixed_anticommutator _ _

end
end InfoGeometry.Algebra.ZornVectorMatrix
