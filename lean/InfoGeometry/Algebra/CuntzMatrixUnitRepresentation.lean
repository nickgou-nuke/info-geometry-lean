import InfoGeometry.Algebra.CuntzN

/-!
# Matrix representations derived from a Cuntz presentation

The existing algebraic presentation supplies only the Cuntz relations. Matrix
units, a unital matrix algebra map, and the obstruction to a normalized cyclic
functional are derived here. The construction works over the real numbers and
does not identify a formal linear dagger with complex conjugation.
-/

noncomputable section

namespace InfoGeometry.Algebra.Cuntz

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

namespace AlgebraicCuntzNPresentation

variable {N : ℕ} (P : AlgebraicCuntzNPresentation R N A)

def matrixUnit (i j : Fin N) : A := P.S i * P.T j

theorem matrixUnit_mul (i j k l : Fin N) :
    P.matrixUnit i j * P.matrixUnit k l =
      if j = k then P.matrixUnit i l else 0 := by
  simp only [matrixUnit]
  calc
    (P.S i * P.T j) * (P.S k * P.T l) =
        P.S i * (P.T j * P.S k) * P.T l := by simp [mul_assoc]
    _ = P.S i * (if j = k then 1 else 0) * P.T l := by rw [P.isometry]
    _ = _ := by split_ifs <;> simp

theorem matrixUnit_sum_diag : (∑ i : Fin N, P.matrixUnit i i) = 1 :=
  P.range_sum

theorem matrixUnit_star [StarRing A] (hstar : ∀ i, star (P.S i) = P.T i)
    (i j : Fin N) : star (P.matrixUnit i j) = P.matrixUnit j i := by
  have ht : star (P.T j) = P.S j := by rw [← hstar j, star_star]
  simp [matrixUnit, star_mul, hstar, ht]

include P in
/-- Cyclicity determines the value at the unit, before normalization is imposed. -/
theorem cyclic_value_one (τ : A →ₗ[R] R)
    (hcyclic : ∀ a b, τ (a * b) = τ (b * a)) :
    τ 1 = (N : R) * τ 1 := by
  calc
    τ 1 = τ (∑ i : Fin N, P.S i * P.T i) := by rw [P.range_sum]
    _ = ∑ i : Fin N, τ (P.S i * P.T i) := map_sum τ _ _
    _ = ∑ i : Fin N, τ (P.T i * P.S i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hcyclic _ _
    _ = (N : R) * τ 1 := by simp [P.isometry]

end AlgebraicCuntzNPresentation

namespace AlgebraicCuntzNPresentation

variable (P : AlgebraicCuntzNPresentation R 2 A)

theorem matrixUnit_two_diag : P.matrixUnit 0 0 + P.matrixUnit 1 1 = 1 := by
  simpa only [Fin.sum_univ_two] using P.matrixUnit_sum_diag

/-- The finite matrix subalgebra is derived from the presented generators. -/
def matrixTwoLinear : Matrix (Fin 2) (Fin 2) R →ₗ[R] A where
  toFun M := M 0 0 • P.matrixUnit 0 0 + M 0 1 • P.matrixUnit 0 1 +
    M 1 0 • P.matrixUnit 1 0 + M 1 1 • P.matrixUnit 1 1
  map_add' M K := by simp only [Matrix.add_apply, add_smul]; abel
  map_smul' r M := by simp [smul_add, smul_smul]

@[simp] theorem matrixTwoLinear_apply (M : Matrix (Fin 2) (Fin 2) R) :
    P.matrixTwoLinear M =
      M 0 0 • P.matrixUnit 0 0 + M 0 1 • P.matrixUnit 0 1 +
      M 1 0 • P.matrixUnit 1 0 + M 1 1 • P.matrixUnit 1 1 := rfl

@[simp] theorem matrixTwoLinear_one : P.matrixTwoLinear 1 = 1 := by
  simpa [matrixTwoLinear] using P.matrixUnit_two_diag

theorem matrixTwoLinear_mul (M K : Matrix (Fin 2) (Fin 2) R) :
    P.matrixTwoLinear (M * K) = P.matrixTwoLinear M * P.matrixTwoLinear K := by
  simp only [matrixTwoLinear_apply, Matrix.mul_apply, Fin.sum_univ_two,
    add_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    matrixUnit_mul]
  norm_num
  simp only [smul_smul, mul_comm]
  abel

def matrixTwoHom : Matrix (Fin 2) (Fin 2) R →ₐ[R] A where
  toFun := P.matrixTwoLinear
  map_zero' := map_zero P.matrixTwoLinear
  map_one' := P.matrixTwoLinear_one
  map_add' := map_add P.matrixTwoLinear
  map_mul' := P.matrixTwoLinear_mul
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, P.matrixTwoLinear_one,
      Algebra.algebraMap_eq_smul_one]

@[simp] theorem matrixTwoHom_apply (M : Matrix (Fin 2) (Fin 2) R) :
    P.matrixTwoHom M = P.matrixTwoLinear M := rfl

include P in
/-- A cyclic functional on a two-isometry Cuntz presentation vanishes at `1`. -/
theorem cyclic_value_one_eq_zero (τ : A →ₗ[R] R)
    (hcyclic : ∀ a b, τ (a * b) = τ (b * a)) : τ 1 = 0 := by
  have h := P.cyclic_value_one τ hcyclic
  have h' : τ 1 + 0 = τ 1 + τ 1 := by simpa [two_mul] using h
  exact (add_left_cancel h').symm

include P in
theorem no_normalized_cyclic_functional [Nontrivial R] :
    ¬ ∃ τ : A →ₗ[R] R, τ 1 = 1 ∧ ∀ a b, τ (a * b) = τ (b * a) := by
  rintro ⟨τ, hnorm, hcyclic⟩
  have hzero := P.cyclic_value_one_eq_zero τ hcyclic
  rw [hnorm] at hzero
  exact one_ne_zero hzero

theorem matrixUnit_zero_zero_ne_one [Nontrivial A] : P.matrixUnit 0 0 ≠ 1 := by
  intro h
  have hzero : P.matrixUnit 0 0 * P.S 1 = 0 := by
    simp [matrixUnit, mul_assoc, P.isometry]
  rw [h, one_mul] at hzero
  have hisom := P.isometry 1 1
  rw [hzero, mul_zero] at hisom
  simp at hisom

/-- The unrepaired block has a proper range projection in its first square sector. -/
theorem raw_isometry_block_square :
    (!![0, P.S 0; P.T 0, 0] : Matrix (Fin 2) (Fin 2) A) ^ 2 =
      !![P.matrixUnit 0 0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, matrixUnit, P.isometry]

theorem raw_isometry_block_not_involution [Nontrivial A] :
    (!![0, P.S 0; P.T 0, 0] : Matrix (Fin 2) (Fin 2) A) ^ 2 ≠ 1 := by
  intro h
  rw [P.raw_isometry_block_square] at h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 0) h
  exact P.matrixUnit_zero_zero_ne_one (by simpa using hentry)

end AlgebraicCuntzNPresentation

end InfoGeometry.Algebra.Cuntz
