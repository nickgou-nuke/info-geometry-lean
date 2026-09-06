import InfoGeometry.Clifford.HestenesOddSector

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M)

/-- Генераторът γ₀ в Clifford алгебрата -/
def gamma0 : CliffordAlgebra Q := ι Q v0

/-- ТЕОРЕМА 5: γ₀² = 1 -/
theorem gamma0_sq (hv0_norm : Q v0 = 1) : gamma0 Q v0 * gamma0 Q v0 = 1 := by
  dsimp [gamma0]
  rw [ι_sq_scalar]
  rw [hv0_norm]
  simp

/-- γ₀ е нечетен елемент (вектор) -/
theorem gamma0_is_odd : gamma0 Q v0 ∈ ClMinus Q := by
  dsimp [gamma0]
  exact ι_mem_evenOdd_one Q v0

/-- Десен Паравекторен Изоморфизъм: X_R(x) = x * γ₀
    Преобразува нечетен елемент (вектор) в четен (оператор) -/
def rightParavectorEquiv (hv0_norm : Q v0 = 1) : ClMinus Q ≃ₗ[R] ClPlus Q where
  toFun x := ⟨x.val * gamma0 Q v0, clMinus_mul_clMinus Q x.val (gamma0 Q v0) x.property (gamma0_is_odd Q v0)⟩
  invFun y := ⟨y.val * gamma0 Q v0, clPlus_mul_clMinus Q y.val (gamma0 Q v0) y.property (gamma0_is_odd Q v0)⟩
  left_inv x := Subtype.ext (by
    dsimp
    rw [mul_assoc, gamma0_sq Q v0 hv0_norm, mul_one])
  right_inv y := Subtype.ext (by
    dsimp
    rw [mul_assoc, gamma0_sq Q v0 hv0_norm, mul_one])
  map_add' x y := Subtype.ext (by dsimp; rw [add_mul])
  map_smul' c x := Subtype.ext (by dsimp; rw [smul_mul_assoc])

/-- Ляв Паравекторен Изоморфизъм: X_L(x) = γ₀ * x -/
def leftParavectorEquiv (hv0_norm : Q v0 = 1) : ClMinus Q ≃ₗ[R] ClPlus Q where
  toFun x := ⟨gamma0 Q v0 * x.val, clMinus_mul_clMinus Q (gamma0 Q v0) x.val (gamma0_is_odd Q v0) x.property⟩
  invFun y := ⟨gamma0 Q v0 * y.val, clMinus_mul_clPlus Q (gamma0 Q v0) y.val (gamma0_is_odd Q v0) y.property⟩
  left_inv x := Subtype.ext (by
    dsimp
    rw [← mul_assoc, gamma0_sq Q v0 hv0_norm, one_mul])
  right_inv y := Subtype.ext (by
    dsimp
    rw [← mul_assoc, gamma0_sq Q v0 hv0_norm, one_mul])
  map_add' x y := Subtype.ext (by dsimp; rw [mul_add])
  map_smul' c x := Subtype.ext (by dsimp; rw [Algebra.mul_smul_comm])

/-- 
ТЕОРЕМА 6: X_L(x) * X_R(x) = Q(x)
За чисти вектори (x ∈ M), произведението на лявото и дясното паравекторно вложение 
възстановява скаларната норма.
-/
theorem left_mul_right_paravector_eq_norm (hv0_norm : Q v0 = 1) (x : M) :
    (leftParavectorEquiv Q v0 hv0_norm ⟨ι Q x, ι_mem_evenOdd_one Q x⟩).val * 
    (rightParavectorEquiv Q v0 hv0_norm ⟨ι Q x, ι_mem_evenOdd_one Q x⟩).val = 
    algebraMap R (CliffordAlgebra Q) (Q x) := by
  dsimp [leftParavectorEquiv, rightParavectorEquiv]
  calc (gamma0 Q v0 * ι Q x) * (ι Q x * gamma0 Q v0)
    _ = gamma0 Q v0 * (ι Q x * ι Q x) * gamma0 Q v0 := by
      rw [mul_assoc (gamma0 Q v0) (ι Q x) (ι Q x * gamma0 Q v0)]
      rw [← mul_assoc (ι Q x) (ι Q x) (gamma0 Q v0)]
      rw [← mul_assoc (gamma0 Q v0) (ι Q x * ι Q x) (gamma0 Q v0)]
    _ = gamma0 Q v0 * (algebraMap R (CliffordAlgebra Q) (Q x)) * gamma0 Q v0 := by rw [ι_sq_scalar Q x]
    _ = (algebraMap R (CliffordAlgebra Q) (Q x)) * gamma0 Q v0 * gamma0 Q v0 := by 
        rw [← Algebra.commutes (Q x) (gamma0 Q v0)]
    _ = (algebraMap R (CliffordAlgebra Q) (Q x)) * (gamma0 Q v0 * gamma0 Q v0) := by rw [mul_assoc]
    _ = (algebraMap R (CliffordAlgebra Q) (Q x)) * 1 := by rw [gamma0_sq Q v0 hv0_norm]
    _ = algebraMap R (CliffordAlgebra Q) (Q x) := by rw [mul_one]

end InfoGeometry.Clifford.Hestenes
