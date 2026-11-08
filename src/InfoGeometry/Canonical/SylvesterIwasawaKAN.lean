import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace InfoGeometry.Canonical.SylvesterIwasawaKAN

variable {R : Type*} [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The core Heisenberg-Weyl commutation relation Z X = ω X Z -/
def IsSylvesterPair (ω : R) (X Z : Matrix n n R) : Prop :=
  Z * X = ω • (X * Z)

/-! ### 1. The N-Component (Nilpotent / Shear / Laplace Transform)
    The shear operation maps X ↦ X Z and Z ↦ Z.
    This corresponds to the Laplace/Fresnel quadratic chirp. -/
omit [DecidableEq n] in
theorem iwasawa_N_shear (ω : R) (X Z : Matrix n n R) (h : IsSylvesterPair ω X Z) :
    IsSylvesterPair ω (X * Z) Z := by
  dsimp [IsSylvesterPair] at *
  calc
    Z * (X * Z) = (Z * X) * Z := by rw [Matrix.mul_assoc]
    _ = (ω • (X * Z)) * Z := by rw [h]
    _ = ω • (X * Z * Z) := by rw [Matrix.smul_mul, Matrix.mul_assoc]

/-! ### 2. The K-Component (Compact / Rotation / Fourier Transform)
    The rotation maps X ↦ Z and Z ↦ X⁻¹.
    Here we model X⁻¹ as Y where X Y = Y X = I. -/
theorem iwasawa_K_rotation (ω : R) (X Z Y : Matrix n n R)
    (h : IsSylvesterPair ω X Z)
    (h_inv1 : X * Y = 1) (h_inv2 : Y * X = 1) :
    IsSylvesterPair ω Z Y := by
  dsimp [IsSylvesterPair] at *
  have h1 : Y * (Z * X) * Y = Y * (ω • (X * Z)) * Y := by rw [h]
  have h2 : Y * (Z * X) * Y = Y * Z := by
    calc
      Y * (Z * X) * Y = Y * Z * (X * Y) := by simp only [Matrix.mul_assoc]
      _ = Y * Z * 1 := by rw [h_inv1]
      _ = Y * Z := by rw [Matrix.mul_one]
  have h3 : Y * (ω • (X * Z)) * Y = ω • (Z * Y) := by
    calc
      Y * (ω • (X * Z)) * Y = ω • (Y * (X * Z) * Y) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = ω • (Y * X * Z * Y) := by simp only [Matrix.mul_assoc]
      _ = ω • (1 * Z * Y) := by rw [h_inv2]
      _ = ω • (Z * Y) := by rw [Matrix.one_mul]
  rw [h2, h3] at h1
  exact h1

/-! ### 3. The A-Component (Abelian / Scaling / Mellin Transform)
    The scaling maps X ↦ X^a and Z ↦ Z^b.
    First, we prove the Weyl shift induction relations. -/

theorem sylvester_pow_X (ω : R) (X Z : Matrix n n R) (h : IsSylvesterPair ω X Z) (a : ℕ) :
    Z * (X ^ a) = (ω ^ a) • ((X ^ a) * Z) := by
  induction a with
  | zero =>
    simp only [pow_zero, Matrix.mul_one, Matrix.one_mul, one_smul]
  | succ a ih =>
    calc
      Z * (X ^ (a + 1)) = Z * (X ^ a * X) := by rw [pow_succ]
      _ = (Z * X ^ a) * X := by rw [Matrix.mul_assoc]
      _ = ((ω ^ a) • (X ^ a * Z)) * X := by rw [ih]
      _ = (ω ^ a) • (X ^ a * (Z * X)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (ω ^ a) • (X ^ a * (ω • (X * Z))) := by rw [h]
      _ = (ω ^ a) • ω • (X ^ a * (X * Z)) := by rw [Matrix.mul_smul]
      _ = (ω ^ a * ω) • (X ^ a * X * Z) := by rw [smul_smul, Matrix.mul_assoc]
      _ = (ω ^ (a + 1)) • (X ^ (a + 1) * Z) := by rw [pow_succ, pow_succ]

theorem sylvester_pow_Z (ω : R) (X Z : Matrix n n R) (h : IsSylvesterPair ω X Z) (b : ℕ) :
    (Z ^ b) * X = (ω ^ b) • (X * (Z ^ b)) := by
  induction b with
  | zero =>
    simp only [pow_zero, Matrix.one_mul, Matrix.mul_one, one_smul]
  | succ b ih =>
    calc
      (Z ^ (b + 1)) * X = (Z ^ b * Z) * X := by rw [pow_succ]
      _ = Z ^ b * (Z * X) := by rw [Matrix.mul_assoc]
      _ = Z ^ b * (ω • (X * Z)) := by rw [h]
      _ = ω • (Z ^ b * (X * Z)) := by rw [Matrix.mul_smul]
      _ = ω • ((Z ^ b * X) * Z) := by rw [Matrix.mul_assoc]
      _ = ω • (((ω ^ b) • (X * Z ^ b)) * Z) := by rw [ih]
      _ = ω • ((ω ^ b) • (X * Z ^ b * Z)) := by rw [Matrix.smul_mul]
      _ = (ω * ω ^ b) • (X * (Z ^ b * Z)) := by rw [smul_smul, Matrix.mul_assoc]
      _ = (ω ^ (b + 1)) • (X * Z ^ (b + 1)) := by rw [pow_succ', pow_succ]

theorem sylvester_pow_XZ (ω : R) (X Z : Matrix n n R) (h : IsSylvesterPair ω X Z) (a b : ℕ) :
    (Z ^ b) * (X ^ a) = (ω ^ (a * b)) • ((X ^ a) * (Z ^ b)) := by
  induction b with
  | zero =>
    simp only [pow_zero, mul_zero, Matrix.one_mul, Matrix.mul_one, one_smul]
  | succ b ih =>
    calc
      (Z ^ (b + 1)) * (X ^ a) = (Z ^ b * Z) * (X ^ a) := by rw [pow_succ]
      _ = Z ^ b * (Z * X ^ a) := by rw [Matrix.mul_assoc]
      _ = Z ^ b * ((ω ^ a) • (X ^ a * Z)) := by rw [sylvester_pow_X ω X Z h a]
      _ = (ω ^ a) • (Z ^ b * (X ^ a * Z)) := by rw [Matrix.mul_smul]
      _ = (ω ^ a) • ((Z ^ b * X ^ a) * Z) := by rw [Matrix.mul_assoc]
      _ = (ω ^ a) • (((ω ^ (a * b)) • (X ^ a * Z ^ b)) * Z) := by rw [ih]
      _ = (ω ^ a) • ((ω ^ (a * b)) • (X ^ a * Z ^ b * Z)) := by rw [Matrix.smul_mul]
      _ = (ω ^ a * ω ^ (a * b)) • (X ^ a * (Z ^ b * Z)) := by rw [smul_smul, Matrix.mul_assoc]
      _ = (ω ^ (a + a * b)) • (X ^ a * Z ^ (b + 1)) := by rw [← pow_add, pow_succ]
      _ = (ω ^ (a * (b + 1))) • (X ^ a * Z ^ (b + 1)) := by
        congr 2
        ring

/-- The Mellin / Scaling component scales X and Z.
    We require the scaling factors a and b to satisfy a * b ≡ 1 mod N.
    Here we represent the period relation via ω^(a * b) = ω. -/
theorem iwasawa_A_scaling (ω : R) (X Z : Matrix n n R)
    (h : IsSylvesterPair ω X Z) (a b : ℕ) (h_period : ω ^ (a * b) = ω) :
    IsSylvesterPair ω (X ^ a) (Z ^ b) := by
  dsimp [IsSylvesterPair]
  rw [sylvester_pow_XZ ω X Z h a b, h_period]

end InfoGeometry.Canonical.SylvesterIwasawaKAN
