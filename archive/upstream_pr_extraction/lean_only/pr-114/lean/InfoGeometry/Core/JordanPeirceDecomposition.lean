import InfoGeometry.Core.PeirceDecomposition
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Core.JordanPeirceDecomposition

open InfoGeometry.Core.PeirceDecomposition

section SpecialJordan

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℝ A]

def jordanMul (x y : A) : A :=
  (1 / 2 : ℝ) • (x * y + y * x)

def jordanLeft (f : A) : A →ₗ[ℝ] A where
  toFun x := jordanMul f x
  map_add' x y := by
    simp only [jordanMul, mul_add, add_mul, smul_add]
    abel
  map_smul' r x := by
    simp [jordanMul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      smul_add, smul_smul]
    rw [mul_comm]

def IsJordanPeirceOne (f x : A) : Prop := jordanMul f x = x
def IsJordanPeirceHalf (f x : A) : Prop :=
  jordanMul f x = (1 / 2 : ℝ) • x
def IsJordanPeirceZero (f x : A) : Prop := jordanMul f x = 0

/-- The special-Jordan associator is induced by the commutator of the
associative envelope. -/
theorem jordan_associator_eq_double_commutator (x y z : A) :
    jordanMul (jordanMul x y) z - jordanMul x (jordanMul y z) =
      (1 / 4 : ℝ) •
        (y * (x * z - z * x) - (x * z - z * x) * y) := by
  simp only [jordanMul, smul_add, smul_sub,
    add_mul, mul_add, sub_mul, mul_sub]
  norm_num [smul_smul]
  noncomm_ring

theorem jordan_one_of_assoc {f x : A}
    (hl : f * x = x) (hr : x * f = x) : IsJordanPeirceOne f x := by
  dsimp [IsJordanPeirceOne, jordanMul]
  rw [hl, hr]
  rw [← two_smul ℝ x]
  rw [smul_smul]
  norm_num

theorem jordan_half_of_assoc_left {f x : A}
    (hl : f * x = x) (hr : x * f = 0) : IsJordanPeirceHalf f x := by
  dsimp [IsJordanPeirceHalf, jordanMul]
  rw [hl, hr]
  simp

theorem jordan_half_of_assoc_right {f x : A}
    (hl : f * x = 0) (hr : x * f = x) : IsJordanPeirceHalf f x := by
  dsimp [IsJordanPeirceHalf, jordanMul]
  rw [hl, hr]
  simp

theorem jordan_zero_of_assoc {f x : A}
    (hl : f * x = 0) (hr : x * f = 0) : IsJordanPeirceZero f x := by
  dsimp [IsJordanPeirceZero, jordanMul]
  rw [hl, hr]
  simp

theorem peirce11_is_jordan_one
    {f x : A} (hf : f * f = f) (hx : peirce11 f x) :
    IsJordanPeirceOne f x := by
  rcases hx with ⟨a, rfl⟩
  apply jordan_one_of_assoc
  · simp [mul_assoc, hf]
  · simp [mul_assoc, hf]

theorem peirce10_is_jordan_half
    {f x : A} (hf : f * f = f) (hx : peirce10 f x) :
    IsJordanPeirceHalf f x := by
  rcases hx with ⟨a, rfl⟩
  apply jordan_half_of_assoc_left
  · simp [mul_assoc, hf]
  · calc
      (f * a * complementIdempotent f) * f =
          f * a * (complementIdempotent f * f) := by
            simp only [mul_assoc]
      _ = 0 := by rw [complement_mul_idempotent f hf, mul_zero]

theorem peirce01_is_jordan_half
    {f x : A} (hf : f * f = f) (hx : peirce01 f x) :
    IsJordanPeirceHalf f x := by
  rcases hx with ⟨a, rfl⟩
  apply jordan_half_of_assoc_right
  · calc
      f * (complementIdempotent f * a * f) =
          (f * complementIdempotent f) * a * f := by simp only [mul_assoc]
      _ = 0 := by rw [idempotent_mul_complement f hf, zero_mul, zero_mul]
  · simp [mul_assoc, hf]

theorem peirce00_is_jordan_zero
    {f x : A} (hf : f * f = f) (hx : peirce00 f x) :
    IsJordanPeirceZero f x := by
  rcases hx with ⟨a, rfl⟩
  apply jordan_zero_of_assoc
  · calc
      f * (complementIdempotent f * a * complementIdempotent f) =
          (f * complementIdempotent f) * a * complementIdempotent f := by
            simp only [mul_assoc]
      _ = 0 := by rw [idempotent_mul_complement f hf, zero_mul, zero_mul]
  · calc
      (complementIdempotent f * a * complementIdempotent f) * f =
          complementIdempotent f * a *
            (complementIdempotent f * f) := by
              simp only [mul_assoc]
      _ = 0 := by
        rw [complement_mul_idempotent f hf, mul_zero]

theorem component11_is_jordan_one (f x : A) (hf : f * f = f) :
    IsJordanPeirceOne f (component11 f x) :=
  peirce11_is_jordan_one hf (component11_mem f x)

theorem component10_is_jordan_half (f x : A) (hf : f * f = f) :
    IsJordanPeirceHalf f (component10 f x) :=
  peirce10_is_jordan_half hf (component10_mem f x)

theorem component01_is_jordan_half (f x : A) (hf : f * f = f) :
    IsJordanPeirceHalf f (component01 f x) :=
  peirce01_is_jordan_half hf (component01_mem f x)

theorem component00_is_jordan_zero (f x : A) (hf : f * f = f) :
    IsJordanPeirceZero f (component00 f x) :=
  peirce00_is_jordan_zero hf (component00_mem f x)

theorem jordan_peirce_decomposition (f x : A) :
    x = component11 f x +
        (component10 f x + component01 f x) +
        component00 f x := by
  calc
    x = component11 f x + component10 f x +
        component01 f x + component00 f x := peirce_decomposition f x
    _ = component11 f x +
        (component10 f x + component01 f x) + component00 f x := by
      abel

end

end SpecialJordan

end InfoGeometry.Core.JordanPeirceDecomposition
