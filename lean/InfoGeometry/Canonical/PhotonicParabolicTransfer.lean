import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.Canonical.PhotonicParabolicTransfer

Concrete parabolic transport model (2x2 real upper-unitriangular transfer matrices):
`T χ = [[1, χ], [0, 1]]`.
-/

namespace InfoGeometry.Canonical.PhotonicParabolicTransfer

open Matrix

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Parabolic transfer matrix for shear parameter `χ`. -/
def T (χ : ℝ) : M2R := !![1, χ; 0, 1]

/--
Parabolic transport composition law:
successive shears add their parameters.
-/
theorem T_mul (χ₁ χ₂ : ℝ) : T χ₁ * T χ₂ = T (χ₁ + χ₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply] <;> ring

/-- Determinant is preserved on the parabolic transport lane (`det = 1`). -/
theorem det_T (χ : ℝ) : Matrix.det (T χ) = 1 := by
  simp [T]

/-- Inverse transport is given by negating the shear parameter. -/
theorem T_inv (χ : ℝ) : T χ * T (-χ) = (1 : M2R) := by
  calc
    T χ * T (-χ) = T (χ + (-χ)) := by simpa using T_mul χ (-χ)
    _ = T 0 := by simp
    _ = (1 : M2R) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [T]

/--
Parabolic transfer matrices commute:
`T χ₁ * T χ₂ = T χ₂ * T χ₁`.
-/
theorem T_comm (χ₁ χ₂ : ℝ) : T χ₁ * T χ₂ = T χ₂ * T χ₁ := by
  calc
    T χ₁ * T χ₂ = T (χ₁ + χ₂) := by simpa using T_mul χ₁ χ₂
    _ = T (χ₂ + χ₁) := by congr 1; ring
    _ = T χ₂ * T χ₁ := by simpa using (T_mul χ₂ χ₁).symm

/-- Cast normalization helper for transport-parameter recursion. -/
lemma cast_succ_mul (n : ℕ) (χ : ℝ) :
    (((n : ℝ) + 1) * χ) = (((n + 1 : ℕ) : ℝ) * χ) := by
  norm_num

/--
Closed form for repeated parabolic transport:
`T χ ^ n = T ((n : ℝ) * χ)`.
-/
theorem T_pow (χ : ℝ) : ∀ n : ℕ, (T χ) ^ n = T ((n : ℝ) * χ) := by
  intro n
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [T]
  | succ n ih =>
      calc
        (T χ) ^ (n + 1) = (T χ) ^ n * T χ := by simp [pow_succ]
        _ = T (n * χ) * T χ := by rw [ih]
        _ = T (n * χ + χ) := by simpa using T_mul (n * χ) χ
        _ = T (((n : ℝ) + 1) * χ) := by
              congr 1
              ring
        _ = T (((n + 1 : ℕ) : ℝ) * χ) := by
              exact congrArg T (cast_succ_mul n χ)

/-- Repeated transfer through a two-wall periodic cell. -/
theorem T_periodic_cell_pow (χ₁ χ₂ : ℝ) (n : ℕ) :
    (T χ₁ * T χ₂) ^ n = T ((n : ℝ) * (χ₁ + χ₂)) := by
  calc
    (T χ₁ * T χ₂) ^ n = (T (χ₁ + χ₂)) ^ n := by rw [T_mul]
    _ = T ((n : ℝ) * (χ₁ + χ₂)) := by simpa using T_pow (χ₁ + χ₂) n

/--
Parameter identifiability on the parabolic transfer lane:
if two transfer matrices are equal, their shear parameters are equal.
-/
theorem T_injective {χ₁ χ₂ : ℝ} (h : T χ₁ = T χ₂) : χ₁ = χ₂ := by
  have h01 := congrArg (fun M : M2R => M 0 1) h
  simpa [T] using h01

/-- Equality characterization for the parabolic transfer family. -/
theorem T_eq_iff (χ₁ χ₂ : ℝ) : T χ₁ = T χ₂ ↔ χ₁ = χ₂ := by
  constructor
  · exact T_injective
  · intro h
    simpa [h]

/--
Left-cancellation on the transfer family:
if `T a * T b = T a * T c`, then `b = c`.
-/
theorem T_left_cancel (a b c : ℝ) (h : T a * T b = T a * T c) : b = c := by
  have h' : T (a + b) = T (a + c) := by
    simpa [T_mul] using h
  have hs : a + b = a + c := T_injective h'
  linarith

/--
Right-cancellation on the transfer family:
if `T b * T a = T c * T a`, then `b = c`.
-/
theorem T_right_cancel (a b c : ℝ) (h : T b * T a = T c * T a) : b = c := by
  have h' : T (b + a) = T (c + a) := by
    simpa [T_mul] using h
  have hs : b + a = c + a := T_injective h'
  linarith

/--
Identity-product characterization:
`T a * T b = I` iff `a + b = 0`.
-/
theorem T_mul_eq_one_iff (a b : ℝ) :
    T a * T b = (1 : M2R) ↔ a + b = 0 := by
  constructor
  · intro h
    have hT : T (a + b) = (1 : M2R) := by simpa [T_mul] using h
    have h01 := congrArg (fun M : M2R => M 0 1) hT
    simpa [T] using h01
  · intro hsum
    calc
      T a * T b = T (a + b) := by simpa using T_mul a b
      _ = T 0 := by simpa [hsum]
      _ = (1 : M2R) := by
            ext i j
            fin_cases i <;> fin_cases j <;> simp [T]

/-- Identity characterization for a single parabolic transfer matrix. -/
theorem T_eq_one_iff (χ : ℝ) : T χ = (1 : M2R) ↔ χ = 0 := by
  constructor
  · intro h
    have h01 := congrArg (fun M : M2R => M 0 1) h
    simpa [T] using h01
  · intro hχ
    calc
      T χ = T 0 := by simpa [hχ]
      _ = (1 : M2R) := by
            ext i j
            fin_cases i <;> fin_cases j <;> simp [T]

/--
Composition identifiability:
`T a * T b = T c` iff the shear parameters satisfy `a + b = c`.
-/
theorem T_mul_eq_T_iff (a b c : ℝ) :
    T a * T b = T c ↔ a + b = c := by
  constructor
  · intro h
    have h' : T (a + b) = T c := by simpa [T_mul] using h
    exact T_injective h'
  · intro hsum
    calc
      T a * T b = T (a + b) := by simpa using T_mul a b
      _ = T c := by simpa [hsum]

end InfoGeometry.Canonical.PhotonicParabolicTransfer
