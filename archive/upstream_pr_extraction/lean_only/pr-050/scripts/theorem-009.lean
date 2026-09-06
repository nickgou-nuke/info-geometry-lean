import Mathlib

open Matrix

/-!
# Kac-Moody affine A₁⁽¹⁾ Root System — Imaginary Root δ

The generalized Cartan matrix for affine A₁⁽¹⁾ is A = [[2, -2], [-2, 2]].
This matrix is singular (det = 0), characterizing it as affine type.
The nullspace is spanned by δ = (1,1)ᵗ, the primitive imaginary root.
-/

-- The affine A₁⁽¹⁾ generalized Cartan matrix over ℤ
def A1_1_Cartan : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -2;
     -2, 2]

-- The imaginary root delta = (1,1) as a column vector
def delta : Matrix (Fin 2) (Fin 1) ℤ :=
  !![1; 1]

-- Determinant over ℤ is zero
theorem det_A1_1_zero : (A1_1_Cartan : Matrix (Fin 2) (Fin 2) ℤ).det = 0 := by
  native_decide

-- A · δ = 0
theorem A_times_delta_zero : A1_1_Cartan * delta = 0 := by
  native_decide

-- Cartan matrix is symmetric
theorem A_symmetric : A1_1_Cartan = A1_1_Cartanᵀ := by
  native_decide

-- δ ≠ 0
theorem delta_nonzero : delta ≠ 0 := by
  intro h
  have h0 : delta 0 0 = (0 : ℤ) := by simpa [h] using rfl
  simp [delta] at h0

-- The main theorem: A₁⁽¹⁾ det = 0, A·δ = 0, δ ≠ 0
theorem kac_moody_A1_1_imaginary_root_delta :
    (A1_1_Cartan : Matrix (Fin 2) (Fin 2) ℤ).det = 0 ∧
    A1_1_Cartan * delta = 0 ∧
    delta ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · exact delta_nonzero
