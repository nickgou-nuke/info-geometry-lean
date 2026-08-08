import Mathlib

/-!
# Biquaternion Laplace resolvent and tripotent scale poles

Formalizes the algebraic core of the prompt:

* for `X=a₀I+a·σ`, the matrix Laplace transform of `exp(tX)` is the resolvent
  `(sI-X)⁻¹`, and the Pauli algebra gives a closed numerator/denominator;
* `exp(z)` is never zero for finite complex `z`, so zero monodromy is a limiting
  scale phenomenon rather than a finite exponential;
* the tripotent defect `diag(1,-1,0)` has spectral polynomial
  `s(s-1)(s+1)`, encoding poles at `-1,0,+1`.
-/

noncomputable section

namespace BiquaternionLaplaceTripotent

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ

/-- Pauli σ₁. -/
def σ₁ : M2C := !![0, 1; 1, 0]
/-- Pauli σ₂. -/
def σ₂ : M2C := !![0, -I; I, 0]
/-- Pauli σ₃. -/
def σ₃ : M2C := !![1, 0; 0, -1]

/-- Traceless Pauli vector. -/
def pauliT (a₁ a₂ a₃ : ℂ) : M2C := a₁ • σ₁ + a₂ • σ₂ + a₃ • σ₃

/-- Pauli squaring identity. -/
theorem pauliT_sq (a₁ a₂ a₃ : ℂ) :
    pauliT a₁ a₂ a₃ * pauliT a₁ a₂ a₃ =
      (a₁ * a₁ + a₂ * a₂ + a₃ * a₃) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliT, σ₁, σ₂, σ₃, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    ring_nf <;>
    (try rw [show (I : ℂ) ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]; ring_nf)

/-- Biquaternion matrix `X=a₀I+a·σ`. -/
def biquatX (a₀ a₁ a₂ a₃ : ℂ) : M2C := a₀ • (1 : M2C) + pauliT a₁ a₂ a₃

/-- Numerator of the closed-form resolvent. -/
def resolventNumerator (s a₀ a₁ a₂ a₃ : ℂ) : M2C :=
  (s - a₀) • (1 : M2C) + pauliT a₁ a₂ a₃

/-- Denominator of the closed-form resolvent. -/
def resolventDenominator (s a₀ a₁ a₂ a₃ : ℂ) : ℂ :=
  (s - a₀) * (s - a₀) - (a₁ * a₁ + a₂ * a₂ + a₃ * a₃)

/-- Left resolvent identity: `(sI-X)N = ΔI`. -/
theorem biquat_resolvent_left (s a₀ a₁ a₂ a₃ : ℂ) :
    (s • (1 : M2C) - biquatX a₀ a₁ a₂ a₃) * resolventNumerator s a₀ a₁ a₂ a₃ =
      resolventDenominator s a₀ a₁ a₂ a₃ • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [biquatX, resolventNumerator, resolventDenominator, pauliT, σ₁, σ₂, σ₃,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    (try rw [show (I : ℂ) ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]; ring_nf)

/-- Right resolvent identity: `N(sI-X) = ΔI`. -/
theorem biquat_resolvent_right (s a₀ a₁ a₂ a₃ : ℂ) :
    resolventNumerator s a₀ a₁ a₂ a₃ * (s • (1 : M2C) - biquatX a₀ a₁ a₂ a₃) =
      resolventDenominator s a₀ a₁ a₂ a₃ • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [biquatX, resolventNumerator, resolventDenominator, pauliT, σ₁, σ₂, σ₃,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    (try rw [show (I : ℂ) ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]; ring_nf)

/-- Finite complex exponentials are never zero, so finite scalar monodromy cannot be `0`. -/
theorem complex_exp_ne_zero (z : ℂ) : Complex.exp z ≠ 0 := Complex.exp_ne_zero z

/-! ## Tripotent scale poles -/

/-- Tripotent scale-defect operator with eigenvalues `+1,-1,0`. -/
def Trip : M3C := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- `Trip³=Trip`. -/
theorem Trip_tripotent : Trip * Trip * Trip = Trip := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Trip, Matrix.mul_apply, Fin.sum_univ_three]

/-- Matrix `sI-Trip`. -/
def scaleMatrix (s : ℂ) : M3C := s • (1 : M3C) - Trip

/-- Determinant of the tripotent scale matrix: poles at `s=1,-1,0`. -/
theorem scaleMatrix_det (s : ℂ) :
    (scaleMatrix s).det = (s - 1) * (s + 1) * s := by
  simp [scaleMatrix, Trip, Matrix.det_fin_three, Matrix.smul_apply, Matrix.sub_apply]

/-- The determinant vanishes at the bosonic pole `s=1`. -/
theorem scale_det_at_one : (scaleMatrix 1).det = 0 := by simp [scaleMatrix_det]

/-- The determinant vanishes at the fermionic pole `s=-1`. -/
theorem scale_det_at_neg_one : (scaleMatrix (-1)).det = 0 := by simp [scaleMatrix_det]

/-- The determinant vanishes at the non-invertible zero-mode pole `s=0`. -/
theorem scale_det_at_zero : (scaleMatrix 0).det = 0 := by simp [scaleMatrix_det]

/-- Synthesis theorem. -/
theorem biquaternion_laplace_tripotent_synthesis :
    (∀ s a₀ a₁ a₂ a₃ : ℂ,
      (s • (1 : M2C) - biquatX a₀ a₁ a₂ a₃) * resolventNumerator s a₀ a₁ a₂ a₃ =
        resolventDenominator s a₀ a₁ a₂ a₃ • (1 : M2C)) ∧
    (∀ s a₀ a₁ a₂ a₃ : ℂ,
      resolventNumerator s a₀ a₁ a₂ a₃ * (s • (1 : M2C) - biquatX a₀ a₁ a₂ a₃) =
        resolventDenominator s a₀ a₁ a₂ a₃ • (1 : M2C)) ∧
    (∀ z : ℂ, Complex.exp z ≠ 0) ∧
    Trip * Trip * Trip = Trip ∧
    (∀ s : ℂ, (scaleMatrix s).det = (s - 1) * (s + 1) * s) ∧
    (scaleMatrix 1).det = 0 ∧ (scaleMatrix (-1)).det = 0 ∧ (scaleMatrix 0).det = 0 := by
  constructor
  · intro s a₀ a₁ a₂ a₃
    exact biquat_resolvent_left s a₀ a₁ a₂ a₃
  constructor
  · intro s a₀ a₁ a₂ a₃
    exact biquat_resolvent_right s a₀ a₁ a₂ a₃
  constructor
  · intro z
    exact complex_exp_ne_zero z
  constructor
  · exact Trip_tripotent
  constructor
  · intro s
    exact scaleMatrix_det s
  constructor
  · exact scale_det_at_one
  constructor
  · exact scale_det_at_neg_one
  · exact scale_det_at_zero

#check pauliT_sq
#check biquat_resolvent_left
#check biquat_resolvent_right
#check complex_exp_ne_zero
#check Trip_tripotent
#check scaleMatrix_det
#check biquaternion_laplace_tripotent_synthesis

end BiquaternionLaplaceTripotent
