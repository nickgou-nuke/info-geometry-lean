import Mathlib.Tactic

/-!
# Squashing/Cayley/Fredholm/Möbius transforms of biquaternions

The squashing operator is the Cayley transform `C(z)=(z-1)/(z+1)`.  Its
fixed points solve `z²=-1`, and on a Pauli-biquaternion line `aI+bσ₁`,
Fredholm resolvents and Möbius transforms stay in the same biquaternionic line.
-/

noncomputable section

namespace BiquaternionMobiusSquashing

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## Scalar squashing / Cayley transform -/

def scalarCayley (z : ℂ) : ℂ := (z - 1) / (z + 1)

/-- Fixed points of `z ↦ (z-1)/(z+1)` satisfy the fixed-point polynomial. -/
theorem scalarCayley_fixed_poly_of_fixed (z : ℂ) (hz : z + 1 ≠ 0)
    (hfix : scalarCayley z = z) : z^2 + 1 = 0 := by
  unfold scalarCayley at hfix
  have hmul := congrArg (fun w => w * (z + 1)) hfix
  field_simp [hz] at hmul
  calc
    z^2 + 1 = z * (z + 1) - (z - 1) := by ring
    _ = 0 := by rw [← hmul]; ring

/-- The fixed-point polynomial is `z²+1`, hence the analytic fixed points are `±i`. -/
def fixedPointPolynomial (z : ℂ) : ℂ := z^2 + 1

/-- Cayley squashing of an exponential parameter `E`: `(E-1)/(E+1)`.
Analytically, for `E=exp K`, this is `tanh(K/2)`. -/
def expCayleySquash (E : ℂ) : ℂ := (E - 1) / (E + 1)

/-- The Cayley squashing parameter is exactly the scalar Cayley transform. -/
theorem expCayleySquash_eq_scalarCayley (E : ℂ) :
    expCayleySquash E = scalarCayley E := by
  rfl

/-- Algebraic reconstruction of the exponential ratio from the squashed
parameter `κ=(E-1)/(E+1)`: `E=(1+κ)/(1-κ)`, away from poles. -/
theorem exp_of_squash {E κ : ℂ} (hE : E + 1 ≠ 0) (hκ : κ = expCayleySquash E)
    (hden : 1 - κ ≠ 0) : E = (1 + κ) / (1 - κ) := by
  subst κ
  unfold expCayleySquash
  field_simp [hE, hden]
  ring

/-! ## Pauli-biquaternion resolvent -/

/-- Pauli `σ₁`. -/
def σ1 : M2C := !![0, 1; 1, 0]

theorem σ1_sq : σ1 * σ1 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [σ1, Matrix.mul_apply, Fin.sum_univ_two]

/-- Two-dimensional Pauli-biquaternion subalgebra element `aI+bσ₁`. -/
def Xab (a b : ℂ) : M2C := a • (1 : M2C) + b • σ1

/-- Inverse candidate for `A I + B σ₁`. -/
def invPauli (A B : ℂ) : M2C :=
  (1 / (A^2 - B^2)) • (A • (1 : M2C) - B • σ1)

/-- Inverse identity for `A I+Bσ₁`. -/
theorem pauli_inverse_identity (A B : ℂ) (h : A^2 - B^2 ≠ 0) :
    Xab A B * invPauli A B = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Xab, invPauli, σ1, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_two] <;>
    field_simp [h] <;> ring

/-- Explicit Fredholm resolvent candidate for `(sI-X)⁻¹`. -/
def resolventCandidate (s a b : ℂ) : M2C := invPauli (s - a) (-b)

/-- Fredholm resolvent identity for `X=aI+bσ₁`. -/
theorem resolvent_identity (s a b : ℂ) (h : (s - a)^2 - b^2 ≠ 0) :
    (s • (1 : M2C) - Xab a b) * resolventCandidate s a b = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Xab, resolventCandidate, invPauli, σ1, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_two] <;>
    field_simp [h] <;> ring

/-- Resolvent determinant. -/
theorem resolvent_det (s a b : ℂ) :
    (s • (1 : M2C) - Xab a b).det = (s - a)^2 - b^2 := by
  simp [Xab, σ1, Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
  ring

/-! ## Matrix Cayley squashing closure -/

/-- Matrix Cayley/squashing transform coefficients for `X=aI+bσ₁`. -/
def cayleyAlpha (a b : ℂ) : ℂ := ((a - 1) * (a + 1) - b^2) / ((a + 1)^2 - b^2)
def cayleyBeta (a b : ℂ) : ℂ := (2 * b) / ((a + 1)^2 - b^2)

/-- Cayley transform remains in the Pauli-biquaternion subalgebra. -/
theorem cayley_biquaternion_closure (a b : ℂ) (h : (a + 1)^2 - b^2 ≠ 0) :
    (Xab a b - 1) * invPauli (a + 1) b = Xab (cayleyAlpha a b) (cayleyBeta a b) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Xab, invPauli, cayleyAlpha, cayleyBeta, σ1, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_two] <;>
    field_simp [h] <;> ring

/-! ## General Möbius transform closure -/

/-- Coefficients of `(pX+qI)(rX+tI)⁻¹`. -/
def mobiusAlpha (p q r t a b : ℂ) : ℂ :=
  (((p*a + q) * (r*a + t)) - (p*b)*(r*b)) / ((r*a + t)^2 - (r*b)^2)

def mobiusBeta (p q r t a b : ℂ) : ℂ :=
  (((p*b) * (r*a + t)) - ((p*a + q) * (r*b))) / ((r*a + t)^2 - (r*b)^2)

/-- General scalar-coefficient Möbius transform preserves the biquaternion line. -/
theorem mobius_biquaternion_closure (p q r t a b : ℂ)
    (h : (r*a + t)^2 - (r*b)^2 ≠ 0) :
    (p • Xab a b + q • (1 : M2C)) * invPauli (r*a + t) (r*b) =
    Xab (mobiusAlpha p q r t a b) (mobiusBeta p q r t a b) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Xab, invPauli, mobiusAlpha, mobiusBeta, σ1, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_two] <;>
    field_simp [h] <;> ring

end BiquaternionMobiusSquashing
