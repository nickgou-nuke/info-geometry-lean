import Mathlib

/-!
# Minkowski spacetime inside the complexified split-octonions

We formalize the quaternionic subalgebra of `ℂ ⊗ O_s` by its faithful
Pauli-matrix realization:

* `e₀ ↦ I₂`;
* `eⱼ ↦ -i σⱼ`, so `e₁²=e₂²=e₃²=-1`;
* the spacetime embedding
  `X_oct = t e₀ + i x e₁ + i y e₂ + i z e₃`
  becomes the usual Pauli/Minkowski matrix
  `tI+xσ₁+yσ₂+zσ₃`;
* its determinant is `t²-x²-y²-z²`;
* the octonionic boost generator `v i e₁` squares to `v²` and exponentiates
  in the closed `cosh/sinh` span;
* determinant-one boost matrices preserve the interval under `X ↦ ΛXΛ`.
-/

noncomputable section

namespace SplitOctonionMinkowski

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli matrices. -/
def σ1 : M2C := !![0, 1; 1, 0]
def σ2 : M2C := !![0, -Complex.I; Complex.I, 0]
def σ3 : M2C := !![1, 0; 0, -1]

/-- Complexified quaternionic subalgebra basis inside `ℂ ⊗ O_s`. -/
def oct_e0 : M2C := 1
def oct_e1 : M2C := (-Complex.I) • σ1
def oct_e2 : M2C := (-Complex.I) • σ2
def oct_e3 : M2C := (-Complex.I) • σ3

/-- The first octonionic imaginary unit squares to `-1`. -/
theorem oct_e1_sq : oct_e1 * oct_e1 = (-1 : ℂ) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oct_e1, σ1, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]

/-- The second octonionic imaginary unit squares to `-1`. -/
theorem oct_e2_sq : oct_e2 * oct_e2 = (-1 : ℂ) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oct_e2, σ2, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]

/-- The third octonionic imaginary unit squares to `-1`. -/
theorem oct_e3_sq : oct_e3 * oct_e3 = (-1 : ℂ) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oct_e3, σ3, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]

/-- Spacetime vector embedded into the complexified octonionic quaternionic subalgebra. -/
def octonionicSpacetime (t x y z : ℂ) : M2C :=
  t • oct_e0 + (Complex.I * x) • oct_e1 +
    (Complex.I * y) • oct_e2 + (Complex.I * z) • oct_e3

/-- Usual Pauli/Minkowski matrix. -/
def minkowskiMatrix (t x y z : ℂ) : M2C :=
  t • (1 : M2C) + x • σ1 + y • σ2 + z • σ3

/-- The octonionic embedding is exactly the Pauli/Minkowski matrix. -/
theorem octonionicSpacetime_eq_minkowski (t x y z : ℂ) :
    octonionicSpacetime t x y z = minkowskiMatrix t x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [octonionicSpacetime, minkowskiMatrix, oct_e0, oct_e1, oct_e2, oct_e3,
      σ1, σ2, σ3, Matrix.smul_apply, Matrix.add_apply] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

/-- Closed entry form. -/
theorem minkowskiMatrix_entries (t x y z : ℂ) :
    minkowskiMatrix t x y z = !![t + z, x - Complex.I * y; x + Complex.I * y, t - z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiMatrix, σ1, σ2, σ3, Matrix.smul_apply, Matrix.add_apply] <;> ring

/-- The determinant of the octonionic spacetime embedding is the Minkowski interval. -/
theorem octonionic_minkowski_interval (t x y z : ℂ) :
    (octonionicSpacetime t x y z).det = t^2 - x^2 - y^2 - z^2 := by
  rw [octonionicSpacetime_eq_minkowski, minkowskiMatrix_entries]
  simp [Matrix.det_fin_two]
  have hI : Complex.I * Complex.I = -1 := by simp [Complex.I_mul_I]
  calc
    (t + z) * (t - z) - (x - Complex.I * y) * (x + Complex.I * y)
        = t^2 - z^2 - (x^2 - (Complex.I * Complex.I) * y^2) := by ring
    _ = t^2 - z^2 - (x^2 - (-1 : ℂ) * y^2) := by rw [hI]
    _ = t^2 - x^2 - y^2 - z^2 := by ring

/-- Octonionic boost generator `v i e₁`. -/
def octBoostGenerator (v : ℂ) : M2C := v • (Complex.I • oct_e1)

/-- The octonionic boost generator is the Pauli boost generator. -/
theorem octBoostGenerator_eq (v : ℂ) : octBoostGenerator v = v • σ1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [octBoostGenerator, oct_e1, σ1, Matrix.smul_apply]

/-- The boost generator squares to a scalar. -/
theorem octBoostGenerator_sq (v : ℂ) :
    octBoostGenerator v * octBoostGenerator v = (v * v) • (1 : M2C) := by
  rw [octBoostGenerator_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ1, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]

/-- Closed octonionic boost expression. -/
def octBoostClosed (eps v : ℂ) : M2C :=
  Complex.cosh (eps * v) • (1 : M2C) +
    (if v = 0 then eps else Complex.sinh (eps * v) / v) • octBoostGenerator v

/-- For nonzero `v`, the closed boost reduces to `cosh I + sinh σ₁`. -/
theorem octBoostClosed_nonzero {eps v : ℂ} (hv : v ≠ 0) :
    octBoostClosed eps v =
      Complex.cosh (eps * v) • (1 : M2C) + Complex.sinh (eps * v) • σ1 := by
  rw [octBoostClosed, if_neg hv, octBoostGenerator_eq]
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply]
  ring_nf
  field_simp [hv]

/-- Spin boost matrix `Λ(η)=cosh η I+sinh η σ₁`. -/
def spinBoost (η : ℂ) : M2C := Complex.cosh η • (1 : M2C) + Complex.sinh η • σ1

/-- The spin boost has determinant one. -/
theorem spinBoost_det (η : ℂ) : (spinBoost η).det = 1 := by
  simp [spinBoost, σ1, Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply]
  simpa [pow_two] using Complex.cosh_sq_sub_sinh_sq η

/-- Boost action `X ↦ ΛXΛ`. -/
def boostAction (η : ℂ) (X : M2C) : M2C := spinBoost η * X * spinBoost η

/-- Since `det Λ=1`, the boost action preserves the determinant. -/
theorem boostAction_preserves_det (η : ℂ) (X : M2C) :
    (boostAction η X).det = X.det := by
  unfold boostAction
  rw [Matrix.det_mul, Matrix.det_mul, spinBoost_det]
  simp

/-- Therefore the octonionic spacetime interval is boost invariant. -/
theorem boost_preserves_octonionic_interval (η t x y z : ℂ) :
    (boostAction η (octonionicSpacetime t x y z)).det = t^2 - x^2 - y^2 - z^2 := by
  rw [boostAction_preserves_det, octonionic_minkowski_interval]

/-- Main synthesis theorem. -/
theorem split_octonion_minkowski_synthesis :
    (∀ t x y z : ℂ, (octonionicSpacetime t x y z).det = t^2 - x^2 - y^2 - z^2) ∧
    (∀ v : ℂ, octBoostGenerator v * octBoostGenerator v = (v * v) • (1 : M2C)) ∧
    (∀ η : ℂ, (spinBoost η).det = 1) ∧
    (∀ η : ℂ, ∀ X : M2C, (boostAction η X).det = X.det) := by
  exact ⟨octonionic_minkowski_interval, octBoostGenerator_sq, spinBoost_det,
    boostAction_preserves_det⟩

#check oct_e1_sq
#check octonionicSpacetime_eq_minkowski
#check octonionic_minkowski_interval
#check octBoostGenerator_sq
#check octBoostClosed_nonzero
#check boost_preserves_octonionic_interval
#check split_octonion_minkowski_synthesis

end SplitOctonionMinkowski
