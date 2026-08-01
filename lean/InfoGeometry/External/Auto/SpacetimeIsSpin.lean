import Mathlib.Tactic

/-!
# Spacetime is spin

A Minkowski 4-vector is equivalently a `2×2` Hermitian Pauli matrix

`X = t I + x σ₁ + y σ₂ + z σ₃`.

The trace is `2t`, the determinant is the Minkowski quadratic form, the
characteristic polynomial gives lightcone coordinates, and pure spinor outer
products are null (`det=0`).
-/

noncomputable section

namespace SpacetimeIsSpin

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli matrices. -/
def σ1 : M2C := !![0, 1; 1, 0]
def σ2 : M2C := !![0, -Complex.I; Complex.I, 0]
def σ3 : M2C := !![1, 0; 0, -1]

/-- Pauli encoding of a spacetime vector. -/
def Xst (t x y z : ℂ) : M2C := t • (1 : M2C) + x • σ1 + y • σ2 + z • σ3

/-- The explicit matrix form. -/
theorem Xst_entries (t x y z : ℂ) :
    Xst t x y z = !![t + z, x - Complex.I * y; x + Complex.I * y, t - z] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Xst, σ1, σ2, σ3, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply] <;> ring

/-- Manual `2×2` trace. -/
def tr2 (A : M2C) : ℂ := A 0 0 + A 1 1

/-- Trace is twice time. -/
theorem Xst_trace (t x y z : ℂ) : tr2 (Xst t x y z) = 2 * t := by
  rw [Xst_entries]
  simp [tr2]
  ring

/-- Determinant is the Minkowski metric. -/
theorem Xst_det (t x y z : ℂ) :
    (Xst t x y z).det = t^2 - x^2 - y^2 - z^2 := by
  rw [Xst_entries]
  simp [Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Characteristic determinant: lightcone eigenvalue equation. -/
theorem Xst_char_det (lam t x y z : ℂ) :
    ((lam • (1 : M2C)) - Xst t x y z).det = (lam - t)^2 - (x^2 + y^2 + z^2) := by
  rw [Xst_entries]
  simp [Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Algebraic transpose-conjugation determinant law.  For `det L=1`, determinant is preserved. -/
theorem det_congruence (L X : M2C) : (L * X * Lᵀ).det = L.det^2 * X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Pure spinor outer product. -/
def spinorOuter (a b : ℂ) : M2C := !![a*a, a*b; b*a, b*b]

/-- A pure spinor outer product is null. -/
theorem spinorOuter_det_zero (a b : ℂ) : (spinorOuter a b).det = 0 := by
  simp [spinorOuter, Matrix.det_fin_two]
  ring

end SpacetimeIsSpin
