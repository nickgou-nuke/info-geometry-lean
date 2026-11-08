import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix
open Complex

namespace TestBraid

section TemperleyLieb

variable {F : Type*} [Field F]
variable (A : F)

def d : F := - A^2 - (A⁻¹)^2

variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (e : ℕ → A_alg)

class TemperleyLieb (d_val : F) (e : ℕ → A_alg) : Prop where
  e_sq : ∀ i, e i * e i = d_val • e i
  e_comm : ∀ i j, i + 1 < j ∨ j + 1 < i → e i * e j = e j * e i
  e_adj : ∀ i j, (i = j + 1 ∨ j = i + 1) → e i * e j * e i = e i

variable [TemperleyLieb (d A) e]

def σ (i : ℕ) : A_alg := (A:F) • (1:A_alg) + (A⁻¹:F) • e i
def σ_inv (i : ℕ) : A_alg := (A⁻¹:F) • (1:A_alg) + (A:F) • e i

@[simp] lemma tl_smul_mul_smul_comm (c1 c2 : F) (x1 x2 : A_alg) : 
  (c1 • x1) * (c2 • x2) = (c1 * c2) • (x1 * x2) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

-- We define a normal form for the expansion of σ i * σ j * σ i
def σ_adj_nf (i j : ℕ) : A_alg :=
  (A^3:F) • (1:A_alg) + (A:F) • e i + (A:F) • e j + (A⁻¹:F) • (e i * e j) + (A⁻¹:F) • (e j * e i)

lemma braid_adj_left (i j : ℕ) (h : i = j + 1 ∨ j = i + 1) (hA : A ≠ 0) : 
  σ A e i * σ A e j * σ A e i = σ_adj_nf A e i j := by
  dsimp [σ, σ_adj_nf]
  have h_sq : e i * e i = (d A) • e i := TemperleyLieb.e_sq (d_val := d A) (e := e) i
  have h_adj : e i * e j * e i = e i := TemperleyLieb.e_adj (d_val := d A) (e := e) i j h
  have hc1 : A * A * A = A^3 := by ring
  have hc2 : A * A * A⁻¹ = A := by field_simp [hA]
  have hc3 : A * A⁻¹ * A = A := by field_simp [hA]
  have hc4 : A * A⁻¹ * A⁻¹ = A⁻¹ := by field_simp [hA]
  have hc5 : A⁻¹ * A * A = A := by field_simp [hA]
  have hc6 : A⁻¹ * A * A⁻¹ = A⁻¹ := by field_simp [hA]
  have hc7 : A⁻¹ * A⁻¹ * A = A⁻¹ := by field_simp [hA]
  have hc8 : A⁻¹ * A⁻¹ * A⁻¹ = A⁻¹^3 := by ring
  have h_reduce : A + A + A⁻¹ * (d A) + A⁻¹^3 = A := by
    have h1 : A⁻¹ * (-A^2 - (A⁻¹)^2) = -A - A⁻¹^3 := by
      calc
        A⁻¹ * (-A^2 - (A⁻¹)^2) = - (A⁻¹ * A) * A - A⁻¹^3 := by ring
        _ = - 1 * A - A⁻¹^3 := by rw [inv_mul_cancel₀ hA]
        _ = -A - A⁻¹^3 := by ring
    dsimp [d]
    rw [h1]
    ring
  have h_group : A^3 • 1 + A • e i + (A • e j + A⁻¹ • (e i * e j)) +
        (A • e i + (A⁻¹ * d A) • e i +
        (A⁻¹ • (e j * e i) + A⁻¹^3 • e i)) =
      A^3 • 1 + (A • e i + A • e i + (A⁻¹ * d A) • e i + A⁻¹^3 • e i) + A • e j + A⁻¹ • (e i * e j) + A⁻¹ • (e j * e i) := by abel
  have h_smul : (A • e i + A • e i + (A⁻¹ * d A) • e i + A⁻¹^3 • e i) = (A + A + A⁻¹ * d A + A⁻¹^3) • e i := by
    rw [add_smul, add_smul, add_smul]
  calc
    σ A e i * σ A e j * σ A e i
      = (A * A * A) • 1 + (A⁻¹ * A * A) • e i + ((A * A⁻¹ * A) • e j + (A⁻¹ * A⁻¹ * A) • (e i * e j)) +
        ((A * A * A⁻¹) • e i + (A⁻¹ * A * A⁻¹) • (e i * e i) +
        ((A * A⁻¹ * A⁻¹) • (e j * e i) + (A⁻¹ * A⁻¹ * A⁻¹) • (e i * e j * e i))) := by
      simp only [σ, mul_add, add_mul, tl_smul_mul_smul_comm, mul_one, one_mul]
    _ = A^3 • 1 + A • e i + (A • e j + A⁻¹ • (e i * e j)) +
        (A • e i + A⁻¹ • (e i * e i) +
        (A⁻¹ • (e j * e i) + A⁻¹^3 • (e i * e j * e i))) := by
      rw [hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8]
    _ = A^3 • 1 + A • e i + (A • e j + A⁻¹ • (e i * e j)) +
        (A • e i + A⁻¹ • ((d A) • e i) +
        (A⁻¹ • (e j * e i) + A⁻¹^3 • e i)) := by
      rw [h_sq, h_adj]
    _ = A^3 • 1 + A • e i + (A • e j + A⁻¹ • (e i * e j)) +
        (A • e i + (A⁻¹ * d A) • e i +
        (A⁻¹ • (e j * e i) + A⁻¹^3 • e i)) := by
      rw [smul_smul]
    _ = A^3 • 1 + (A • e i + A • e i + (A⁻¹ * d A) • e i + A⁻¹^3 • e i) + A • e j + A⁻¹ • (e i * e j) + A⁻¹ • (e j * e i) := h_group
    _ = A^3 • 1 + (A + A + A⁻¹ * d A + A⁻¹^3) • e i + A • e j + A⁻¹ • (e i * e j) + A⁻¹ • (e j * e i) := by rw [h_smul]
    _ = A^3 • 1 + A • e i + A • e j + A⁻¹ • (e i * e j) + A⁻¹ • (e j * e i) := by rw [h_reduce]
    _ = σ_adj_nf A e i j := rfl

end TemperleyLieb

end TestBraid
