import Mathlib

open Matrix
open Complex

section TemperleyLieb

variable {F : Type*} [Field F]
variable (A : F)

/-- The Temperley-Lieb loop value -/
def d : F := - A^2 - (A⁻¹)^2

variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (e : ℕ → A_alg)

/-- Temperley-Lieb Algebra relations on generators e i -/
class TemperleyLieb (d_val : F) (e : ℕ → A_alg) : Prop where
  e_sq : ∀ i, e i * e i = d_val • e i
  e_comm : ∀ i j, i + 1 < j ∨ j + 1 < i → e i * e j = e j * e i
  e_adj : ∀ i j, (i = j + 1 ∨ j = i + 1) → e i * e j * e i = e i

variable [TemperleyLieb (d A) e]

/-- The Jones representation of the Braid Group generators -/
def σ (i : ℕ) : A_alg := (A:F) • (1:A_alg) + (A⁻¹:F) • e i

/-- Inverse of the Braid Group generators -/
def σ_inv (i : ℕ) : A_alg := (A⁻¹:F) • (1:A_alg) + (A:F) • e i

@[simp] lemma tl_smul_mul_smul_comm (c1 c2 : F) (x1 x2 : A_alg) : 
  (c1 • x1) * (c2 • x2) = (c1 * c2) • (x1 * x2) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

macro "tl_expand" : tactic => `(tactic| simp only [add_mul, mul_add, tl_smul_mul_smul_comm, add_assoc, one_mul, mul_one])
macro "abel_simp" : tactic => `(tactic| simp only [add_assoc, add_left_comm, add_comm])

lemma add_smul3 (c1 c2 c3 : F) (x : A_alg) : 
  c1 • x + c2 • x + c3 • x = (c1 + c2 + c3) • x := by
  rw [← add_smul, ← add_smul]

lemma add_smul4 (c1 c2 c3 c4 : F) (x : A_alg) : 
  c1 • x + c2 • x + c3 • x + c4 • x = (c1 + c2 + c3 + c4) • x := by
  rw [← add_smul, ← add_smul, ← add_smul]

-- Prove that σ and σ_inv are inverses
lemma sigma_mul_sigma_inv (i : ℕ) (hA : A ≠ 0) : σ A e i * σ_inv A e i = 1 := by
  dsimp [σ, σ_inv, d]
  calc
    ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) * ((A⁻¹:F) • (1:A_alg) + (A:F) • e i)
      = ((A * A⁻¹):F) • (1:A_alg) + ((A * A):F) • e i + (((A⁻¹ * A⁻¹):F) • e i + ((A⁻¹ * A):F) • (e i * e i)) := by tl_expand; abel_simp
    _ = (1:F) • (1:A_alg) + (A^2:F) • e i + (((A⁻¹)^2:F) • e i + (1:F) • (e i * e i)) := by
        have h1 : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
        have h2 : A⁻¹ * A = 1 := inv_mul_cancel₀ hA
        have h3 : A * A = A^2 := by ring
        have h4 : A⁻¹ * A⁻¹ = (A⁻¹)^2 := by ring
        rw [h1, h2, h3, h4]
    _ = (1:A_alg) + (A^2:F) • e i + (((A⁻¹)^2:F) • e i + ((- A^2 - (A⁻¹)^2):F) • e i) := by
        have h_sq : e i * e i = ((-A^2 - (A⁻¹)^2):F) • e i := TemperleyLieb.e_sq i
        rw [h_sq]
        simp only [one_smul]
    _ = (1:A_alg) + ((A^2:F) • e i + ((A⁻¹)^2:F) • e i + ((- A^2 - (A⁻¹)^2):F) • e i) := by abel_simp
    _ = (1:A_alg) + (A^2 + (A⁻¹)^2 + (- A^2 - (A⁻¹)^2)) • e i := by rw [add_smul3]
    _ = (1:A_alg) + (0:F) • e i := by
        congr 2
        ring
    _ = 1 := by rw [zero_smul, add_zero]

-- Prove far commutation
lemma braid_comm (i j : ℕ) (h : i + 1 < j ∨ j + 1 < i) : σ A e i * σ A e j = σ A e j * σ A e i := by
  dsimp [σ]
  calc
    ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e j)
      = ((A * A):F) • (1:A_alg) + ((A * A⁻¹):F) • e j + (((A⁻¹ * A):F) • e i + ((A⁻¹ * A⁻¹):F) • (e i * e j)) := by tl_expand; abel_simp
    _ = ((A * A):F) • (1:A_alg) + ((A * A⁻¹):F) • e j + (((A⁻¹ * A):F) • e i + ((A⁻¹ * A⁻¹):F) • (e j * e i)) := by
        have h_comm : e i * e j = e j * e i := TemperleyLieb.e_comm i j h
        rw [h_comm]
    _ = ((A * A):F) • (1:A_alg) + ((A⁻¹ * A):F) • e j + (((A * A⁻¹):F) • e i + ((A⁻¹ * A⁻¹):F) • (e j * e i)) := by
        have hc1 : A * A⁻¹ = A⁻¹ * A := by ring
        have hc2 : A⁻¹ * A = A * A⁻¹ := by ring
        nth_rw 1 [hc1]
        nth_rw 2 [hc2]
    _ = ((A * A):F) • (1:A_alg) + ((A * A⁻¹):F) • e i + (((A⁻¹ * A):F) • e j + ((A⁻¹ * A⁻¹):F) • (e j * e i)) := by abel_simp
    _ = ((A:F) • (1:A_alg) + (A⁻¹:F) • e j) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) := by tl_expand; abel_simp

end TemperleyLieb
