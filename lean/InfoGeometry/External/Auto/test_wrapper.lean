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
  have hTL : TemperleyLieb (d A) e := inferInstance
  rw [σ, σ_inv]
  simp only [add_mul, mul_add, tl_smul_mul_smul_comm, one_mul, mul_one, add_assoc]
  rw [hTL.e_sq]
  have hcoeff : A⁻¹ * A⁻¹ + (A * A) + (-A ^ 2 - (A ^ 2)⁻¹) = 0 := by
    field_simp [hA]
    ring
  rw [mul_inv_cancel₀ hA, inv_mul_cancel₀ hA]
  simp only [one_smul]
  have hsum : ((A⁻¹ * A⁻¹) • e i + ((A * A) • e i + d A • e i)) = 0 := by
    simpa [d, add_smul, add_assoc, add_left_comm, add_comm] using
      congrArg (fun c : F => c • e i) hcoeff
  rw [hsum]
  simp

-- Prove far commutation
lemma braid_comm (i j : ℕ) (h : i + 1 < j ∨ j + 1 < i) : σ A e i * σ A e j = σ A e j * σ A e i := by
  by_cases hA : A = 0
  · subst hA
    simp [σ]
  · rw [σ, σ]
    simp only [add_mul, mul_add, tl_smul_mul_smul_comm, one_mul, mul_one, add_assoc]
    rw [TemperleyLieb.e_comm (d_val := d A) (e := e) i j h]
    have hAAinv : (A : F) * A⁻¹ = 1 := mul_inv_cancel₀ hA
    have hAinvA : (A : F)⁻¹ * A = 1 := inv_mul_cancel₀ hA
    simp [hAAinv, hAinvA, add_comm, add_left_comm, add_assoc]

end TemperleyLieb
