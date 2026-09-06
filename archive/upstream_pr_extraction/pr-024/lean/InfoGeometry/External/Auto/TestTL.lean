import Mathlib

open Matrix
open Complex

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

lemma TL_e_sq (i : ℕ) : e i * e i = (d A) • e i := by
  simpa using (TemperleyLieb.e_sq (d_val := d A) (e := e) i)
lemma TL_e_comm (A : F) (e : ℕ → A_alg) [TemperleyLieb (d A) e]
    (i j : ℕ) (h : i + 1 < j ∨ j + 1 < i) : e i * e j = e j * e i := by
  have inst := ‹TemperleyLieb (d A) e›
  exact inst.e_comm i j h
lemma TL_e_adj (A : F) (e : ℕ → A_alg) [TemperleyLieb (d A) e]
    (i j : ℕ) (h : i = j + 1 ∨ j = i + 1) : e i * e j * e i = e i := by
  have inst := ‹TemperleyLieb (d A) e›
  exact inst.e_adj i j h

def σ (i : ℕ) : A_alg := (A:F) • (1:A_alg) + (A⁻¹:F) • e i
def σ_inv (i : ℕ) : A_alg := (A⁻¹:F) • (1:A_alg) + (A:F) • e i

@[simp] lemma tl_smul_mul_smul_comm (c1 c2 : F) (x1 x2 : A_alg) : 
  (c1 • x1) * (c2 • x2) = (c1 * c2) • (x1 * x2) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

lemma add_smul3 (c1 c2 c3 : F) (x : A_alg) : 
  c1 • x + c2 • x + c3 • x = (c1 + c2 + c3) • x := by
  rw [add_smul, add_smul]

lemma add_smul4 (c1 c2 c3 c4 : F) (x : A_alg) : 
  c1 • x + (c2 • x + (c3 • x + c4 • x)) = (c1 + c2 + c3 + c4) • x := by
  rw [add_smul, add_smul, add_smul, add_assoc, add_assoc]

lemma sigma_mul_sigma_inv (i : ℕ) (hA : A ≠ 0) : σ A e i * σ_inv A e i = 1 := by
  dsimp [σ, σ_inv]
  have h1 : ((A:F) • (1:A_alg)) * ((A⁻¹:F) • (1:A_alg)) = (1:A_alg) := by
    rw [tl_smul_mul_smul_comm]
    simp [mul_inv_cancel₀ hA]
  have h2 : ((A:F) • (1:A_alg)) * ((A:F) • e i) = (A^2:F) • e i := by
    rw [tl_smul_mul_smul_comm]
    simp [sq]
  have h3 : ((A⁻¹:F) • e i) * ((A⁻¹:F) • (1:A_alg)) = ((A⁻¹)^2:F) • e i := by
    rw [tl_smul_mul_smul_comm]
    simp [sq]
  have h4 : ((A⁻¹:F) • e i) * ((A:F) • e i) = (1:F) • (e i * e i) := by
    rw [tl_smul_mul_smul_comm, inv_mul_cancel₀ hA]
  rw [add_mul, mul_add, mul_add]
  rw [h1, h2, h3, h4]
  rw [TL_e_sq A e i]
  have h_smul_smul : (1:F) • ((d A) • e i) = (d A) • e i := by rw [smul_smul, one_mul]
  rw [h_smul_smul]
  have h_sum : (A^2:F) • e i + ((A⁻¹)^2:F) • e i + (d A) • e i = 0 := by
    rw [← add_smul, ← add_smul]
    have hz : A^2 + (A⁻¹)^2 + d A = 0 := by
      dsimp [d]
      ring
    rw [hz, zero_smul]
  simpa [add_assoc] using congrArg (fun x : A_alg => (1 : A_alg) + x) h_sum

end TemperleyLieb
