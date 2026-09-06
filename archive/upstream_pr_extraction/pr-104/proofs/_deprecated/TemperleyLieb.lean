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

lemma add_smul3 (c1 c2 c3 : F) (x : A_alg) : 
  c1 • x + c2 • x + c3 • x = (c1 + c2 + c3) • x := by
  rw [add_smul, add_smul]

lemma add_smul4 (c1 c2 c3 c4 : F) (x : A_alg) : 
  c1 • x + (c2 • x + (c3 • x + c4 • x)) = (c1 + c2 + c3 + c4) • x := by
  rw [add_smul, add_smul, add_smul, add_assoc, add_assoc]

-- Prove that σ and σ_inv are inverses
lemma sigma_mul_sigma_inv (i : ℕ) (hA : A ≠ 0) : σ A e i * σ_inv A e i = 1 := by
  dsimp [σ, σ_inv]
  have h1 : ((A:F) • (1:A_alg)) * ((A⁻¹:F) • (1:A_alg)) = (1:F) • (1:A_alg) := by
    calc
      ((A:F) • (1:A_alg)) * ((A⁻¹:F) • (1:A_alg)) = (A * A⁻¹) • (1 * 1 : A_alg) := tl_smul_mul_smul_comm A A⁻¹ 1 1
      _ = (1:F) • (1:A_alg) := by rw [mul_inv_cancel₀ hA, mul_one]
  have h2 : ((A:F) • (1:A_alg)) * ((A:F) • e i) = (A^2:F) • e i := by
    calc
      ((A:F) • (1:A_alg)) * ((A:F) • e i) = (A * A) • (1 * e i) := tl_smul_mul_smul_comm A A 1 (e i)
      _ = (A^2:F) • e i := by rw [sq, one_mul]
  have h3 : ((A⁻¹:F) • e i) * ((A⁻¹:F) • (1:A_alg)) = ((A⁻¹)^2:F) • e i := by
    calc
      ((A⁻¹:F) • e i) * ((A⁻¹:F) • (1:A_alg)) = (A⁻¹ * A⁻¹) • (e i * 1) := tl_smul_mul_smul_comm A⁻¹ A⁻¹ (e i) 1
      _ = ((A⁻¹)^2:F) • e i := by rw [sq, mul_one]
  have h4 : ((A⁻¹:F) • e i) * ((A:F) • e i) = (1:F) • (e i * e i) := by
    calc
      ((A⁻¹:F) • e i) * ((A:F) • e i) = (A⁻¹ * A) • (e i * e i) := tl_smul_mul_smul_comm A⁻¹ A (e i) (e i)
      _ = (1:F) • (e i * e i) := by rw [inv_mul_cancel₀ hA]
  rw [add_mul, mul_add, mul_add]
  rw [h1, h2, h3, h4]
  have h_sq : e i * e i = (d A) • e i := TemperleyLieb.e_sq (d_val := d A) (e := e) i
  rw [h_sq]
  have h_one_smul : (1:F) • (1:A_alg) = 1 := one_smul _ _
  rw [h_one_smul]
  have h_smul_smul : (1:F) • ((d A) • e i) = (d A) • e i := by rw [smul_smul, one_mul]
  rw [h_smul_smul]
  have h_sum : (A^2:F) • e i + ((A⁻¹)^2:F) • e i + (d A) • e i = 0 := by
    rw [← add_smul, ← add_smul]
    have hz : A^2 + (A⁻¹)^2 + d A = 0 := by dsimp [d]; ring
    rw [hz, zero_smul]
  have h_assoc2 : 1 + (A^2:F) • e i + ((A⁻¹)^2:F) • e i + (d A) • e i = 1 + ((A^2:F) • e i + ((A⁻¹)^2:F) • e i + (d A) • e i) := by abel
  calc
    1 + (A ^ 2) • e i + ((A⁻¹) ^ 2 • e i + d A • e i) = 1 + (A^2:F) • e i + ((A⁻¹)^2:F) • e i + (d A) • e i := by abel
    _ = 1 + ((A^2:F) • e i + ((A⁻¹)^2:F) • e i + (d A) • e i) := h_assoc2
    _ = 1 + 0 := by rw [h_sum]
    _ = 1 := add_zero 1

-- Prove far commutation
lemma braid_comm (i j : ℕ) (h : i + 1 < j ∨ j + 1 < i) : σ A e i * σ A e j = σ A e j * σ A e i := by
  dsimp [σ]
  have h1 : ((A⁻¹:F) • e i) * ((A⁻¹:F) • e j) = ((A⁻¹:F) • e j) * ((A⁻¹:F) • e i) := by
    calc
      ((A⁻¹:F) • e i) * ((A⁻¹:F) • e j) = (A⁻¹ * A⁻¹) • (e i * e j) := tl_smul_mul_smul_comm A⁻¹ A⁻¹ (e i) (e j)
      _ = (A⁻¹ * A⁻¹) • (e j * e i) := by rw [TemperleyLieb.e_comm (d_val := d A) (e := e) i j h]
      _ = ((A⁻¹:F) • e j) * ((A⁻¹:F) • e i) := (tl_smul_mul_smul_comm A⁻¹ A⁻¹ (e j) (e i)).symm
  have h2 : ((A:F) • (1:A_alg)) * ((A⁻¹:F) • e j) = ((A⁻¹:F) • e j) * ((A:F) • (1:A_alg)) := by
    calc
      ((A:F) • (1:A_alg)) * ((A⁻¹:F) • e j) = (A * A⁻¹) • (1 * e j) := tl_smul_mul_smul_comm A A⁻¹ 1 (e j)
      _ = (A⁻¹ * A) • (e j * 1) := by rw [mul_comm A A⁻¹, one_mul, mul_one]
      _ = ((A⁻¹:F) • e j) * ((A:F) • (1:A_alg)) := (tl_smul_mul_smul_comm A⁻¹ A (e j) 1).symm
  have h3 : ((A⁻¹:F) • e i) * ((A:F) • (1:A_alg)) = ((A:F) • (1:A_alg)) * ((A⁻¹:F) • e i) := by
    calc
      ((A⁻¹:F) • e i) * ((A:F) • (1:A_alg)) = (A⁻¹ * A) • (e i * 1) := tl_smul_mul_smul_comm A⁻¹ A (e i) 1
      _ = (A * A⁻¹) • (1 * e i) := by rw [mul_comm A⁻¹ A, mul_one, one_mul]
      _ = ((A:F) • (1:A_alg)) * ((A⁻¹:F) • e i) := (tl_smul_mul_smul_comm A A⁻¹ 1 (e i)).symm
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add]
  rw [h1, h2, h3]
  abel

lemma TL_coef_reduce (hA : A ≠ 0) : A + A + A⁻¹ * (d A) + A⁻¹^3 = A := by
  dsimp [d]
  have h1 : A⁻¹ * (-A^2 - (A⁻¹)^2) = -A - A⁻¹^3 := by
    calc
      A⁻¹ * (-A^2 - (A⁻¹)^2) = -A⁻¹ * A^2 - A⁻¹ * (A⁻¹)^2 := by ring
      _ = - (A⁻¹ * A) * A - A⁻¹^3 := by ring
      _ = - 1 * A - A⁻¹^3 := by rw [inv_mul_cancel₀ hA]
      _ = -A - A⁻¹^3 := by ring
  rw [h1]
  ring

lemma hc1 : A * A * A = A^3 := by ring
lemma hc2 (hA : A ≠ 0) : A * A * A⁻¹ = A := by field_simp [hA]
lemma hc3 (hA : A ≠ 0) : A * A⁻¹ * A = A := by field_simp [hA]
lemma hc4 (hA : A ≠ 0) : A * A⁻¹ * A⁻¹ = A⁻¹ := by field_simp [hA]
lemma hc5 (hA : A ≠ 0) : A⁻¹ * A * A = A := by field_simp [hA]
lemma hc6 (hA : A ≠ 0) : A⁻¹ * A * A⁻¹ = A⁻¹ := by field_simp [hA]
lemma hc7 (hA : A ≠ 0) : A⁻¹ * A⁻¹ * A = A⁻¹ := by field_simp [hA]
lemma hc8 : A⁻¹ * A⁻¹ * A⁻¹ = A⁻¹^3 := by ring

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
    ((A:F) • 1 + (A⁻¹:F) • e i) * ((A:F) • 1 + (A⁻¹:F) • e j) * ((A:F) • 1 + (A⁻¹:F) • e i)
      = (A * A * A) • 1 + (A⁻¹ * A * A) • e i + ((A * A⁻¹ * A) • e j + (A⁻¹ * A⁻¹ * A) • (e i * e j)) +
        ((A * A * A⁻¹) • e i + (A⁻¹ * A * A⁻¹) • (e i * e i) +
        ((A * A⁻¹ * A⁻¹) • (e j * e i) + (A⁻¹ * A⁻¹ * A⁻¹) • (e i * e j * e i))) := by
      simp only [mul_add, add_mul, tl_smul_mul_smul_comm, mul_one, one_mul]
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

-- Prove the Braid Relation for adjacent generators
lemma braid_adj (i j : ℕ) (h : i = j + 1 ∨ j = i + 1) (hA : A ≠ 0) : 
  σ A e i * σ A e j * σ A e i = σ A e j * σ A e i * σ A e j := by
  have h_left : σ A e i * σ A e j * σ A e i = σ_adj_nf A e i j := braid_adj_left A e i j h hA
  have h_symm : j = i + 1 ∨ i = j + 1 := Or.symm h
  have h_right : σ A e j * σ A e i * σ A e j = σ_adj_nf A e j i := braid_adj_left A e j i h_symm hA
  have h_nf_eq : σ_adj_nf A e i j = σ_adj_nf A e j i := by dsimp [σ_adj_nf]; abel
  rw [h_left, h_right, h_nf_eq]

end TemperleyLieb
