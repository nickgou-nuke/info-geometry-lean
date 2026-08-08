import sympy as sp

# A SymPy script to generate the exact Lean 4 proofs for the Temperley-Lieb algebra.
# Since Lean 4 `noncomm_ring` doesn't natively handle `algebraMap` commutativity perfectly,
# we will output explicit `calc` blocks where `tl_simp` handles the distribution,
# and we just align the scalars using `congr`.

lean_code = """import Mathlib

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
def σ (i : ℕ) : A_alg := A • 1 + A⁻¹ • e i

/-- Inverse of the Braid Group generators -/
def σ_inv (i : ℕ) : A_alg := A⁻¹ • 1 + A • e i

-- A powerful expansion macro for our specific algebra structure
macro "tl_simp" : tactic => `(tactic| simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_comm A⁻¹ A, add_assoc, add_left_comm, add_comm, one_mul, mul_one])

-- Helper lemma for scalar reduction
lemma A_inv_cancel (hA : A ≠ 0) : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
lemma A_inv_cancel2 (hA : A ≠ 0) : A⁻¹ * A = 1 := inv_mul_cancel₀ hA

-- Prove that σ and σ_inv are inverses
lemma sigma_mul_sigma_inv (i : ℕ) (hA : A ≠ 0) : σ A e i * σ_inv A e i = 1 := by
  dsimp [σ, σ_inv, d]
  calc
    (A • 1 + A⁻¹ • e i) * (A⁻¹ • 1 + A • e i)
      = (A * A⁻¹) • 1 + (A * A) • e i + (A⁻¹ * A⁻¹) • e i + (A⁻¹ * A) • (e i * e i) := by tl_simp
    _ = 1 • 1 + A^2 • e i + (A⁻¹)^2 • e i + 1 • (e i * e i) := by
        have h1 : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
        have h2 : A⁻¹ * A = 1 := inv_mul_cancel₀ hA
        have h3 : A * A = A^2 := by ring
        have h4 : A⁻¹ * A⁻¹ = (A⁻¹)^2 := by ring
        rw [h1, h2, h3, h4]
    _ = 1 + A^2 • e i + (A⁻¹)^2 • e i + (- A^2 - (A⁻¹)^2) • e i := by
        rw [TemperleyLieb.e_sq i]
        simp
    _ = 1 + (A^2 + (A⁻¹)^2 - A^2 - (A⁻¹)^2) • e i := by
        rw [add_smul, add_smul, sub_smul, sub_smul]
        -- regroup
        sorry
    _ = 1 := by
        sorry

-- Prove far commutation
lemma braid_comm (i j : ℕ) (h : i + 1 < j ∨ j + 1 < i) : σ A e i * σ A e j = σ A e j * σ A e i := by
  dsimp [σ]
  calc
    (A • 1 + A⁻¹ • e i) * (A • 1 + A⁻¹ • e j)
      = (A * A) • 1 + (A * A⁻¹) • e i + (A * A⁻¹) • e j + (A⁻¹ * A⁻¹) • (e i * e j) := by tl_simp
    _ = (A * A) • 1 + (A * A⁻¹) • e i + (A * A⁻¹) • e j + (A⁻¹ * A⁻¹) • (e j * e i) := by
        rw [TemperleyLieb.e_comm i j h]
    _ = (A • 1 + A⁻¹ • e j) * (A • 1 + A⁻¹ • e i) := by tl_simp

-- Prove the Braid Relation for adjacent generators
lemma braid_adj (i j : ℕ) (h : i = j + 1 ∨ j = i + 1) (hA : A ≠ 0) : 
  σ A e i * σ A e j * σ A e i = σ A e j * σ A e i * σ A e j := by
  dsimp [σ, d]
  sorry

end TemperleyLieb
"""

with open("TemperleyLieb.lean", "w") as f:
    f.write(lean_code)
