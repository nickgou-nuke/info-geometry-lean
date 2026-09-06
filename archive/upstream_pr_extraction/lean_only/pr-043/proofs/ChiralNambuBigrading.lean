import Mathlib

/-!
# Independent chiral/Nambu bi-grading

This owner records two independent involutive gradings on
`ℂ²_chiral ⊗ ℂ²_Nambu ⊗ ℂ³_family`. It does not identify relativistic
chirality with BdG chiral symmetry.
-/

noncomputable section
namespace ChiralNambuBigrading

abbrev NambuIndex := Fin 2 × Fin 2 × Fin 3
abbrev M12C := Matrix NambuIndex NambuIndex ℂ

def gammaChi : M12C :=
  Matrix.diagonal (fun i => if i.1 = 0 then (1 : ℂ) else -1)

def gammaNambu : M12C :=
  Matrix.diagonal (fun i => if i.2.1 = 0 then (1 : ℂ) else -1)

@[simp] theorem gammaChi_sq : gammaChi * gammaChi = (1 : M12C) := by
  dsimp [gammaChi]
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    by_cases h0 : i.1 = 0 <;> simp [Matrix.diagonal, h0]
  · simp [Matrix.diagonal, h]

@[simp] theorem gammaNambu_sq : gammaNambu * gammaNambu = (1 : M12C) := by
  dsimp [gammaNambu]
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    by_cases h0 : i.2.1 = 0 <;> simp [Matrix.diagonal, h0]
  · simp [Matrix.diagonal, h]

@[simp] theorem gammaChi_gammaNambu_commute :
    gammaChi * gammaNambu = gammaNambu * gammaChi := by
  dsimp [gammaChi, gammaNambu]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal, mul_comm]

def ChiralParity (A : M12C) (ε : Fin 2) : Prop :=
  gammaChi * A * gammaChi = (if ε = 0 then A else -A)

def NambuParity (A : M12C) (ε : Fin 2) : Prop :=
  gammaNambu * A * gammaNambu = (if ε = 0 then A else -A)

def Bidegree (A : M12C) (εχ εN : Fin 2) : Prop :=
  ChiralParity A εχ ∧ NambuParity A εN

end ChiralNambuBigrading
end noncomputable section
