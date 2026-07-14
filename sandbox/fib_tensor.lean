import InfoGeometry.Categorical.FibonacciBraidedCategory
import InfoGeometry.Categorical.FibonacciHomSpace

open CategoryTheory Matrix InfoGeometry.Categorical InfoGeometry.Categorical.FibonacciHomSpace InfoGeometry.Categorical.FibonacciBraidedCategory

def blockDiag2 {α : Type} [Zero α] {m₁ n₁ m₂ n₂ : ℕ} (A : Matrix (Fin m₁) (Fin n₁) α) (B : Matrix (Fin m₂) (Fin n₂) α) :
  Matrix (Fin (m₁ + m₂)) (Fin (n₁ + n₂)) α :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

def blockDiag3 {α : Type} [Zero α] {m₁ n₁ m₂ n₂ m₃ n₃ : ℕ}
  (A : Matrix (Fin m₁) (Fin n₁) α) (B : Matrix (Fin m₂) (Fin n₂) α) (C : Matrix (Fin m₃) (Fin n₃) α) :
  Matrix (Fin (m₁ + m₂ + m₃)) (Fin (n₁ + n₂ + n₃)) α :=
  blockDiag2 (blockDiag2 A B) C

def kron {m₁ n₁ m₂ n₂ : ℕ} (A : Matrix (Fin m₁) (Fin n₁) ℂ) (B : Matrix (Fin m₂) (Fin n₂) ℂ) :
  Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kronecker A B)

def fibTensorHom {X₁ X₂ Y₁ Y₂ : FibCat} (f : FibHom X₁ X₂) (g : FibHom Y₁ Y₂) : FibHom (fibTensorObj X₁ Y₁) (fibTensorObj X₂ Y₂) where
  unit_comp := Matrix.reindex
    (Equiv.cast (by simp [fibTensorObj]))
    (Equiv.cast (by simp [fibTensorObj]))
    (blockDiag2 (kron f.unit_comp g.unit_comp) (kron f.tau_comp g.tau_comp))
  tau_comp := Matrix.reindex
    (Equiv.cast (by simp [fibTensorObj]))
    (Equiv.cast (by simp [fibTensorObj]))
    (blockDiag3 (kron f.unit_comp g.tau_comp) (kron f.tau_comp g.unit_comp) (kron f.tau_comp g.tau_comp))
