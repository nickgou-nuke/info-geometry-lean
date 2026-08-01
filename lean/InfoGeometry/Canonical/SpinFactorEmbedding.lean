import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Group.Basic
import InfoGeometry.Canonical.SplitGaugeGroup
import InfoGeometry.Algebra.SplitJordanSpinor

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.SplitJordanSpinor
open JordanMatrix2

variable (K A : Type*) [CommRing K] [NonAssocSemiring A] [SMul K A]
variable [SplitCompositionAlgebra K A]

/-- 
  1. Абстрактна 10D координатна реализация (Мостът)
  Изометрично вложение на JordanMatrix2 (експертното състояние в KAN)
  към 10D векторното пространство, където действа O(5,5).
-/
structure SpinFactorEmbedding where
  Phi : JordanMatrix2 K A → Matrix (Sum (Fin 5) (Fin 5)) (Fin 1) K
  
  -- Изометричното условие: Φ(X)ᵀ · η · Φ(X) = [det(X)]
  -- Детерминантата на 2x2 матрицата се превръща в квадратичната форма в 10D!
  isometry : ∀ X : JordanMatrix2 K A, 
    (Phi X).transpose * (splitMetric10D K) * (Phi X) = 
    (fun _ _ => JordanMatrix2.determinant X)

/--
  2. ТЕОРЕМА ЗА СИМЕТРИЯТА НА МАРШРУТИЗАЦИЯТА (Routing Symmetry Theorem)
  Ако експертното пространство е вложено изометрично, то всяко калибровочно 
  действие G ∈ O(5,5) запазва информационния Лагранжиан (детерминантата)!
  
  (Тъй като дефинирахме isO55Isometric като G * η * Gᵀ = η, ние прилагаме 
   ко-действието Gᵀ към вектора, за да получим елегантно и строго доказателство.)
-/
theorem transpose_o55_preserves_spin_factor_determinant 
    (emb : SpinFactorEmbedding K A)
    (G : Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) K)
    (hG : isO55Isometric K G)
    (X : JordanMatrix2 K A) :
    ((G.transpose * emb.Phi X).transpose * (splitMetric10D K) * (G.transpose * emb.Phi X)) = 
    (fun _ _ => JordanMatrix2.determinant X) := by
  dsimp [isO55Isometric] at hG
  rw [Matrix.transpose_mul]
  rw [Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  -- LHS: Φᵀ * (G * (η * (Gᵀ * Φ)))
  rw [← Matrix.mul_assoc (splitMetric10D K) G.transpose (emb.Phi X)]
  -- LHS: Φᵀ * (G * ((η * Gᵀ) * Φ))
  rw [← Matrix.mul_assoc G (splitMetric10D K * G.transpose) (emb.Phi X)]
  -- LHS: Φᵀ * ((G * (η * Gᵀ)) * Φ)
  rw [← Matrix.mul_assoc G (splitMetric10D K) G.transpose]
  -- LHS: Φᵀ * (((G * η) * Gᵀ) * Φ)
  rw [hG]
  -- LHS: Φᵀ * (η * Φ)
  rw [← Matrix.mul_assoc]
  -- LHS: (Φᵀ * η) * Φ
  rw [emb.isometry X]

end InfoGeometry.Canonical
