import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
abbrev SpinFactorEmbedding :=
  {Phi : JordanMatrix2 K A → Matrix (Sum (Fin 5) (Fin 5)) (Fin 1) K //
    ∀ X : JordanMatrix2 K A,
      (Phi X).transpose * (splitMetric10D K) * (Phi X) =
        (fun _ _ => JordanMatrix2.determinant X)}

def Phi {K A : Type*} [CommRing K] [NonAssocSemiring A] [SMul K A]
    [SplitCompositionAlgebra K A] (emb : SpinFactorEmbedding K A) :
    JordanMatrix2 K A → Matrix (Sum (Fin 5) (Fin 5)) (Fin 1) K :=
  emb.1

theorem isometry {K A : Type*} [CommRing K] [NonAssocSemiring A] [SMul K A]
    [SplitCompositionAlgebra K A]
    (emb : SpinFactorEmbedding K A) (X : JordanMatrix2 K A) :
    (Phi emb X).transpose * (splitMetric10D K) * (Phi emb X) =
      (fun _ _ => JordanMatrix2.determinant X) :=
  emb.2 X

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
    ((G.transpose * Phi emb X).transpose * (splitMetric10D K) *
      (G.transpose * Phi emb X)) =
    (fun _ _ => JordanMatrix2.determinant X) := by
  have hleft :
      (G.transpose * Phi emb X).transpose * (splitMetric10D K) *
          (G.transpose * Phi emb X) =
        (Phi emb X).transpose * (G * splitMetric10D K * G.transpose) * Phi emb X := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hconj :
      (Phi emb X).transpose * (G * splitMetric10D K * G.transpose) * Phi emb X =
        (fun _ _ => JordanMatrix2.determinant X) := by
    calc
      (Phi emb X).transpose * (G * splitMetric10D K * G.transpose) * Phi emb X
          = (Phi emb X).transpose * (splitMetric10D K) * Phi emb X := by
              simpa [Matrix.mul_assoc] using
                congrArg (fun M => (Phi emb X).transpose * M * Phi emb X) hG
      _ = (fun _ _ => JordanMatrix2.determinant X) := isometry emb X
  exact hleft.trans hconj

end InfoGeometry.Canonical
