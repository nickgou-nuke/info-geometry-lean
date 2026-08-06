import Mathlib.Algebra.Group.Defs
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Riemannian.ConeAction

namespace InfoGeometry.Riemannian

open InfoGeometry.Clifford.Hestenes
open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/-- Дефиниране на следата на произволен паравектор като неговата скаларна част (grade 0). -/
def hTrace (X : ClPlus Q) : R :=
  sorry

/-- Фундаментално свойство: Clifford следата (grade 0) е циклично инвариантна. -/
theorem hTrace_mul_comm (A B : ClPlus Q) : hTrace Q (A * B) = hTrace Q (B * A) :=
  sorry

/-- Връзка с полярната форма (Polar Form / Билинейната форма на Q) за чисти вектори.
    Ако V1 и V2 са обикновени вектори (grade 1), техният hTrace е точно polar Q. -/
theorem hTrace_vect_eq_polar (u v : M) :
    hTrace Q ⟨ι Q u * ι Q v, sorry⟩ = QuadraticMap.polar Q u v := by
  sorry

/-- Обратен елемент в четната алгебра. -/
def clInv (S : ClPlus Q) [Invertible S.val] : ClPlus Q :=
  ⟨⅟(S.val), sorry⟩

/-- Дефиниция на Римановата метрика на Картан (Fisher Information Metric). -/
def cartanMetric (S : ClPlus Q) [Invertible S.val] (V1 V2 : ClPlus Q) : R :=
  hTrace Q (clInv Q S * V1 * clInv Q S * V2)

/-- Свойство на инверсията при анти-автоморфизма hestenesAdjoint. -/
axiom hestenesAdjoint_inv (G : ClPlus Q) [Invertible G.val] [Invertible (hestenesAdjoint Q v0 G).val] :
  hestenesAdjoint Q v0 (clInv Q G) = clInv Q (hestenesAdjoint Q v0 G)

/-- Основна теорема: Инвариантност на метриката на Картан под coneConjugationAction. -/
theorem cartanMetric_invariance (G : ClPlus Q) [Invertible G.val] [Invertible (hestenesAdjoint Q v0 G).val]
    (S : ClPlus Q) [Invertible S.val] 
    (V1 V2 : ClPlus Q) :
    haveI h1 : Invertible (S.val * (hestenesAdjoint Q v0 G).val) := Invertible.mul inferInstance inferInstance
    haveI h2 : Invertible (coneConjugationAction Q v0 G S).val := by
      dsimp [coneConjugationAction, L_action, R_action]
      exact Invertible.mul inferInstance h1 
    cartanMetric Q (coneConjugationAction Q v0 G S) (coneConjugationAction Q v0 G V1) (coneConjugationAction Q v0 G V2) = 
    cartanMetric Q S V1 V2 := by
  sorry

end InfoGeometry.Riemannian
