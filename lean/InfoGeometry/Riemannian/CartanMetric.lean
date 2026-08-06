import Mathlib.Algebra.Group.Defs
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Riemannian.ConeAction

namespace InfoGeometry.Riemannian

open InfoGeometry.Clifford.Hestenes
open CliffordAlgebra

variable {R : Type*} [Field R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/-- Дефиниране на следата (скаларната част) на Clifford елемент. -/
def clTrace (X : ClPlus Q) : R :=
  -- Абстрактна дефиниция на проекцията върху скаларите
  sorry

/-- Лемма за циклична инвариантност на Clifford следата. -/
axiom clTrace_mul_comm (A B : ClPlus Q) : clTrace Q (A * B) = clTrace Q (B * A)

/-- Обратен елемент в четната алгебра. -/
def clInv (S : ClPlus Q) [Invertible S.val] : ClPlus Q :=
  ⟨⅟(S.val), sorry⟩

/-- Дефиниция на Римановата метрика на Картан (Fisher Information Metric). -/
def cartanMetric (S : ClPlus Q) [Invertible S.val] (V1 V2 : ClPlus Q) : R :=
  clTrace Q (clInv Q S * V1 * clInv Q S * V2)

/-- Свойство на инверсията при анти-автоморфизма hestenesAdjoint. -/
axiom hestenesAdjoint_inv (G : ClPlus Q) [Invertible G.val] [Invertible (hestenesAdjoint Q v0 G).val] :
  hestenesAdjoint Q v0 (clInv Q G) = clInv Q (hestenesAdjoint Q v0 G)

/-- Основна теорема: Инвариантност на метриката на Картан под coneConjugationAction. -/
theorem cartanMetric_invariance (G : ClPlus Q) [Invertible G.val] [Invertible (hestenesAdjoint Q v0 G).val]
    (S : ClPlus Q) [Invertible S.val] 
    (V1 V2 : ClPlus Q) :
    -- Изискваме инвертируемост на трансформирания елемент
    haveI : Invertible (coneConjugationAction Q v0 G S).val := sorry 
    cartanMetric Q (coneConjugationAction Q v0 G S) (coneConjugationAction Q v0 G V1) (coneConjugationAction Q v0 G V2) = 
    cartanMetric Q S V1 V2 := by
  sorry

end InfoGeometry.Riemannian
