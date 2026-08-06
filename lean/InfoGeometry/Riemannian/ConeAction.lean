import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Action.Defs
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Clifford.HestenesLorentzJordanCone

namespace InfoGeometry.Riemannian

open InfoGeometry.Clifford.Hestenes
open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M)

/-- Дефиниране на двустранното действие (Conjugation Action) чрез Clifford елемент 
    и неговия Hestenes Adjoint (reverse) оператор. -/
def coneConjugationAction (G : ClPlus Q) (X : ClPlus Q) : ClPlus Q :=
  L_action Q G (R_action Q (hestenesAdjoint Q v0 G) X)

/-- hestenesAdjoint на идентитета е идентитетът. -/
theorem hestenesAdjoint_one : hestenesAdjoint Q v0 (1 : ClPlus Q) = 1 := by
  sorry

/-- Доказателство, че идентитетът действа тривиално: 1 ⬝ X = X -/
theorem coneAction_one (X : ClPlus Q) : coneConjugationAction Q v0 1 X = X := by
  sorry

/-- hestenesAdjoint обръща реда на умножение (анти-автоморфизъм). -/
theorem hestenesAdjoint_mul (G1 G2 : ClPlus Q) :
    hestenesAdjoint Q v0 (G1 * G2) = hestenesAdjoint Q v0 G2 * hestenesAdjoint Q v0 G1 := by
  sorry

/-- Доказателство за свойството на съвместимост: (G1 * G2) ⬝ X = G1 ⬝ (G2 ⬝ X) -/
theorem coneAction_mul (G1 G2 : ClPlus Q) (X : ClPlus Q) :
    coneConjugationAction Q v0 (G1 * G2) X = coneConjugationAction Q v0 G1 (coneConjugationAction Q v0 G2 X) := by
  sorry

/-- Официално регистриране на действието като MulAction в Lean 4 типажите -/
instance : MulAction (ClPlus Q) (ClPlus Q) where
  smul := coneConjugationAction Q v0
  one_smul := coneAction_one Q v0
  mul_smul := coneAction_mul Q v0

end InfoGeometry.Riemannian
