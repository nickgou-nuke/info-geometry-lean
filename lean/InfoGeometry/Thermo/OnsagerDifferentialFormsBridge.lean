import Mathlib.LinearAlgebra.BilinearForm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import InfoGeometry.Thermo.OnsagerOperatorClosure

noncomputable section

namespace InfoGeometry.Thermo.OnsagerFormsBridge

open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem

variable {V W A : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]
  [Ring A] [Algebra ℝ A]

/-- The induced Onsager dissipative bilinear metric on operator 1-forms evaluated on test vectors. -/
def dissipative1Form
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u v : V) : ℝ :=
  S.dissipative (α u) (β v)

/-- The induced Onsager reversible skew-symplectic form on operator 1-forms. -/
def reversible1Form
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u v : V) : ℝ :=
  S.reversible (α u) (β v)

/-- The induced total non-equilibrium generator on operator 1-forms. -/
def totalGenerator1Form
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u v : V) : ℝ :=
  S.totalGenerator (α u) (β v)

/-- THEOREM 1 (1-Form Onsager Reciprocity):
    On matching test state u, the dissipative metric is symmetric in 1-forms:
      L(α u, β u) = L(β u, α u)
-/
theorem dissipative1Form_symm
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u : V) :
    dissipative1Form S α β u u = dissipative1Form S β α u u := by
  dsimp [dissipative1Form]
  exact S.dissipative_symm (α u) (β u)

/-- THEOREM 2 (1-Form Skew Reversibility):
    The reversible generator is skew-symmetric on 1-forms:
      Ω(α u, β u) = - Ω(β u, α u)
-/
theorem reversible1Form_skew
    (S : OnsagerCasimirSystem A) (α β : Op1Form ℝ V A) (u : V) :
    reversible1Form S α β u u = - reversible1Form S β α u u := by
  dsimp [reversible1Form]
  exact S.reversible_skew (α u) (β u)

/-- THEOREM 3 (Zero Dissipation of Reversible Bracket on 1-Forms):
    Ω(α u, α u) = 0
-/
@[simp]
theorem reversible1Form_diag_zero
    (S : OnsagerCasimirSystem A) (α : Op1Form ℝ V A) (u : V) :
    reversible1Form S α α u u = 0 := by
  dsimp [reversible1Form]
  exact S.reversible_diag_zero (α u)

/-- THEOREM 4 (1-Form Total Entropy Production):
    W(α u, α u) = L(α u, α u) ≥ 0
-/
theorem totalGenerator1Form_diag_eq
    (S : OnsagerCasimirSystem A) (α : Op1Form ℝ V A) (u : V) :
    totalGenerator1Form S α α u u = dissipative1Form S α α u u := by
  dsimp [totalGenerator1Form, dissipative1Form]
  exact S.entropy_production_eq (α u)

/-- THEOREM 5 (Second Law on Operator 1-Forms):
    Total entropy production of any operator 1-form is unconditionally non-negative:
      0 ≤ W(α u, α u)
-/
theorem totalGenerator1Form_nonneg
    (S : OnsagerCasimirSystem A) (α : Op1Form ℝ V A) (u : V) :
    0 ≤ totalGenerator1Form S α α u u := by
  dsimp [totalGenerator1Form]
  exact S.entropy_production_nonneg (α u)

/-- THEOREM 6 (Master Onsager–Casimir Reciprocity on Operator 1-Forms):
    Under time reversal T on the operator algebra, the 1-form generator satisfies:
      W((T ∘ α) u, (T ∘ β) u) = W(β u, α u)
-/
theorem onsager_casimir_1Form_master_reciprocity
    (PS : ParityOnsagerSystem A) (α β : Op1Form ℝ V A) (u : V) :
    PS.totalGenerator (PS.T.op (α u)) (PS.T.op (β u)) =
      totalGenerator1Form PS.toOnsagerCasimirSystem β α u u := by
  dsimp [totalGenerator1Form]
  exact PS.onsager_casimir_master_reciprocity (α u) (β u)

/-- THEOREM 7 (Pullback Invariance of the 1-Form Response):
    Pullback along linear map ϕ : W → V preserves the Onsager metric evaluated on pulled-back vectors:
      L(ϕ* α w, ϕ* β w) = L(α (ϕ w), β (ϕ w))
-/
theorem pullback_dissipative1Form_eq
    (S : OnsagerCasimirSystem A) (ϕ : W →ₗ[ℝ] V) (α β : Op1Form ℝ V A) (w : W) :
    dissipative1Form S (pullback1 ϕ α) (pullback1 ϕ β) w w =
      dissipative1Form S α β (ϕ w) (ϕ w) := by
  rfl

end InfoGeometry.Thermo.OnsagerFormsBridge

end noncomputable section
