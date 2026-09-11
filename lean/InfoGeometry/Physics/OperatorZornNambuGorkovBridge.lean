import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Star.Basic

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A] [StarRing A]

/-- Four operator entries arranged in the two chiral Peirce sectors.

This is an operator-valued carrier, not yet a multiplication on the
four-tuples and not a claim of a BdG Hamiltonian or spectral triple. -/
structure OperatorZornMatrix (A : Type*) [Ring A] [StarRing A] where
  n_plus_op : A
  n_minus_op : A
  sigma_plus_op : A
  sigma_minus_op : A

namespace OperatorZornMatrix

/-- Charge-conjugation-style involution on the four operator entries. -/
def nambuGorkovConjugation (M : OperatorZornMatrix A) : OperatorZornMatrix A where
  n_plus_op := -star M.n_minus_op
  n_minus_op := -star M.n_plus_op
  sigma_plus_op := star M.sigma_minus_op
  sigma_minus_op := star M.sigma_plus_op

@[simp] theorem nambuGorkovConjugation_involution
    (M : OperatorZornMatrix A) :
    nambuGorkovConjugation (nambuGorkovConjugation M) = M := by
  cases M; simp [nambuGorkovConjugation]

/-- The involution is packaged as an equivalence of the four-entry carrier. -/
def nambuGorkovEquiv : OperatorZornMatrix A ≃ OperatorZornMatrix A where
  toFun := nambuGorkovConjugation
  invFun := nambuGorkovConjugation
  left_inv := nambuGorkovConjugation_involution
  right_inv := nambuGorkovConjugation_involution

def operatorPeirceForm (H Delta : A) : A :=
  H * (-star H) - Delta * star Delta

theorem operatorPeirceForm_eq_neg_sum (H Delta : A) :
    operatorPeirceForm H Delta =
      -(H * star H + Delta * star Delta) := by
  unfold operatorPeirceForm
  calc
    H * (-star H) - Delta * star Delta =
        -(H * star H) - Delta * star Delta := by rw [mul_neg]
    _ = -(H * star H + Delta * star Delta) := by
      rw [sub_eq_add_neg, ← neg_add]

def IsOperatorPeirceNull (H Delta : A) : Prop :=
  operatorPeirceForm H Delta = 0

theorem isOperatorPeirceNull_iff (H Delta : A) :
    IsOperatorPeirceNull H Delta ↔
      H * star H + Delta * star Delta = 0 := by
  unfold IsOperatorPeirceNull
  rw [operatorPeirceForm_eq_neg_sum]
  exact neg_eq_zero

theorem operatorZorn_nambuGorkov_synthesis
    (M : OperatorZornMatrix A) (H Delta : A) :
    nambuGorkovConjugation (nambuGorkovConjugation M) = M ∧
      operatorPeirceForm H Delta =
        -(H * star H + Delta * star Delta) := by
  exact ⟨nambuGorkovConjugation_involution M, operatorPeirceForm_eq_neg_sum H Delta⟩

end OperatorZornMatrix

end InfoGeometry.Physics
