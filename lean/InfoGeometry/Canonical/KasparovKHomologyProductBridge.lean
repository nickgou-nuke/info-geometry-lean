import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace KasparovKHomologyProductBridge

/-- Finite matrix Fredholm-model datum in `Mₙ(ℂ)`.

This is not a C*-algebraic Kasparov module: the file records only the
displayed finite matrix hypotheses. -/
abbrev KasparovModule (n : ℕ) [DecidableEq (Fin n)] :=
  { F : selfAdjoint (Matrix (Fin n) (Fin n) ℂ) //
      (F : Matrix (Fin n) (Fin n) ℂ) * F = 1 }

namespace KasparovModule

variable {n : ℕ} [DecidableEq (Fin n)] (modAB modBC modCD : KasparovModule n)

abbrev fredholm_operator : Matrix (Fin n) (Fin n) ℂ := modAB.1

theorem h_self_adjoint : (fredholm_operator modAB).conjTranspose = fredholm_operator modAB := by
  simpa only [fredholm_operator, Matrix.star_eq_conjTranspose] using modAB.1.property

theorem h_involution : fredholm_operator modAB * fredholm_operator modAB = 1 := by
  exact modAB.2

/-- Involutivity of the finite matrix datum. -/
theorem kasparov_module_involution :
    fredholm_operator modAB * fredholm_operator modAB = 1 :=
  h_involution modAB

/-- Self-adjointness of the finite matrix datum. -/
theorem kasparov_module_self_adjoint :
    (fredholm_operator modAB).conjTranspose = fredholm_operator modAB :=
  h_self_adjoint modAB

/-- Composite matrix representative `F_AB * F_BC` in the finite model. -/
def kasparovProduct (x y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  x * y

/-- Associativity of finite matrix composition. -/
theorem kasparov_product_associativity (x y z : Matrix (Fin n) (Fin n) ℂ) :
    kasparovProduct (kasparovProduct x y) z = kasparovProduct x (kasparovProduct y z) := by
  dsimp [kasparovProduct]
  rw [mul_assoc]

/-- Trace identity for the finite matrix composite under the stated
    self-adjoint involution hypotheses. -/
theorem kasparov_product_trace_index (x y : Matrix (Fin n) (Fin n) ℂ)
    (hx_sa : x.conjTranspose = x) (hx_inv : x * x = 1)
    (hy_sa : y.conjTranspose = y) (hy_inv : y * y = 1) :
    trace (kasparovProduct x y * (kasparovProduct x y).conjTranspose) = n := by
  dsimp [kasparovProduct]
  rw [conjTranspose_mul, hy_sa, hx_sa, ← mul_assoc, mul_assoc x y y, hy_inv, mul_one, hx_inv, trace_one, Fintype.card_fin]

end KasparovModule

end KasparovKHomologyProductBridge
