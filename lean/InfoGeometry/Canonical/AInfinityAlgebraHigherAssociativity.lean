import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace AInfinityAlgebra

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- A_∞-Algebra Differential m₁ (Nilpotent: m₁ * m₁ = 0). -/
structure AInfinityDiff (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  m1 : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ
  m1_add : ∀ X Y, m1 (X + Y) = m1 X + m1 Y
  m1_nilpotent : ∀ X, m1 (m1 X) = 0

namespace AInfinityDiff

variable (diff : AInfinityDiff n)

/-- **Theorem**: A_∞ Differential Nilpotency m₁(m₁(X)) = 0. -/
theorem m1_squared_zero (X : Matrix (Fin n) (Fin n) ℂ) :
    diff.m1 (diff.m1 X) = 0 :=
  diff.m1_nilpotent X

/-- **Theorem**: A_∞ Differential Value at Zero m₁(0) = 0. -/
theorem m1_zero : diff.m1 0 = 0 := by
  have h : diff.m1 0 = diff.m1 0 + diff.m1 0 := by
    have h_add := diff.m1_add 0 0
    rw [add_zero] at h_add
    exact h_add
  have h_sub : diff.m1 0 - diff.m1 0 = (diff.m1 0 + diff.m1 0) - diff.m1 0 := by rw [← h]
  have h_lh : diff.m1 0 - diff.m1 0 = 0 := sub_self (diff.m1 0)
  have h_rh : (diff.m1 0 + diff.m1 0) - diff.m1 0 = diff.m1 0 := by noncomm_ring
  rw [h_lh, h_rh] at h_sub
  exact h_sub.symm

/-- A_∞ Binary Product m₂(a, b) = a * b. -/
def m2 (a b : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  a * b

/-- A_∞ Higher Ternary Homotopy Operator m₃(a, b, c). -/
def m3 (a b c : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  0

/-- **Theorem**: Strict Associativity for Associative Product m₂(m₂(a,b), c) - m₂(a, m₂(b,c)) = 0. -/
theorem m2_associative (a b c : Matrix (Fin n) (Fin n) ℂ) :
    m2 (m2 a b) c - m2 a (m2 b c) = 0 := by
  dsimp [m2]
  noncomm_ring

/-- **Theorem**: A_∞ Stasheff Relation for k=3:
    m₁(m₃(a,b,c)) + m₃(m₁(a),b,c) + m₃(a,m₁(b),c) + m₃(a,b,m₁(c)) + m₂(m₂(a,b),c) - m₂(a,m₂(b,c)) = 0. -/
theorem stasheff_k3_relation (diff : AInfinityDiff n) (a b c : Matrix (Fin n) (Fin n) ℂ) :
    diff.m1 (m3 a b c) + m3 (diff.m1 a) b c + m3 a (diff.m1 b) c + m3 a b (diff.m1 c) +
    m2 (m2 a b) c - m2 a (m2 b c) = 0 := by
  dsimp [m3, m2]
  rw [diff.m1_zero]
  noncomm_ring

end AInfinityDiff

end AInfinityAlgebra
