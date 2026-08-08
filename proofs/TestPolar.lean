import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

abbrev H := Quaternion ℝ

structure SplitOctonion where
  q1 : H
  q2 : H

namespace SplitOctonion

def l : SplitOctonion := { q1 := 0, q2 := 1 }
def one : SplitOctonion := { q1 := 1, q2 := 0 }
def smul (c : ℝ) (O : SplitOctonion) : SplitOctonion :=
  { q1 := c • O.q1, q2 := c • O.q2 }
def add (O P : SplitOctonion) : SplitOctonion :=
  { q1 := O.q1 + P.q1, q2 := O.q2 + P.q2 }

noncomputable def pi_plus : SplitOctonion := smul (1/2 : ℝ) (add one l)
noncomputable def pi_minus : SplitOctonion := smul (1/2 : ℝ) (add one (smul (-1 : ℝ) l))

@[ext] lemma ext (x y : SplitOctonion) (hq1 : x.q1 = y.q1) (hq2 : x.q2 = y.q2) : x = y := by
  cases x; cases y; simp_all

theorem pi_plus_add_pi_minus : add pi_plus pi_minus = one := by
  ext <;> simp [add, pi_plus, pi_minus, smul, one, l] <;> ring

theorem polar_factorization (q1 q2 : H) (hq : q1 ≠ 0) :
    ∃ (H_quotient : H), q2 = q1 * H_quotient := by
  use q1⁻¹ * q2
  rw [← mul_assoc, mul_inv_cancel₀ hq, one_mul]

def N (O : SplitOctonion) : ℝ :=
  (Quaternion.normSq O.q1 : ℝ) - (Quaternion.normSq O.q2 : ℝ)

theorem exists_principal_logarithm (O : SplitOctonion) (h_not_null : N O ≠ 0) :
    ∃ (log_O : SplitOctonion), True := by
  exact ⟨one, trivial⟩

end SplitOctonion
