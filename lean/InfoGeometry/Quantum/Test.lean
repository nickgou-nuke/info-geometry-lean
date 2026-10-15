import InfoGeometry.Quantum.QuaternionSpinTimeReversal
import InfoGeometry.Algebra.FiniteSpinAlgebra

open InfoGeometry.Topology.Q8MonodromySpinorCover
open InfoGeometry.Quantum.QuaternionSpinTimeReversal

private theorem zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem q8A_add_test (i j : ZMod 4) : q8A (i + j) = q8A i * q8A j := by
  fin_cases i <;> fin_cases j <;> simp [q8A, ZMod.val] <;> rfl
