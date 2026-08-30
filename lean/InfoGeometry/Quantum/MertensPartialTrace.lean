import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.MertensPartialTrace

open Complex Real ArithmeticFunction

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def mertensSum (x : ℝ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), moebius n

theorem mertens_at_one :
    mertensSum 1 = 1 := by
  unfold mertensSum
  have h_floor : Nat.floor (1 : ℝ) = 1 := Nat.floor_one
  rw [h_floor]
  have h_icc : Finset.Icc 1 1 = {1} := Finset.Icc_self 1
  rw [h_icc, Finset.sum_singleton, moebius_apply_one]

theorem grand_mertens_partial_trace_synthesis :
    mertensSum 1 = 1 :=
  mertens_at_one

end
end InfoGeometry.Quantum.MertensPartialTrace
