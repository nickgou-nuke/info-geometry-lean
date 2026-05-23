import Mathlib

namespace DAG.KernelEquivalenceFixture

def twoA : Nat := 1 + 1

def twoB : Nat := 2

def three : Nat := 3

theorem twoA_eq_twoB : twoA = twoB := by
  rfl

theorem three_ne_twoA : three ≠ twoA := by
  decide

end DAG.KernelEquivalenceFixture
