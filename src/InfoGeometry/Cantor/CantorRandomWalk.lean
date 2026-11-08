import Mathlib.Tactic

noncomputable section

/-!
# CantorRandomWalk

Cantor configuration carrier and bit-flip action.

The Cantor carrier is the binary sequence space `ℕ → Bool`. Operator-valued
finite-mode steps are owned by `Cantor.CliffordMarkovOperators`, where they act
through the represented split Clifford algebra on the Fock carrier.
-/

namespace InfoGeometry.Cantor.CantorRandomWalk

/-- Cantor binary sequence space, read as infinitely many occupation bits. -/
abbrev CantorWord : Type :=
  ℕ → Bool

/-- Dirac-sea reference word with every mode unoccupied. -/
def diracSea : CantorWord :=
  fun _ => false

/-- Predicate saying two Cantor words differ at coordinate `n`. -/
def DifferAt (x y : CantorWord) (n : ℕ) : Prop :=
  x n ≠ y n

/-- A singleton bit flip at coordinate `i`. -/
def flipBit (i : ℕ) (x : CantorWord) : CantorWord :=
  fun j => if j = i then !(x j) else x j

/-- The flipped coordinate is negated. -/
@[simp] theorem flipBit_self (i : ℕ) (x : CantorWord) :
    flipBit i x i = !(x i) := by
  simp [flipBit]

/-- Other coordinates are unchanged by a singleton bit flip. -/
theorem flipBit_other {i j : ℕ} (hji : j ≠ i) (x : CantorWord) :
    flipBit i x j = x j := by
  simp [flipBit, hji]

/-- Flipping the same coordinate twice is the identity. -/
@[simp] theorem flipBit_involutive (i : ℕ) (x : CantorWord) :
    flipBit i (flipBit i x) = x := by
  ext j
  by_cases hji : j = i <;> simp [flipBit, hji]

/-- A singleton bit flip always changes the word. -/
theorem flipBit_ne_self (i : ℕ) (x : CantorWord) :
    flipBit i x ≠ x := by
  intro h
  have hi := congrFun h i
  simp [flipBit] at hi

/-- If two Cantor words are unequal, they differ at some coordinate. -/
theorem exists_differAt_of_ne {x y : CantorWord} (hxy : x ≠ y) :
    ∃ n : ℕ, DifferAt x y n := by
  by_contra hnone
  apply hxy
  funext n
  by_contra hd
  exact hnone ⟨n, hd⟩

/--
First coordinate at which two unequal Cantor words differ.

This is the discrete depth readout behind the usual Cantor ultrametric. The
file only uses the depth, not a metric-space instance.
-/
def firstDifference (x y : CantorWord) (hxy : x ≠ y) : ℕ :=
  by
    classical
    exact Nat.find (exists_differAt_of_ne hxy)

/-- The first-difference coordinate really differs. -/
theorem firstDifference_spec (x y : CantorWord) (hxy : x ≠ y) :
    DifferAt x y (firstDifference x y hxy) := by
  classical
  exact Nat.find_spec (exists_differAt_of_ne hxy)

/-- Before the first-difference depth, the two Cantor words agree. -/
theorem agree_before_firstDifference
    (x y : CantorWord) (hxy : x ≠ y) {k : ℕ}
    (hk : k < firstDifference x y hxy) :
    x k = y k := by
  classical
  by_contra hd
  have hle : firstDifference x y hxy ≤ k :=
    Nat.find_min' (exists_differAt_of_ne hxy) hd
  exact (not_le_of_gt hk) hle

end InfoGeometry.Cantor.CantorRandomWalk
