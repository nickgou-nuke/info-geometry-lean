import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum

/-!
# Split Cayley-Dickson pure trace count

This file formalizes the combinatorial trace theorem for split Cayley-Dickson
blade signs.

For `q` negative-signature generators and `p > 0` positive/unitary generators,
the square sign of a blade is determined by the parity of the unitary part:
even unitary grade contributes `-1`, odd unitary grade contributes `+1`.

The total signed trace over all non-scalar pure blades is `1`.

This is only the trace-counting layer. It does not introduce a non-associative
Cayley-Dickson multiplication table or a Zorn multiplication table.
-/

namespace InfoGeometry.Canonical.SplitCayleyDicksonTrace

open Finset
open scoped BigOperators

/--
Square-trace sign for a blade whose unitary component has grade `k`.

This is `-(-1)^k`, hence even unitary grade gives `-1` and odd unitary grade
gives `+1`.
-/
def splitSquareTraceSign (k : ℕ) : ℤ :=
  -((-1 : ℤ) ^ k)

@[simp] theorem splitSquareTraceSign_zero :
    splitSquareTraceSign 0 = -1 := by
  norm_num [splitSquareTraceSign]

/-- Even unitary grade contributes square trace `-1`. -/
theorem splitSquareTraceSign_of_even {k : ℕ} (h : Even k) :
    splitSquareTraceSign k = -1 := by
  simp [splitSquareTraceSign, h.neg_one_pow]

/-- Odd unitary grade contributes square trace `+1`. -/
theorem splitSquareTraceSign_of_odd {k : ℕ} (h : Odd k) :
    splitSquareTraceSign k = 1 := by
  simp [splitSquareTraceSign, h.neg_one_pow]

/-- Number of blades in bidegree `(q, p)`, including the scalar blade. -/
def splitBladeCount (q p : ℕ) : ℕ :=
  2 ^ q * 2 ^ p

/-- Number of pure blades, excluding the scalar blade. -/
def splitPureBladeCount (q p : ℕ) : ℕ :=
  splitBladeCount q p - 1

/-- The bidegree blade count is `2^(q+p)`. -/
theorem splitBladeCount_eq_two_pow_add (q p : ℕ) :
    splitBladeCount q p = 2 ^ (q + p) := by
  simp [splitBladeCount, pow_add]

/-- The pure bidegree blade count is `2^(q+p)-1`. -/
theorem splitPureBladeCount_eq_two_pow_add_sub_one (q p : ℕ) :
    splitPureBladeCount q p = 2 ^ (q + p) - 1 := by
  simp [splitPureBladeCount, splitBladeCount_eq_two_pow_add]

/-- Alternating binomial sum over nonempty unitary levels vanishes for `p > 0`. -/
theorem alternating_choose_sum_zero {p : ℕ} (hp : 0 < p) :
    (∑ k ∈ range (p + 1), ((Nat.choose p k : ℤ) * (-1 : ℤ) ^ k)) = 0 := by
  have h := add_pow (-1 : ℤ) 1 p
  have hzero : ((-1 : ℤ) + 1) ^ p = 0 := by
    simp [hp.ne']
  rw [hzero] at h
  have hsum :
      (∑ k ∈ range (p + 1),
          (-1 : ℤ) ^ k * 1 ^ (p - k) * (Nat.choose p k : ℤ)) = 0 :=
    h.symm
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsum

/-- The signed unitary-grade contribution vanishes for at least one unitary generator. -/
theorem unitaryTraceContribution_zero {p : ℕ} (hp : 0 < p) :
    (∑ k ∈ range (p + 1), ((Nat.choose p k : ℤ) * splitSquareTraceSign k)) = 0 := by
  have h := alternating_choose_sum_zero (p := p) hp
  unfold splitSquareTraceSign
  simpa [Finset.sum_neg_distrib] using congrArg Neg.neg h

/--
Pure trace for split bidegree `(q,p)`.

All imaginary choices contribute the multiplicity `2^q`; the scalar blade has
sign `-1` and is removed from the pure trace, hence the final `+1`.
-/
def splitPureTrace (q p : ℕ) : ℤ :=
  (2 : ℤ) ^ q *
      (∑ k ∈ range (p + 1), ((Nat.choose p k : ℤ) * splitSquareTraceSign k)) +
    1

/--
Trace theorem: every split Cayley-Dickson bidegree with at least one unitary
generator has pure trace `1`.
-/
theorem splitPureTrace_eq_one {q p : ℕ} (hp : 0 < p) :
    splitPureTrace q p = 1 := by
  simp [splitPureTrace, unitaryTraceContribution_zero hp]

@[simp] theorem splitPureTrace_tildeC :
    splitPureTrace 0 1 = 1 := by
  exact splitPureTrace_eq_one (q := 0) (p := 1) (by norm_num)

@[simp] theorem splitPureTrace_tildeH :
    splitPureTrace 0 2 = 1 := by
  exact splitPureTrace_eq_one (q := 0) (p := 2) (by norm_num)

@[simp] theorem splitPureTrace_tildeO :
    splitPureTrace 0 3 = 1 := by
  exact splitPureTrace_eq_one (q := 0) (p := 3) (by norm_num)

@[simp] theorem splitPureTrace_A03 :
    splitPureTrace 0 3 = 1 := by
  exact splitPureTrace_tildeO

@[simp] theorem splitPureTrace_A04 :
    splitPureTrace 0 4 = 1 := by
  exact splitPureTrace_eq_one (q := 0) (p := 4) (by norm_num)

@[simp] theorem splitPureTrace_A31 :
    splitPureTrace 3 1 = 1 := by
  exact splitPureTrace_eq_one (q := 3) (p := 1) (by norm_num)

end InfoGeometry.Canonical.SplitCayleyDicksonTrace
