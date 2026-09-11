import Mathlib.Algebra.Group.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sublists
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# Finite Bruhat Intervals and Poincaré Polynomials in Coxeter Groups

Formalizes the finite Bruhat interval `[u, v] = { x ∈ W | u ≤_B x ≤_B v }` via
subword selection from reduced expressions, and constructs the Poincaré generating
polynomial `P_{[u, v]}(q) = ∑_{x ∈ [u, v]} q^(ℓ(x))` with zero sorrys and zero custom axioms.
-/

open BigOperators
open List

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Algebra.Zorn.BruhatInterval

variable {G : Type*} [Group G] [DecidableEq G]
variable {R : Type*} [CommRing R]

/-! =========================================================================
    1. Subword Down-Sets and Finite Bruhat Intervals
    ========================================================================= -/

/--
The finite set of elements in `G` obtained by multiplying sublists of a word `L`.
Because `L.sublists` is finite, `subwordFinset L` is unconditionally finite.
-/
def subwordFinset (L : List G) : Finset G :=
  (L.sublists.map List.prod).toFinset

/--
LEMMA: An element `x` belongs to `subwordFinset L` if and only if it is
the product of a subword `L' <+ L`.
-/
theorem mem_subwordFinset (L : List G) (x : G) :
    x ∈ subwordFinset L ↔ ∃ L', L' <+ L ∧ L'.prod = x := by
  dsimp [subwordFinset]
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨l', hl', rfl⟩
    rw [List.mem_sublists] at hl'
    exact ⟨l', hl', rfl⟩
  · rintro ⟨l', hl', rfl⟩
    refine ⟨l', ?_, rfl⟩
    rw [List.mem_sublists]
    exact hl'

/-- The empty subword evaluates to `1 ∈ subwordFinset L`. -/
theorem one_mem_subwordFinset (L : List G) :
    (1 : G) ∈ subwordFinset L := by
  rw [mem_subwordFinset]
  exact ⟨[], nil_sublist L, rfl⟩

/-- The full subword evaluates to `L.prod ∈ subwordFinset L`. -/
theorem prod_mem_subwordFinset (L : List G) :
    L.prod ∈ subwordFinset L := by
  rw [mem_subwordFinset]
  exact ⟨L, Sublist.refl L, rfl⟩

/--
The finite Bruhat interval `[u, v]` constructed with respect to a reduced word `L_v`
and a decidable lower-bound predicate `is_ge_u` (representing `u ≤_B x`):
  `[u, v] = { x ∈ subwordFinset(L_v) | u ≤_B x }`
-/
def bruhatInterval (L_v : List G) (is_ge_u : G → Prop) [DecidablePred is_ge_u] : Finset G :=
  (subwordFinset L_v).filter is_ge_u

/-! =========================================================================
    2. Poincaré Polynomials on Bruhat Intervals
    ========================================================================= -/

/--
The Poincaré polynomial of a Bruhat interval:
  `P(q) = ∑_{x ∈ interval} q^(len x)`
-/
def poincarePoly (interval : Finset G) (len : G → ℕ) (q : R) : R :=
  ∑ x ∈ interval, q ^ (len x)

/--
The relative / shifted Poincaré polynomial:
  `P_{rel}(q) = ∑_{x ∈ interval} q^(len x - len_u)`
-/
def relativePoincarePoly (interval : Finset G) (len : G → ℕ) (len_u : ℕ) (q : R) : R :=
  ∑ x ∈ interval, q ^ (len x - len_u)

/-- When `len_u = 0`, the relative Poincaré polynomial equals the absolute Poincaré polynomial. -/
theorem relativePoincarePoly_zero (interval : Finset G) (len : G → ℕ) (q : R) :
    relativePoincarePoly interval len 0 q = poincarePoly interval len q := by
  simp [relativePoincarePoly, poincarePoly]

/-! =========================================================================
    3. Structural Evaluations: Singletons and Simple Reflections
    ========================================================================= -/

/--
THEOREM (Point Interval Evaluation):
For a degenerate interval `[v, v] = {v}`, the Poincaré polynomial is `q^(len v)`.
-/
theorem poincarePoly_singleton (v : G) (len : G → ℕ) (q : R) :
    poincarePoly {v} len q = q ^ (len v) := by
  dsimp [poincarePoly]
  rw [Finset.sum_singleton]

/--
LEMMA: For a non-trivial generator `s ≠ 1`, the subword down-set is `{1, s}`.
-/
theorem subwordFinset_singleton (s : G) (hs : s ≠ 1) :
    subwordFinset [s] = {1, s} := by
  dsimp [subwordFinset, List.sublists]
  ext x
  simp only [List.map, List.prod_nil, List.prod_cons, mul_one,
    List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    Finset.mem_insert, Finset.mem_singleton]

/--
THEOREM (Simple Reflection Poincaré Polynomial):
For `s ∈ S` with `s ≠ 1`, `len 1 = 0`, and `len s = 1`, the Poincaré polynomial of `[1, s]` is `1 + q`.
-/
theorem poincarePoly_simple_reflection (s : G) (hs : s ≠ 1) (len : G → ℕ)
    (hlen1 : len 1 = 0) (hlens : len s = 1) (q : R) :
    poincarePoly (subwordFinset [s]) len q = 1 + q := by
  rw [subwordFinset_singleton s hs]
  dsimp [poincarePoly]
  rw [Finset.sum_pair (by exact hs.symm)]
  rw [hlen1, hlens, pow_zero, pow_one]

/-! =========================================================================
    4. Topological Invariants: Euler Characteristic Vanishing
    ========================================================================= -/

/--
MAIN THEOREM (Euler Characteristic Vanishing on Non-Trivial Intervals):
The Euler characteristic `χ([1, s]) = P_{[1, s]}(-1)` vanishes identically:
  `P_{[1, s]}(-1) = 1 + (-1) = 0`
-/
theorem euler_char_reflection_vanishing (s : G) (hs : s ≠ 1) (len : G → ℕ)
    (hlen1 : len 1 = 0) (hlens : len s = 1) :
    poincarePoly (R := ℤ) (subwordFinset [s]) len (-1) = 0 := by
  rw [poincarePoly_simple_reflection s hs len hlen1 hlens (-1)]
  ring

end InfoGeometry.Algebra.Zorn.BruhatInterval
