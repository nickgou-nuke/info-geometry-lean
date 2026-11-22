/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

/-!
# Arithmetic audit of proposed Leech count expressions

This file checks natural-number arithmetic only. It does not construct the
extended Golay code or Leech lattice, nor derive vector-class counts from
lattice membership. The repo-owned constructions are in
`InfoGeometry.Combinatorics.ExtendedBinaryGolay` and
`InfoGeometry.Combinatorics.LeechLattice`.

The third expression must be `24 * 2^12` to produce `98,304`; the expression
`24 * 2^(12 - 1)` appearing in the supplied synthesis is `49,152` and cannot
yield the stated kissing-number total.
-/

namespace InfoGeometry.Canonical.LeechLatticeQuIPPoset

/-- First proposed count expression, as natural-number arithmetic. -/
def typeOneCountExpression : Nat := Nat.choose 24 2 * 2^2

/-- Second proposed count expression, using the supplied constant 759. -/
def typeTwoCountExpression : Nat := 759 * 2^7

/-- Corrected third expression needed for the stated arithmetic total. -/
def typeThreeCountExpression : Nat := 24 * 2^12

/-- The sum of the three count expressions. -/
def proposedCountSum : Nat :=
  typeOneCountExpression + typeTwoCountExpression + typeThreeCountExpression

/-- Exact arithmetic values of the three proposed count expressions. -/
theorem proposed_count_expressions_evaluate :
    typeOneCountExpression = 1104 ∧
    typeTwoCountExpression = 97152 ∧
    typeThreeCountExpression = 98304 ∧
    proposedCountSum = 196560 := by
  norm_num [Nat.choose, typeOneCountExpression, typeTwoCountExpression,
    typeThreeCountExpression, proposedCountSum]

/-- The exponent `12 - 1` in the supplied third expression misses a factor two. -/
theorem supplied_third_expression_is_half :
    24 * 2^(12 - 1) = 49152 ∧ 24 * 2^(12 - 1) ≠ 98304 := by
  norm_num

end InfoGeometry.Canonical.LeechLatticeQuIPPoset
