import Mathlib

/-!
# Even signed-permutation parameter counts

`EvenSignVectors n × Equiv.Perm (Fin n)` is the parameter type for even signed
permutations in rank `n`. The results below count this finite parameter type at
ranks 4 and 5. They do not construct a Coxeter quotient or a GAP certificate.

#### BUCKET 1: CLOSED FINITE THEOREMS
The two cardinalities are computed for the explicitly defined finite types.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None in this module.

#### BUCKET 3: OPEN CLOSURE DEBT
Identifying these parameter types with a presented Coxeter group remains open.
-/

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

/-- Sign vectors with even parity, represented over `ZMod 2`. -/
abbrev EvenSignVectors (n : ℕ) :=
  {v : Fin n → ZMod 2 // ∑ i, v i = 0}

/-- Parameters consisting of an even sign vector and a coordinate permutation. -/
abbrev TypeDParameters (n : ℕ) := EvenSignVectors n × Equiv.Perm (Fin n)

namespace TypeDParameterCounting

set_option maxRecDepth 10000
/-- The rank-four even signed-permutation parameter set has 192 elements. -/
theorem rank_four_parameter_card : Fintype.card (TypeDParameters 4) = 192 := by
  decide

/-- The rank-five even signed-permutation parameter set has 1920 elements. -/
theorem rank_five_parameter_card : Fintype.card (TypeDParameters 5) = 1920 := by
  decide

end TypeDParameterCounting
end InfoGeometry.Algebra.AnyonFiniteSpinBraid
