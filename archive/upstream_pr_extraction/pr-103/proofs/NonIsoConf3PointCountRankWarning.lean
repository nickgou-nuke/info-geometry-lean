import proofs.NonIsoConf3QuadricD4PointCount
import proofs.NonIsoConf3ProjectionQuotient

/-!
# Point-count warning against naive rank branches

The finite-field count polynomial for the actual translated D=4 open set

`U_4 = {(a,b) : q(a) q(b) q(a-b) != 0}`

does not match either naive specialization:

* independent/product-Leray rank-32 branch;
* OS-alpha rank-24 quotient branch.

This is only a finite-field point-count comparison.  It shows that neither
finite presentation should be identified with the actual complex de Rham answer
without a real Dupont/Gysin or D-module computation.
-/

noncomputable section

namespace NonIsoConf3PointCountRankWarning

open NonIsoConf3QuadricD4PointCount

/-- Actual D=4 point-count fingerprint from the cyclic convolution audit. -/
def actualCountZ (q : ℤ) : ℤ := countPolynomialZ q

/-- Naive product/Leray rank-32 finite branch specialization:
`q^8 (1-1/q)^3 (1-1/q^2)^2`, cleared to a polynomial. -/
def naiveRank32CountZ (q : ℤ) : ℤ :=
  q * (q - 1) ^ 5 * (q + 1) ^ 2

/-- Naive OS-alpha rank-24 finite branch specialization:
`q^8 (1-3/q+2/q^2)(1-1/q^2)^2`, cleared to a polynomial. -/
def naiveRank24CountZ (q : ℤ) : ℤ :=
  q ^ 2 * (q - 2) * (q - 1) ^ 3 * (q + 1) ^ 2

/-- Symbolic mismatch between the actual count and the naive rank-32
specialization. -/
theorem actual_minus_naiveRank32 (q : ℤ) :
    actualCountZ q - naiveRank32CountZ q =
      -q * (q - 1) ^ 2 * (q + 1) * (q ^ 2 - q - 1) := by
  unfold actualCountZ naiveRank32CountZ countPolynomialZ
  ring_nf

/-- Symbolic mismatch between the actual count and the naive rank-24
specialization. -/
theorem actual_minus_naiveRank24 (q : ℤ) :
    actualCountZ q - naiveRank24CountZ q =
      q ^ 2 * (q - 1) ^ 2 * (q + 1) := by
  unfold actualCountZ naiveRank24CountZ countPolynomialZ
  ring_nf

/-- At `q=3`, the actual count is not the naive rank-32 specialization. -/
theorem actual_p3_ne_naiveRank32 :
    actualCountZ 3 ≠ naiveRank32CountZ 3 := by
  norm_num [actualCountZ, naiveRank32CountZ, countPolynomialZ]

/-- At `q=3`, the actual count is not the naive rank-24 specialization. -/
theorem actual_p3_ne_naiveRank24 :
    actualCountZ 3 ≠ naiveRank24CountZ 3 := by
  norm_num [actualCountZ, naiveRank24CountZ, countPolynomialZ]

/-- Point-count warning: both naive finite branch specializations differ
from the actual D=4 finite-field fingerprint. -/
theorem point_count_rejects_both_naive_specializations :
    actualCountZ 3 = 1296 ∧
    naiveRank32CountZ 3 = 1536 ∧
    naiveRank24CountZ 3 = 1152 ∧
    actualCountZ 3 ≠ naiveRank32CountZ 3 ∧
    actualCountZ 3 ≠ naiveRank24CountZ 3 ∧
    (∀ q : ℤ, actualCountZ q - naiveRank32CountZ q =
      -q * (q - 1) ^ 2 * (q + 1) * (q ^ 2 - q - 1)) ∧
    (∀ q : ℤ, actualCountZ q - naiveRank24CountZ q =
      q ^ 2 * (q - 1) ^ 2 * (q + 1)) := by
  constructor
  · norm_num [actualCountZ, countPolynomialZ]
  constructor
  · norm_num [naiveRank32CountZ]
  constructor
  · norm_num [naiveRank24CountZ]
  constructor
  · exact actual_p3_ne_naiveRank32
  constructor
  · exact actual_p3_ne_naiveRank24
  constructor
  · exact actual_minus_naiveRank32
  · exact actual_minus_naiveRank24

/-- External data slots for a future D-module/Dupont computation.

These are `Type` fields rather than propositions: constructing this record
chooses representations for the computation stages but does not assert that
the de Rham answer has been computed in Lean. -/
structure ActualDeRhamComputationData where
  dModuleOrDupontGysinComputation : Type
  actualBettiNumbers : Type
  actualRingPresentation : Type
  cooperadMapsOnActualPresentation : Type

/-- Point-count warning: point counts reject the two naive specializations, so an
actual D-module/Dupont computation is required before identifying the de Rham
cohomology. -/
theorem point_count_warning_rejects_naive_branches :
    actualCountZ 3 ≠ naiveRank32CountZ 3 ∧
    actualCountZ 3 ≠ naiveRank24CountZ 3 := by
  constructor
  · exact actual_p3_ne_naiveRank32
  · exact actual_p3_ne_naiveRank24

end NonIsoConf3PointCountRankWarning

end noncomputable section
