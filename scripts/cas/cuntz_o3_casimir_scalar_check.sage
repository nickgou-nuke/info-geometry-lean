# Exact CAS check for the scalar coefficients in
# InfoGeometry.Algebra.CuntzO3LieAlgebraCasimir.casimir2_eq_scalar.
#
# Carrier alignment: the Lean owner defines invTwo = 1/2 and invSix = 1/6
# as central coefficients and proves the operator reductions from the Cuntz
# relations using its root-sum, Cartan-square, and completeness lemmas. This
# script checks only the resulting rational coefficient identities over QQ;
# it does not model or certify the noncommutative Cuntz carrier.

from sage.all import QQ

inv_two = QQ(1) / 2
inv_six = QQ(1) / 6

assert inv_two + inv_six == 4 * inv_six
assert QQ(2) + inv_two + inv_six == QQ(8) / 3

print("invTwo + invSix = 4 * invSix")
print("2 + invTwo + invSix = 8/3")
