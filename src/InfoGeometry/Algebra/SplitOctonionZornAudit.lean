import InfoGeometry.Algebra.SplitOctonionZornAlgebra

/-!
# Split-Octonion Zorn Algebra Axiom Audit

Verifies that the Zorn vector-matrix realization of split-octonions,
two-sided determinant inversion, composition algebra multiplicativity,
neutral signature (4, 4) canonical quadratic form, and non-trivial zero divisors
rely strictly on standard Lean 4 foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`.
No custom axioms, no sorry, and no proxy certificate structures.
-/

namespace InfoGeometry.Algebra.SplitOctonionZorn.Audit

#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.mul_conj_eq_det_smul_one
#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.conj_mul_eq_det_smul_one
#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.zornDet_mul
#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.mul_one
#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.one_mul
#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.sub_mul
#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.mul_sub
#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.cancellation_identity
#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.zornDet_ofBasis8
#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.zero_divisor_witness
#print axioms InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion.split_octonion_zorn_synthesis

open InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion

theorem split_octonion_zorn_audit_soundness (X Y : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion)
    (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    X * conj X = zornDet X • (1 : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) ∧
    conj X * X = zornDet X • (1 : InfoGeometry.Algebra.SplitOctonionZorn.SplitOctonion) ∧
    zornDet (X * Y) = zornDet X * zornDet Y ∧
    zornDet (ofBasis8 x0 x1 x2 x3 x4 x5 x6 x7) =
      x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - x4 ^ 2 - x5 ^ 2 - x6 ^ 2 - x7 ^ 2 ∧
    (idempotentE1 ≠ 0 ∧ idempotentE2 ≠ 0 ∧ idempotentE1 * idempotentE2 = 0) :=
  split_octonion_zorn_synthesis X Y x0 x1 x2 x3 x4 x5 x6 x7

#print axioms split_octonion_zorn_audit_soundness

end InfoGeometry.Algebra.SplitOctonionZorn.Audit
