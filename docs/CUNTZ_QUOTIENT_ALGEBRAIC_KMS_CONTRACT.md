# Algebraic KMS closure on the corrected binary quotient

Status: full algebraic identity kernel-checked; independent QA accepted.

The carrier is `ComplexStarCuntzAlg Bool` from `ComplexStarCuntzRedesign`.
Use the existing `quotientProductFunctional` with both letter weights equal to
`1 / 2` and the existing algebra homomorphism `carrierFlow Complex.I`.
The target is, for every pair of quotient elements `x`, `y`,

```text
φ (x * y) = φ (y * carrierFlow Complex.I x).
```

The time convention is `carrierFlow z (Sℂ b) = exp(i z log 2) • Sℂ b`.
Thus imaginary time `i` scales `Sℂ b` by `1 / 2` and `Tℂ b` by `2`.
The inverse temperature for this convention is one.

## Existing owner evidence and required delta

- `CuntzComplexStarProductFunctional.quotientProductFunctional_nonneg`
  establishes positivity on every quotient star-square; normalization and
  star preservation are in `CuntzComplexStarProductFunctional`.
- `CuntzComplexStarProductWordReadout` computes all word-pair values from
  the genuine quotient functional, using the coherent matrix-colimit map.
- `CuntzComplexStarBinaryWordPairMultiplicationBridge` proves actual
  multiplication with both proper-prefix cases, in the same quotient.
- `CuntzComplexStarBinaryWordPairSpanBridge.sourceWordPair_span_eq_top`
  supplies the linear spanning argument.
- `CuntzComplexStarBinaryGaugeFlow` and `CuntzKMSCondition` provide the
  actual flow and the scalar imaginary-time evaluations respectively.

Prove generator twisted cyclicity against arbitrary quotient elements, then
extend across products and the existing spanning family. The first generator
law is `φ (Sℂ b * x) = (1 / 2) * φ (x * Sℂ b)`; derive the adjoint generator
law using star preservation. No cyclicity hypothesis is to be installed as
a structure field in place of this proof.

## Scope boundaries

The existing `CantorBernoulliAlgebraicWordKMSBridge.word_kms_monomial_comm`
is explicitly a scalar-kernel identity with equality-only middle matching.
It does not establish the target for arbitrary quotient products, whose
proper-prefix contributions must be retained.

The target is full **algebraic** twisted cyclicity. Analytic strip continuity,
a C*-completion, and a completed KMS state require additional theorems and
are not asserted by this contract. This work is a constructive continuation
of the counterexample correction, not a substitute for the remaining
repository-wide counterexample inventory and repairs.

## Generator step (2026-10-24)

`CuntzComplexStarGeneratorCyclicity` now proves the S generator identity
against every word pair, extends it to all quotient elements by span induction,
and derives the T identity with factor two by star preservation.
The locked target `InfoGeometry.OperatorAlgebra.CuntzComplexStarGeneratorCyclicityAudit`
passed (9421 jobs, exit zero; `/tmp/cuntz-generator-audit.log`). Its three
printed theorem dependencies are exactly `propext`, `Classical.choice`, and
`Quot.sound`. Strict screening found zero traps; semantic review passed.
Independent QA reran the target successfully (9421 jobs, exit zero;
`/tmp/cuntz-generator-qa.log`) and accepted the generator scope. There were
zero own-source warnings, 732 dependency-source warnings, and two package
notices. This generator step supplies the input for the closure below.

## Full algebraic closure (2026-10-24)

`CuntzComplexStarAlgebraicKMS.uniform_algebraic_KMS` (declaration namespace
`InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional`) directly
proves the existing `InfoGeometry.Modular.KMSState.IsAlgebraicKMS1` predicate
for the uniform quotient functional and `carrierFlow Complex.I`.
No cyclicity assumption is added. A reusable multiplication lemma propagates
generator cyclicity through words and adjoint words; the existing quotient
word-pair spanning theorem extends it to all first arguments.

The locked audit target
`InfoGeometry.OperatorAlgebra.CuntzComplexStarAlgebraicKMSAudit` passed
(9425 jobs, exit zero; `/tmp/cuntz-full-kms-audit.log`). The union of the
seven axiom reports is exactly `propext`, `Classical.choice`, and `Quot.sound`.
The generic multiplication lemma uses only `propext` and `Quot.sound`;
the other six reports contain all three.
The two new modules have zero compiler warnings. Strict screening found
zero traps; independent semantic review passed. Independent QA accepted the
same target: session 47823, exit zero, 9425 jobs, `/tmp/cuntz-full-kms-qa.log`.

The existing algebraic predicate expresses cyclicity only. Normalization and
positivity are supplied separately by the prior product-functional theorems.
This closes the full algebraic target above, while analytic strip regularity
and completion remain outside this theorem.
