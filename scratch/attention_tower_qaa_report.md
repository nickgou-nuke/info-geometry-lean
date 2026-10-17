# QA-A Semantic Review: Attention Tower Compatibility

**Disposition: ACCEPTED WITH LIMITED SCOPE.** This independent review found no
vacuous or misleading theorem among the four declarations in
`lean/InfoGeometry/QuantumContext/AttentionTowerCompatibility.lean`. The scope
is finite-stage compatibility in the existing dyadic complex matrix tower,
under the specified duplicated-logit transport.

## Source reconciliation

- `liftLogits` (lines 31–35) pulls an index back through
  `stageIndexEquiv k` and retains its first coordinate. Thus both values of the
  newly adjoined `Fin 2` coordinate receive the same old logit.
- `softmaxWeight_lift_eq_half` (61–76) follows because each old exponential
  occurs twice in the successor partition sum. The old denominator is strictly
  positive, and each lifted probability is exactly half its predecessor.
- The imported `concreteStep` is the star-algebra embedding
  `reindex(A ⊗ₖ 1₂)` (`CuntzMatrixTraceTower.lean`, lines 37–58), not an
  embedding of diagonal subalgebras. Its action on a diagonal matrix repeats
  each diagonal entry over the new tensor coordinate; the private helper at
  lines 78–102 proves that entrywise fact. Consequently the dimension-scaled
  density `2^k · softmaxWeight` is preserved by `concreteStep` (131–157): the
  factor-of-two increase in matrix dimension cancels the halving of each
  duplicated softmax weight.
- `modularUnitary_lift_compatible` (104–126) applies that same diagonal-entry
  repetition to the phases. The phase definition in
  `ColimitAttentionTomitaFlow.lean` is `exp(I * t * β * logit)`, so duplicated
  logits yield exactly duplicated phases.
- `modularFlow_lift_intertwines_concreteStep` (159–168) is quantified over
  **every** `A : MatrixStage k`. Since `concreteStep` preserves multiplication
  and the lifted unitary agrees with the embedded old unitary at both `t` and
  `-t`, the identity is for the full conjugation action
  `U_t A U_{-t}` on the noncommutative matrix algebra. It is not restricted to
  diagonal observables. The universal variables `logits`, `β`, `t`, and `A`
  and absence of extra hypotheses rule out vacuity from inconsistent premises.

## Scope limits

These theorems establish one-step successor compatibility for a coherent
family selected by duplicating logits. They do not construct or identify a
modular flow on the algebraic/analytic colimit, prove compatibility for
independently chosen logits at different stages, or establish analytic KMS
strip/holomorphy statements. The density and implementing unitary are diagonal
because they encode the finite softmax state; the intertwining theorem itself
acts on arbitrary full matrices through the actual matrix-tower embedding.
The results do not derive attention dynamics from a physical model.

## Mechanical evidence

- `python3 tools/infra/opengauss_screener.py lean/InfoGeometry/QuantumContext/AttentionTowerCompatibility.lean --strict` — passed, **0 traps**.
- `rg -n '\\b(sorry|admit|axiom)\\b' lean/InfoGeometry/QuantumContext/AttentionTowerCompatibility.lean` — no matches.
- `python3 tools/infra/opengauss_cli.py certify --file lean/InfoGeometry/QuantumContext/AttentionTowerCompatibility.lean --verify-kernel` — shared build lock acquired; owner build and generated axiom audit passed; **4 declarations covered**; exit code 0.

These mechanical results support kernel compilation and axiom closure; they are
not, by themselves, a semantic audit. The semantic disposition above is based
on inspection of the theorem statements and the cited owner definitions.
