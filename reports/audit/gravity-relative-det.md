# Gravitational Lean Context

- Query: `relative determinant scattering witness packet`
- Graph source: `arango`
- Nodes: `56014`
- Edges: `388729`
- Synonym groups: `3`
- Requested layers: `all`
- Promotion allowed: `false`

## Representation Layers

- `unlabeled`: `56014`

## Synonym Expansion

- `EQC-0765` matched `determinant, relative`; added `fredholm, partition, readout`
- `EQC-0386` matched `determinant, witness`; added `algebra, denominator, det, function, geometry, info, injective, matrix, minkowski, norm, operator, verified`
- `EQC-0004` matched `relative, witness`; added `action, additive, adjoint, algebraic, ambient, anomaly, antilinear, applications, arithmetic, automorphic, axis, backward, basis, ber, bernoulli, berry, beta, bilingual, binary, binv, bit, bivector, block, bogoliubov, boltzmann, boundary, bounded, brewster, bridge, bulk, calc, calibration, canonical, card, carrier, cayley, cci, central, certified, channel, charge, chi, chiral, chirality, cik, claim, class, clifford, clm, closure, cocycle, coeff, commutator, comp, compatibility, compatible, complementary, complex, complexity, conformal, conj, conjugate, conjugation, connection`

## 1. `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_exp_mul_mul_exp_neg`

- Score: `337.009266`
- Distance: `0`
- Module: `InfoGeometry.Canonical.EinsteinAnomalyOperator`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- Line: `429`

Doc:

Explicit `U χ_R U⁻¹` form for Bogoliubov conjugation of the lifted right chiral
anomaly operator, with `U = exp(tX)` and `X = relativeModularKGenerator`.


```lean
-- 425:         CCI.liftedLeftChiralAnomalyOperator) *
-- 426:       NormedSpace.exp (t • (-(relativeModularKGenerator (E := E) hMod))) := by
-- 427:   rfl
-- 428: 
-- 429: /--
-- 430: Explicit `U χ_R U⁻¹` form for Bogoliubov conjugation of the lifted right chiral
-- 431: anomaly operator, with `U = exp(tX)` and `X = relativeModularKGenerator`.
-- 432: -/
-- 433: theorem bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_exp_mul_mul_exp_neg
```

## 2. `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_exp_mul_mul_exp_neg`

- Score: `336.977293`
- Distance: `0`
- Module: `InfoGeometry.Canonical.EinsteinAnomalyOperator`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- Line: `416`

Doc:

Explicit `U χ_L U⁻¹` form for Bogoliubov conjugation of the lifted left chiral
anomaly operator, with `U = exp(tX)` and `X = relativeModularKGenerator`.


```lean
-- 412:     (relativeModularKGenerator (E := E) hMod)
-- 413:     CCI.liftedRightChiralAnomalyOperator
-- 414:     t
-- 415: 
-- 416: /--
-- 417: Explicit `U χ_L U⁻¹` form for Bogoliubov conjugation of the lifted left chiral
-- 418: anomaly operator, with `U = exp(tX)` and `X = relativeModularKGenerator`.
-- 419: -/
-- 420: theorem bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_exp_mul_mul_exp_neg
```

## 3. `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedRightChiralAnomalyOperator`

- Score: `334.908737`
- Distance: `0`
- Module: `InfoGeometry.Canonical.EinsteinAnomalyOperator`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- Line: `404`

Doc:

Bogoliubov conjugation of the lifted right chiral anomaly operator by the
relative-modular `K`-generator flow.


```lean
-- 400:     (relativeModularKGenerator (E := E) hMod)
-- 401:     CCI.liftedLeftChiralAnomalyOperator
-- 402:     t
-- 403: 
-- 404: /--
-- 405: Bogoliubov conjugation of the lifted right chiral anomaly operator by the
-- 406: relative-modular `K`-generator flow.
-- 407: -/
-- 408: noncomputable def bogoliubovConjugate_liftedRightChiralAnomalyOperator
```

## 4. `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedLeftChiralAnomalyOperator`

- Score: `334.876381`
- Distance: `0`
- Module: `InfoGeometry.Canonical.EinsteinAnomalyOperator`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- Line: `392`

Doc:

Bogoliubov conjugation of the lifted left chiral anomaly operator by the
relative-modular `K`-generator flow.


```lean
-- 388:           simp
-- 389:     _ = A := by
-- 390:           simp
-- 391: 
-- 392: /--
-- 393: Bogoliubov conjugation of the lifted left chiral anomaly operator by the
-- 394: relative-modular `K`-generator flow.
-- 395: -/
-- 396: noncomputable def bogoliubovConjugate_liftedLeftChiralAnomalyOperator
```

## 5. `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_exp_mul_mul_exp_neg`

- Score: `329.149274`
- Distance: `0`
- Module: `InfoGeometry.Canonical.EinsteinAnomalyOperator`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- Line: `558`

Doc:

Explicit `U χ U⁻¹` form for Bogoliubov conjugation of the lifted Einstein
anomaly operator, with `U = exp(tX)` and `X = relativeModularKGenerator`.


```lean
-- 554:     (relativeModularKGenerator (E := E) hMod)
-- 555:     CCI.liftedEinsteinAnomalyOperator
-- 556:     t
-- 557: 
-- 558: /--
-- 559: Explicit `U χ U⁻¹` form for Bogoliubov conjugation of the lifted Einstein
-- 560: anomaly operator, with `U = exp(tX)` and `X = relativeModularKGenerator`.
-- 561: -/
-- 562: theorem bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_exp_mul_mul_exp_neg
```

## 6. `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedEinsteinAnomalyOperator`

- Score: `327.596234`
- Distance: `0`
- Module: `InfoGeometry.Canonical.EinsteinAnomalyOperator`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- Line: `546`

Doc:

Bogoliubov conjugation of the lifted Einstein anomaly operator by the
relative-modular `K`-generator flow.


```lean
-- 542:   simpa using not_congr
-- 543:     (CCI.bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_zero_iff_of_commute_generator
-- 544:       hMod t hComm)
-- 545: 
-- 546: /--
-- 547: Bogoliubov conjugation of the lifted Einstein anomaly operator by the
-- 548: relative-modular `K`-generator flow.
-- 549: -/
-- 550: noncomputable def bogoliubovConjugate_liftedEinsteinAnomalyOperator
```

## 7. `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedRightChiralAnomalyOperator_ne_zero_iff_of_commute_generator`

- Score: `316.612324`
- Distance: `0`
- Module: `InfoGeometry.Canonical.EinsteinAnomalyOperator`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- Line: `530`

Doc:

In the commuting-generator regime, non-vanishing of the lifted right chiral
anomaly operator is invariant under Bogoliubov conjugation.


```lean
-- 526:   simpa using not_congr
-- 527:     (CCI.bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_zero_iff_of_commute_generator
-- 528:       hMod t hComm)
-- 529: 
-- 530: /--
-- 531: In the commuting-generator regime, non-vanishing of the lifted right chiral
-- 532: anomaly operator is invariant under Bogoliubov conjugation.
-- 533: -/
-- 534: theorem bogoliubovConjugate_liftedRightChiralAnomalyOperator_ne_zero_iff_of_commute_generator
```

## 8. `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedLeftChiralAnomalyOperator_ne_zero_iff_of_commute_generator`

- Score: `316.581386`
- Distance: `0`
- Module: `InfoGeometry.Canonical.EinsteinAnomalyOperator`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- Line: `514`

Doc:

In the commuting-generator regime, non-vanishing of the lifted left chiral
anomaly operator is invariant under Bogoliubov conjugation.


```lean
-- 510:   · intro hZero
-- 511:     simpa [CCI.bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_self_of_commute_generator
-- 512:       hMod t hComm] using hZero
-- 513: 
-- 514: /--
-- 515: In the commuting-generator regime, non-vanishing of the lifted left chiral
-- 516: anomaly operator is invariant under Bogoliubov conjugation.
-- 517: -/
-- 518: theorem bogoliubovConjugate_liftedLeftChiralAnomalyOperator_ne_zero_iff_of_commute_generator
```
