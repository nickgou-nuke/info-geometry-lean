# Gravitational Lean Context

- Query: `GibbsSouriauGramAnalyticWitness partition_eq_integral_gibbsWeight massieu_eq_log_partition thermodynamicMoment_eq_gradient_at_beta fisherEquiv_eq_integral_centered_moment_product constructive trivial constant infinite Hilbert Gram`
- Graph source: `arango:faithful_raw`
- Nodes: `29852`
- Edges: `1325307`
- Synonym groups: `8`
- Requested layers: `all`
- Promotion allowed: `false`

## Representation Layers

- `unlabeled`: `25435`
- `L0_Count`: `2`; depth `0`; slug `count`
- `L1_Projective`: `203`; depth `1`; slug `projective`
- `L2_Operator`: `836`; depth `2`; slug `operator`
- `L3_Krein`: `1338`; depth `3`; slug `krein`
- `L4_ModularTransport`: `1696`; depth `4`; slug `transport`
- `L5_ThermodynamicClosure`: `342`; depth `5`; slug `thermo`

## Synonym Expansion

- `EQC-0020` matched `constant, fisher`; added `casimir, cosmological, curvature, energy, source`
- `EQC-0142` matched `thermodynamic, weight`; added `covariant, derivation, dynamics, weighted, weyl, zero`
- `EQC-0080` matched `souriau, thermodynamic`; added `density, generator, lifted, temperature, transport, vector`
- `EQC-0121` matched `thermodynamic, weight`; added `metriplectic, operatorial`
- `EQC-0260` matched `souriau, weight`; added `beta, canonical, geometric, geometry, info, pairing, thermodynamics`
- `EQC-0081` matched `souriau, weight`; added `grand, param, two`
- `EQC-0259` matched `infinite, souriau`; added `coadjoint, context, ent, finite, image, jaynes, max, moment, orbit, problem`
- `EQC-0114` matched `gibbs, weight`; added `bernoulli, class, clifford, exp, exponential, family, flow, hessian, metric, model, modular, multinomial, numerator, operator, partition, quotient, real, rotor`

## 1. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.ofLogPartitionAndFisherCovariance`

- Score: `701.447599`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `509`

Layer note: modular/transport/flow substrate

Doc:

Canonical dimension-agnostic Hessian constructor where the Massieu potential is
defined as the log partition and the covariance readout is defined to be the
Fisher/Hessian readout.

This constructively discharges the `massieu_eq_log_partition` and
`fisher_eq_covariance` fields.  It does not fake the analytic derivative,
strict positivity, Fenchel contact, or inverse-Hessian theorems; those remain
explicit obligations for a concrete infinite-dimensional smooth/operator model.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_83ce33bc5aa17c7eecd5a799af8d4e1c15c3795f`
- SCC: `scc_567814689be212c739cd2e883badbfaf63761e7e`
- Witness backed: `True`

```lean
-- 505: 
-- 506: variable {Orbit : Type u} {LieAlg : Type v} {LieCoalg : Type w}
-- 507: variable {Tangent DualTangent : Type*}
-- 508: 
-- 509: /--
-- 510: Canonical dimension-agnostic Hessian constructor where the Massieu potential is
-- 511: defined as the log partition and the covariance readout is defined to be the
-- 512: Fisher/Hessian readout.
-- 513: 
```

## 2. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.massieu_eq_log_partition_at`

- Score: `694.58672`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `919`

Layer note: modular/transport/flow substrate

Doc:

The full coadjoint-orbit Massieu potential is the log partition. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_0006824ae578035b1f77e6cb8c32816d287d0600`
- SCC: `scc_35d13782a9f09699843a1d7b4b67985da400ea98`
- Witness backed: `True`

```lean
-- 915:   (C :
-- 916:     InfiniteCoadjointOrbitHessianContext
-- 917:       Orbit LieAlg LieCoalg Tangent DualTangent)
-- 918: 
-- 919: /-- The full coadjoint-orbit Massieu potential is the log partition. -/
-- 920: @[rep_depth transport]
-- 921: theorem massieu_eq_log_partition_at (β : LieAlg) :
-- 922:     C.massieuPotential β = Real.log (C.partitionFunction β) :=
-- 923:   C.massieu_eq_log_partition β
```

## 3. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.massieu_eq_log_partition`

- Score: `681.728`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `468`

Doc:

Massieu is the logarithm of the partition functional. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_e084af160a757330d326801459a28656e50893ed`
- SCC: `scc_4837f1412c13e7930090f70172167e9abf0847c0`
- Witness backed: `True`

```lean
-- 464:   entropyHessian : LieCoalg → DualTangent → DualTangent → ℝ
-- 465:   /-- Inverse Fisher readout transported to the dual-side variations. -/
-- 466:   inverseFisherHessian : LieCoalg → DualTangent → DualTangent → ℝ
-- 467:   /-- Massieu is the logarithm of the partition functional. -/
-- 468:   massieu_eq_log_partition :
-- 469:     ∀ β : LieAlg, massieuPotential β = Real.log (partitionFunction β)
-- 470:   /-- First variation of Massieu gives the thermodynamic moment. -/
-- 471:   first_variation_eq_moment : Prop
-- 472:   /-- Proof of the first-variation/moment identity. -/
```

## 4. `InfoGeometry.Canonical.SouriauConformalKKT.ConformalGibbsSouriauOperatorContext.operatorMassieu_eq_log_partition`

- Score: `652.188964`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauConformalKKTContext`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean`
- Line: `279`

Layer note: modular/transport/flow substrate

Doc:

The Massieu potential is the logarithm of the operator partition. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_41cc110fc09e1013df6f6e9e624c3e2f19b576c6`
- SCC: `scc_ab84c2b60179919043745ac26b1fe66505293210`
- Witness backed: `True`

```lean
-- 275:     C.operatorPartition =
-- 276:       C.readout (NormedSpace.exp (-C.conformalGeometricTemperature)) := by
-- 277:   simp [operatorPartition, informationPartitionFunction]
-- 278: 
-- 279: /-- The Massieu potential is the logarithm of the operator partition. -/
-- 280: @[rep_depth transport]
-- 281: theorem operatorMassieu_eq_log_partition :
-- 282:     C.operatorMassieu = Real.log C.operatorPartition := by
-- 283:   rfl
```

## 5. `InfoGeometry.Canonical.SouriauTheoremTranslatorPacket.claimA_massieu_eq_log_partition`

- Score: `616.306408`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauTheoremTranslatorPacket`
- Declaration kind: `theorem`
- Representation layer: `L5_ThermodynamicClosure`
- Representation depth: `5`
- Representation slug: `thermo`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean`
- Line: `147`

Layer note: thermodynamic/free-energy/closure substrate

Doc:

Claim A: the finite Gibbs-Souriau Massieu potential is the logarithm of the
finite Gibbs-Souriau partition function.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_c0498973a9a54ee23e74449a40cce13d1fb80f72`
- SCC: `scc_4af9e2fb0eaa727db5149097a89aa6b0e0408c86`
- Witness backed: `True`

```lean
-- 143: end StrictOnsagerEquilibriumGate
-- 144: 
-- 145: /-! ## Claim A: partition function and Massieu potential -/
-- 146: 
-- 147: /--
-- 148: Claim A: the finite Gibbs-Souriau Massieu potential is the logarithm of the
-- 149: finite Gibbs-Souriau partition function.
-- 150: -/
-- 151: @[rep_depth thermo]
```

## 6. `InfoGeometry.Canonical.SouriauTranslatorAudit.audit_claimA_massieu_eq_log_partition`

- Score: `582.706156`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauTranslatorAudit`
- Declaration kind: `theorem`
- Representation layer: `L5_ThermodynamicClosure`
- Representation depth: `5`
- Representation slug: `thermo`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauTranslatorAudit.lean`
- Line: `73`

Layer note: thermodynamic/free-energy/closure substrate

Doc:

Audit alias for Claim A: partition/log-Massieu routing.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_e7777db3129ed5103d96c68d19d6281cad122a8e`
- SCC: `scc_f949165332444a504fae0cdcdc4fa5f6c9fc7b4d`
- Witness backed: `True`

```lean
-- 69:   rfl
-- 70: 
-- 71: /-! ## Contract aliases to compiled theorem surfaces -/
-- 72: 
-- 73: /--
-- 74: Audit alias for Claim A: partition/log-Massieu routing.
-- 75: -/
-- 76: @[rep_depth thermo]
-- 77: theorem audit_claimA_massieu_eq_log_partition
```

## 7. `InfoGeometry.Canonical.SouriauKreinMetriplectic.OperatorialMetriplecticContext.weightedDynamics_eq_weylCovariantThermodynamicDerivation`

- Score: `382.126878`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauKreinMetriplecticContext`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean`
- Line: `683`

Layer note: modular/transport/flow substrate

Doc:

The weighted Weyl dynamics is exactly the coordinate-free Lie derivation for
the density-weighted Souriau generator.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_a95f303fa14ff11ac401ee3ecf5c1de4802a2de3`
- SCC: `scc_f2d9b1f4885e2e93cbd72604ce13b10dd7f6a04d`
- Witness backed: `True`

```lean
-- 679:   simpa [weightedDynamics, zeroWeightDynamics, weightedPhaseAxisCommutator] using
-- 680:     densityWeightLiftedDynamics_eq_zeroWeight_add_weighted_phaseAxis_commutator
-- 681:       (E := E) C.P C.ψ C.A C.weight
-- 682: 
-- 683: /--
-- 684: The weighted Weyl dynamics is exactly the coordinate-free Lie derivation for
-- 685: the density-weighted Souriau generator.
-- 686: -/
-- 687: @[rep_depth transport]
```

## 8. `InfoGeometry.Canonical.SouriauKreinMetriplectic.OperatorialMetriplecticContext.weylCovariantThermodynamicDerivation`

- Score: `363.145089`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauKreinMetriplecticContext`
- Declaration kind: `def`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean`
- Line: `158`

Layer note: modular/transport/flow substrate

Doc:

Coordinate-free Weyl-covariant thermodynamic derivation.

This is the repo-native operational replacement for a coordinate derivative:
the generator is the Souriau temperature vector corrected by the Weyl density
weight, and the derivative of an observable is its Lie/commutator derivation.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_a99b797e0b9bf7773a3befe8202e85dd55545eb4`
- SCC: `scc_065c4beeab4e4152fcad0c78f96c99d0ddc93243`
- Witness backed: `True`

```lean
-- 154: @[rep_depth transport]
-- 155: noncomputable def weightedPhaseAxisCommutator : EndH :=
-- 156:   C.weight • transportCommutator (E := E) (densityWeightPhaseAxis (E := E)) C.A
-- 157: 
-- 158: /--
-- 159: Coordinate-free Weyl-covariant thermodynamic derivation.
-- 160: 
-- 161: This is the repo-native operational replacement for a coordinate derivative:
-- 162: the generator is the Souriau temperature vector corrected by the Weyl density
```

## 9. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation`

- Score: `357.827543`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `126`

Layer note: modular/transport/flow substrate

Doc:

Constructive dimension-agnostic coadjoint-orbit metriplectic context with a
square dissipation channel.

This removes the Casimir, Onsager nonnegativity, and total-split hypotheses
from the constructor.  The reversible entropy channel is definitionally zero,
the metric channel is `dissipationAmplitude x ^ 2`, and the total channel is
definitionally the same square.  No finite-dimensional matrix model is used.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_9bf4580f7d3f83bc50e5e5e9ec4ce38a7a4691bb`
- SCC: `scc_c9fb1c5fe8e0d6b719260a09cf00552a20e95e7f`
- Witness backed: `True`

```lean
-- 122:   casimir_reversible := casimir_reversible
-- 123:   onsager_metric_nonnegative := onsager_metric_nonnegative
-- 124:   total_entropy_split := total_entropy_split
-- 125: 
-- 126: /--
-- 127: Constructive dimension-agnostic coadjoint-orbit metriplectic context with a
-- 128: square dissipation channel.
-- 129: 
-- 130: This removes the Casimir, Onsager nonnegativity, and total-split hypotheses
```

## 10. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.full_gram_fisher_constructive_theorem`

- Score: `352.8555`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `644`

Layer note: modular/transport/flow substrate

Doc:

Packed constructive Fisher theorem for the dimension-agnostic Gram route. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_eca8155b6859d4992f9aeaa2550c04e6719f798c`
- SCC: `scc_1ace65551dead35c24a38de54cb1586551b89ea1`
- Witness backed: `True`

```lean
-- 640:     (entropy_gradient_eq_beta_holds := entropy_gradient_eq_beta_holds)
-- 641:     (entropy_hessian_eq_inverse_fisher := entropy_hessian_eq_inverse_fisher)
-- 642: 
-- 643: 
-- 644: /-- Packed constructive Fisher theorem for the dimension-agnostic Gram route. -/
-- 645: @[rep_depth transport]
-- 646: theorem full_gram_fisher_constructive_theorem
-- 647:     {Feature : Type*}
-- 648:     [NormedAddCommGroup Feature] [InnerProductSpace ℝ Feature]
```

## 11. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.fisher_hessian_eq_covariance`

- Score: `352.768102`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `925`

Layer note: modular/transport/flow substrate

Doc:

The full coadjoint-orbit Fisher/Hessian readout is the moment covariance. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_bc1b6ff27de3dc4c0ff2b8682681046ea0da6780`
- SCC: `scc_a9b38e9ea675e95711bdb38aced4322da6ad48a9`
- Witness backed: `True`

```lean
-- 921: theorem massieu_eq_log_partition_at (β : LieAlg) :
-- 922:     C.massieuPotential β = Real.log (C.partitionFunction β) :=
-- 923:   C.massieu_eq_log_partition β
-- 924: 
-- 925: /-- The full coadjoint-orbit Fisher/Hessian readout is the moment covariance. -/
-- 926: @[rep_depth transport]
-- 927: theorem fisher_hessian_eq_covariance (β : LieAlg) :
-- 928:     C.fisherHessian β = C.momentCovariance β :=
-- 929:   C.fisher_eq_covariance β
```

## 12. `InfoGeometry.Canonical.SouriauThermodynamics.geometricTemperatureWeightPairing_eq_beta_mul_shiftedMomentReadout`

- Score: `350.472231`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauThermodynamics`
- Declaration kind: `theorem`
- Representation layer: `L5_ThermodynamicClosure`
- Representation depth: `5`
- Representation slug: `thermo`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauThermodynamics.lean`
- Line: `89`

Layer note: thermodynamic/free-energy/closure substrate

Doc:

The finite Souriau weight pairing is exactly the exponent observable used by
the grand-canonical Gibbs kernel.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_28f625ee8c18ae7cdf31a6d370b714d2b4513661`
- SCC: `scc_a03331c1cb9dd6bad22a5aadc3b47d5816738c1e`
- Witness backed: `True`

```lean
-- 85: noncomputable def shiftedMomentReadout
-- 86:     (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) : ℝ :=
-- 87:   shiftedEnergy (toGrandCanonicalTwoParam M) T.mu x
-- 88: 
-- 89: /--
-- 90: The finite Souriau weight pairing is exactly the exponent observable used by
-- 91: the grand-canonical Gibbs kernel.
-- 92: -/
-- 93: @[rep_depth thermo]
```

## 13. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext`

- Score: `349.956348`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `inductive`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `427`

Layer note: modular/transport/flow substrate

Doc:

Abstract full coadjoint-orbit Hessian context.

This is the infinite-dimensional theorem target for the Souriau/Fisher prose:
it is not a finite `2×2` response matrix and it does not assume a count-state
model.  `Tangent` represents admissible variations of the geometric
temperature and `DualTangent` represents admissible variations on the dual
moment side.

The analytic content is intentionally explicit.  A concrete smooth
coadjoint-orbit model must provide the derivative, Hessian, covariance,
Legendre, and inverse-Hessian identities before downstream code may use the
full theorem.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_94223984de76be04bbe2752c08b8e2385d9c9ad7`
- SCC: `scc_54001b3a84ec5e6af631c39459bfcb2169620297`
- Witness backed: `True`

```lean
-- 423: end InfiniteCoadjointOrbitMetriplecticContext
-- 424: 
-- 425: /-! ## Full coadjoint-orbit Hessian/Fisher theorem surface -/
-- 426: 
-- 427: /--
-- 428: Abstract full coadjoint-orbit Hessian context.
-- 429: 
-- 430: This is the infinite-dimensional theorem target for the Souriau/Fisher prose:
-- 431: it is not a finite `2×2` response matrix and it does not assume a count-state
```

## 14. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.fisher_hessian_symmetric`

- Score: `346.345378`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `931`

Layer note: modular/transport/flow substrate

Doc:

Fisher symmetry in the full coadjoint-orbit Hessian interface. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_e3626f85be26bc9f3c30c4d11278abc28e13bf70`
- SCC: `scc_5e1e988cd3504b01a1c89483800c05f79410e8ca`
- Witness backed: `True`

```lean
-- 927: theorem fisher_hessian_eq_covariance (β : LieAlg) :
-- 928:     C.fisherHessian β = C.momentCovariance β :=
-- 929:   C.fisher_eq_covariance β
-- 930: 
-- 931: /-- Fisher symmetry in the full coadjoint-orbit Hessian interface. -/
-- 932: @[rep_depth transport]
-- 933: theorem fisher_hessian_symmetric (β : LieAlg) (X Y : Tangent) :
-- 934:     C.fisherHessian β X Y = C.fisherHessian β Y X :=
-- 935:   C.fisher_symmetric β X Y
```

## 15. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.ofLogPartitionGramFisher`

- Score: `346.015182`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `580`

Layer note: modular/transport/flow substrate

Doc:

Constructive dimension-agnostic Hessian/Fisher constructor from a Gram feature
map.

No finite matrix or count-state model is used.  The Fisher bilinear form is
`⟪feature β X, feature β Y⟫`, so symmetry, nonnegativity, and strict positivity
under feature nondegeneracy are derived from the real inner-product structure.
The analytic derivative, Fenchel contact, and inverse-Hessian obligations remain
explicit because they require a concrete smooth/coordinateless model.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_ba7734d8d48e7365d5a3b869ec64c864da4609c9`
- SCC: `scc_4517c237cc9626ebb6cf2c9dccad39e2123379c3`
- Witness backed: `True`

```lean
-- 576:   entropy_gradient_eq_beta := entropy_gradient_eq_beta
-- 577:   entropy_gradient_eq_beta_holds := entropy_gradient_eq_beta_holds
-- 578:   entropy_hessian_eq_inverse_fisher := entropy_hessian_eq_inverse_fisher
-- 579: 
-- 580: /--
-- 581: Constructive dimension-agnostic Hessian/Fisher constructor from a Gram feature
-- 582: map.
-- 583: 
-- 584: No finite matrix or count-state model is used.  The Fisher bilinear form is
```

## 16. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.ofSmoothLegendreSquareDissipation`

- Score: `345.161597`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `1156`

Layer note: modular/transport/flow substrate

Doc:

Fully constructive dimension-agnostic Hessian/metriplectic context assembled
from repo-owned infinite routes:

* Hessian/Fenchel/inverse-Fisher data comes from the smooth Legendre readout.
* Coadjoint-orbit closure is the image of the moment map.
* Reversible entropy is definitionally zero.
* Metric/total entropy production is a square.

This is not a finite shadow: `Orbit` is arbitrary and the Hessian side is an
arbitrary normed-space Legendre owner surface.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_71f41f39bb143c9f436544a8a4376c3e2068741f`
- SCC: `scc_e4413e6c3d4f52d94433ccf6430ec5b1168b901e`
- Witness backed: `True`

```lean
-- 1152: 
-- 1153: variable {Orbit : Type u}
-- 1154: variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
-- 1155: 
-- 1156: /--
-- 1157: Fully constructive dimension-agnostic Hessian/metriplectic context assembled
-- 1158: from repo-owned infinite routes:
-- 1159: 
-- 1160: * Hessian/Fenchel/inverse-Fisher data comes from the smooth Legendre readout.
```
