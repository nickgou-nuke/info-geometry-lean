# Gravitational Lean Context

- Query: `GibbsSouriauGramAnalyticWitness InfiniteCoadjointOrbitHessianContext first_variation_eq_moment second_variation_eq_fisher fenchel_legendre_contact entropy_gradient_eq_beta LegendreContinuousLinearEquivInverseData Hilbert Gram feature infinite dimension agnostic`
- Graph source: `arango:faithful_raw`
- Nodes: `29852`
- Edges: `1325307`
- Synonym groups: `4`
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

- `EQC-0086` matched `context, continuous, hessian, inverse, legendre, linear`; added `axis, berry, channel, cik, comp, connection, dirac, entropy, eps, exp, fisher, gamma, holonomy, informational, involution, left, map, phase, plus, pminus, polarization, pplus, reverse, right, shadow, sigma, spinor, square, supercharge, thermal, transport, triality, vector`
- `EQC-0259` matched `coadjoint, context, infinite, orbit, souriau`; added `canonical, ent, finite, geometry, image, info, jaynes, max, metriplectic, moment, problem`
- `EQC-0116` matched `context, hessian, inverse, legendre`; added `coord, dual, log, model, potential, thermo`
- `EQC-0102` matched `data, gibbs, hessian`; added `ambient, bridge, coordinate, core, defect, density, energy, hamiltonian, massieu, minus, modular, operator, positive, projective, ray, real, recomposition, relative`

## 1. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.entropy_gradient_eq_beta_holds`

- Score: `1036.436726`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `498`

Doc:

Proof that the entropy gradient recovers the geometric-temperature coordinate. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_b7aa9752e72452f95ba0c596fe522f89752ac0ad`
- SCC: `scc_914f612464aec96af0630a94f25cf9a3efb89826`
- Witness backed: `True`

```lean
-- 494:   fenchel_legendre_contact_holds : fenchel_legendre_contact
-- 495:   /-- Entropy gradient recovers the geometric-temperature coordinate. -/
-- 496:   entropy_gradient_eq_beta : Prop
-- 497:   /-- Proof that the entropy gradient recovers the geometric-temperature coordinate. -/
-- 498:   entropy_gradient_eq_beta_holds : entropy_gradient_eq_beta
-- 499:   /-- Entropy Hessian is the inverse Fisher metric on the coadjoint dual lane. -/
-- 500:   entropy_hessian_eq_inverse_fisher :
-- 501:     ∀ (Q : LieCoalg),
-- 502:       entropyHessian Q = inverseFisherHessian Q
```

## 2. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.fenchel_legendre_contact`

- Score: `1030.735166`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `492`

Doc:

Fenchel-Legendre contact equation for entropy and Massieu. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_31ea09d03e22c1277a2ef26c70238fffa7c6332f`
- SCC: `scc_afee21e67397fa14595a4530c3601c96ed04da64`
- Witness backed: `True`

```lean
-- 488:   /-- Strict Fisher gate supplied by a concrete nondegenerate orbit model. -/
-- 489:   fisher_positive_of_nonzero :
-- 490:     ∀ (β : LieAlg) (X : Tangent), nonzeroTangent X → 0 < fisherHessian β X X
-- 491:   /-- Fenchel-Legendre contact equation for entropy and Massieu. -/
-- 492:   fenchel_legendre_contact : Prop
-- 493:   /-- Proof of the Fenchel-Legendre contact equation. -/
-- 494:   fenchel_legendre_contact_holds : fenchel_legendre_contact
-- 495:   /-- Entropy gradient recovers the geometric-temperature coordinate. -/
-- 496:   entropy_gradient_eq_beta : Prop
```

## 3. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.entropy_gradient_eq_beta`

- Score: `1024.645979`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `496`

Doc:

Entropy gradient recovers the geometric-temperature coordinate. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_770ec9ba6136b47e5e5dcb425e1f7b9bdeafacbc`
- SCC: `scc_7325ff973e56dd0f810c2dc6294233267fe60967`
- Witness backed: `True`

```lean
-- 492:   fenchel_legendre_contact : Prop
-- 493:   /-- Proof of the Fenchel-Legendre contact equation. -/
-- 494:   fenchel_legendre_contact_holds : fenchel_legendre_contact
-- 495:   /-- Entropy gradient recovers the geometric-temperature coordinate. -/
-- 496:   entropy_gradient_eq_beta : Prop
-- 497:   /-- Proof that the entropy gradient recovers the geometric-temperature coordinate. -/
-- 498:   entropy_gradient_eq_beta_holds : entropy_gradient_eq_beta
-- 499:   /-- Entropy Hessian is the inverse Fisher metric on the coadjoint dual lane. -/
-- 500:   entropy_hessian_eq_inverse_fisher :
```

## 4. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.first_variation_eq_moment`

- Score: `1024.382449`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `471`

Doc:

First variation of Massieu gives the thermodynamic moment. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_5c6cbd0aad8d1e0c5e6b37d8d55ce07bc2ae9bb5`
- SCC: `scc_c24791d04e90589c829d2fdba1a91c5ac8b4f981`
- Witness backed: `True`

```lean
-- 467:   /-- Massieu is the logarithm of the partition functional. -/
-- 468:   massieu_eq_log_partition :
-- 469:     ∀ β : LieAlg, massieuPotential β = Real.log (partitionFunction β)
-- 470:   /-- First variation of Massieu gives the thermodynamic moment. -/
-- 471:   first_variation_eq_moment : Prop
-- 472:   /-- Proof of the first-variation/moment identity. -/
-- 473:   first_variation_eq_moment_holds : first_variation_eq_moment
-- 474:   /-- Second variation of Massieu gives the Fisher/Hessian readout. -/
-- 475:   second_variation_eq_fisher : Prop
```

## 5. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.fenchel_legendre_contact_holds`

- Score: `1021.5285`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `494`

Doc:

Proof of the Fenchel-Legendre contact equation. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_0f21b645b4f6a39a6f5101baabc5f04208c8f585`
- SCC: `scc_2493bc5ea962036fa572880375d5c2ece8eee5bd`
- Witness backed: `True`

```lean
-- 490:     ∀ (β : LieAlg) (X : Tangent), nonzeroTangent X → 0 < fisherHessian β X X
-- 491:   /-- Fenchel-Legendre contact equation for entropy and Massieu. -/
-- 492:   fenchel_legendre_contact : Prop
-- 493:   /-- Proof of the Fenchel-Legendre contact equation. -/
-- 494:   fenchel_legendre_contact_holds : fenchel_legendre_contact
-- 495:   /-- Entropy gradient recovers the geometric-temperature coordinate. -/
-- 496:   entropy_gradient_eq_beta : Prop
-- 497:   /-- Proof that the entropy gradient recovers the geometric-temperature coordinate. -/
-- 498:   entropy_gradient_eq_beta_holds : entropy_gradient_eq_beta
```

## 6. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.second_variation_eq_fisher_holds`

- Score: `1021.477125`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `477`

Doc:

Proof of the second-variation/Fisher identity. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_3770ee8263db68cbe5c30c2a40e23c40c8954ac2`
- SCC: `scc_2b695535b6e30fc348a8e2a3934c74d305e01edf`
- Witness backed: `True`

```lean
-- 473:   first_variation_eq_moment_holds : first_variation_eq_moment
-- 474:   /-- Second variation of Massieu gives the Fisher/Hessian readout. -/
-- 475:   second_variation_eq_fisher : Prop
-- 476:   /-- Proof of the second-variation/Fisher identity. -/
-- 477:   second_variation_eq_fisher_holds : second_variation_eq_fisher
-- 478:   /-- Fisher/Hessian readout agrees with the coadjoint moment covariance. -/
-- 479:   fisher_eq_covariance :
-- 480:     ∀ β : LieAlg, fisherHessian β = momentCovariance β
-- 481:   /-- Fisher symmetry on all admissible temperature variations. -/
```

## 7. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.first_variation_eq_moment_holds`

- Score: `1021.42575`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `473`

Doc:

Proof of the first-variation/moment identity. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_68d9e1544318c0558ca446f3d8ecb7cde0edeb99`
- SCC: `scc_30909ab43d1cb502692d8893fca44a6ebe33d771`
- Witness backed: `True`

```lean
-- 469:     ∀ β : LieAlg, massieuPotential β = Real.log (partitionFunction β)
-- 470:   /-- First variation of Massieu gives the thermodynamic moment. -/
-- 471:   first_variation_eq_moment : Prop
-- 472:   /-- Proof of the first-variation/moment identity. -/
-- 473:   first_variation_eq_moment_holds : first_variation_eq_moment
-- 474:   /-- Second variation of Massieu gives the Fisher/Hessian readout. -/
-- 475:   second_variation_eq_fisher : Prop
-- 476:   /-- Proof of the second-variation/Fisher identity. -/
-- 477:   second_variation_eq_fisher_holds : second_variation_eq_fisher
```

## 8. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.second_variation_eq_fisher`

- Score: `1018.104817`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `475`

Doc:

Second variation of Massieu gives the Fisher/Hessian readout. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_1c24549026ebd4c52857c6d66c0e0ff3a514989c`
- SCC: `scc_3a3517aeff5deb4b30c6af6cd78a922aa04dfea9`
- Witness backed: `True`

```lean
-- 471:   first_variation_eq_moment : Prop
-- 472:   /-- Proof of the first-variation/moment identity. -/
-- 473:   first_variation_eq_moment_holds : first_variation_eq_moment
-- 474:   /-- Second variation of Massieu gives the Fisher/Hessian readout. -/
-- 475:   second_variation_eq_fisher : Prop
-- 476:   /-- Proof of the second-variation/Fisher identity. -/
-- 477:   second_variation_eq_fisher_holds : second_variation_eq_fisher
-- 478:   /-- Fisher/Hessian readout agrees with the coadjoint moment covariance. -/
-- 479:   fisher_eq_covariance :
```

## 9. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.ofSmoothLegendreReadout`

- Score: `767.236649`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `L5_ThermodynamicClosure`
- Representation depth: `5`
- Representation slug: `thermo`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `700`

Layer note: thermodynamic/free-energy/closure substrate

Doc:

Dimension-agnostic constructor that discharges the smooth Legendre/Fenchel and
inverse-Hessian fields from the repo-owned `LegendreHessianInverseContext`.

This is local in the usual inverse-function sense: the Fisher and entropy
Hessian readouts are the local continuous-linear-map Hessians at the Legendre
contact point.  No finite matrix inverse is used.  Positivity is deliberately
left to a Hilbert/Gram or operator-cone model and remains an explicit input.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_3fbed7c0e0f81820a0ef9a226ddd28dbb1256206`
- SCC: `scc_bba241b267c7ea411511aa6bf4a2502b0016a2fb`
- Witness backed: `True`

```lean
-- 696: open InfoGeometry.Geometry
-- 697: 
-- 698: variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
-- 699: 
-- 700: /--
-- 701: Dimension-agnostic constructor that discharges the smooth Legendre/Fenchel and
-- 702: inverse-Hessian fields from the repo-owned `LegendreHessianInverseContext`.
-- 703: 
-- 704: This is local in the usual inverse-function sense: the Fisher and entropy
```

## 10. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.ofLogPartitionGramFisher`

- Score: `743.081637`
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

## 11. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.ofContinuousLinearEquivLegendreGramSquareDissipation`

- Score: `734.636137`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `1240`

Layer note: modular/transport/flow substrate

Doc:

Fully constructive dimension-agnostic Hessian/metriplectic context using a
continuous-linear equivalence as the local Legendre inverse.

This removes the separate two-sided inverse-law fields from the Souriau input:
they are proved in `LegendreContinuousLinearEquivInverseData` from
`fisherEquiv` and `fisherEquiv.symm`.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_6ca892c6fabcfc99e5a69b0bd17fbd2e2b648525`
- SCC: `scc_56c2495e51257182ad07895efe78fde8cec1642c`
- Witness backed: `True`

```lean
-- 1236:       (Orbit := Orbit) (LieAlg := Θ) (LieCoalg := MomentCoord Θ)
-- 1237:       moment geometricTemperature reversibleVectorField metricVectorField
-- 1238:       entropy dissipationAmplitude
-- 1239: 
-- 1240: /--
-- 1241: Fully constructive dimension-agnostic Hessian/metriplectic context using a
-- 1242: continuous-linear equivalence as the local Legendre inverse.
-- 1243: 
-- 1244: This removes the separate two-sided inverse-law fields from the Souriau input:
```

## 12. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.ofLogPartitionAndFisherCovariance`

- Score: `731.782747`
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

## 13. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.ofSmoothLegendreGramReadout`

- Score: `721.031294`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `def`
- Representation layer: `L5_ThermodynamicClosure`
- Representation depth: `5`
- Representation slug: `thermo`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `807`

Layer note: thermodynamic/free-energy/closure substrate

Doc:

Dimension-agnostic smooth Legendre constructor with a Gram-represented Fisher
Hessian.

Compared with `ofSmoothLegendreReadout`, this removes the explicit Fisher
symmetry, nonnegativity, and strict-positivity hypotheses.  They are proved
from the inner-product Gram representation.  The remaining nontrivial model
identification is the real analytic bridge
`legendre.fisherHessian X Y = ⟪feature X, feature Y⟫`; this is the correct
place for concrete infinite-dimensional covariance/BKM models to connect.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_6726a1cb4b56ebf90b6aaf9f36e44c20afbed39d`
- SCC: `scc_be1f1bb4e94684d6690f17ce7d9d1d6ea52439e9`
- Witness backed: `True`

```lean
-- 803:       rfl⟩
-- 804: 
-- 805: attribute [terminal] full_smooth_legendre_constructive_theorem
-- 806: 
-- 807: /--
-- 808: Dimension-agnostic smooth Legendre constructor with a Gram-represented Fisher
-- 809: Hessian.
-- 810: 
-- 811: Compared with `ofSmoothLegendreReadout`, this removes the explicit Fisher
```

## 14. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.entropy_hessian_eq_inverse_fisher_at`

- Score: `716.911043`
- Distance: `None`
- Module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- Declaration kind: `theorem`
- Representation layer: `L4_ModularTransport`
- Representation depth: `4`
- Representation slug: `transport`
- File: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- Line: `950`

Layer note: modular/transport/flow substrate

Doc:

Entropy Hessian is the inverse Fisher readout on the coadjoint dual lane. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_2615d21b28deacaf4a12923c6afd92c720ae9b75`
- SCC: `scc_d6d8ae4531db3b1dedd25f55aa85422013d44863`
- Witness backed: `True`

```lean
-- 946:     (β : LieAlg) (X : Tangent) (hX : C.nonzeroTangent X) :
-- 947:     0 < C.fisherHessian β X X :=
-- 948:   C.fisher_positive_of_nonzero β X hX
-- 949: 
-- 950: /-- Entropy Hessian is the inverse Fisher readout on the coadjoint dual lane. -/
-- 951: @[rep_depth transport]
-- 952: theorem entropy_hessian_eq_inverse_fisher_at (Q : LieCoalg) :
-- 953:     C.entropyHessian Q = C.inverseFisherHessian Q :=
-- 954:   C.entropy_hessian_eq_inverse_fisher Q
```

## 15. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.full_gram_fisher_constructive_theorem`

- Score: `710.92575`
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

## 16. `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic.InfiniteCoadjointOrbitHessianContext.massieu_eq_log_partition_at`

- Score: `703.948897`
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
