# Gravitational Lean Context

- Query: `Drazin Moore-Penrose projector noncommutativity dilation conformal Cl(4,4)`
- Graph source: `arango:faithful_raw`
- Nodes: `34355`
- Edges: `1473813`
- Synonym groups: `8`
- Requested layers: `all`
- Promotion allowed: `false`

## Representation Layers

- `unlabeled`: `29357`
- `L0_Count`: `2`; depth `0`; slug `count`
- `L1_Projective`: `219`; depth `1`; slug `projective`
- `L2_Operator`: `1033`; depth `2`; slug `operator`
- `L3_Krein`: `1369`; depth `3`; slug `krein`
- `L4_ModularTransport`: `1828`; depth `4`; slug `transport`
- `L5_ThermodynamicClosure`: `547`; depth `5`; slug `thermo`

## Synonym Expansion

- `EQC-0226` matched `dilation, drazin, penrose, projector`; added `canonical, dpdkkt, geometry, info, kernel, kkt, left`
- `EQC-0227` matched `dilation, drazin, penrose, projector`; added `right`
- `EQC-0152` matched `conformal, moore, penrose, projector`; added `inference, inverse, unification`
- `EQC-0228` matched `dilation, drazin, penrose, projector`; added `complementary, spectral`
- `EQC-0225` matched `dilation, drazin, penrose, projector`; added `delta, generator, mismatch`
- `EQC-0329` matched `moore, penrose, projector`; added ``
- `EQC-0174` matched `dilation, drazin, penrose`; added `commutator, supercharge`
- `EQC-0229` matched `dilation, drazin, penrose`; added `anomaly`

## 1. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_rightProjector_commute`

- Score: `359.305886`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `748`

Doc:

If the Drazin spectral projector commutes with the Moore-Penrose right
projector, then its commutator with the conformal dilation generator is exactly
minus one half of the left-projector chiral anomaly.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_9fe7abb5b0db32ed9da4e577a3ad009f0f48bacb`
- SCC: `scc_ace621a166fbb6e29dcba68d06eb4de6cfbc940d`
- Witness backed: `True`

```lean
-- 744:   simp [rightChiralAnomaly, chiralAnomalyOperator, chiralAnomaly, P_MP_right,
-- 745:     IsMoorePenroseInverse.rightProjector, sub_eq_add_neg, add_assoc, add_left_comm,
-- 746:     add_comm, smul_add, smul_neg]
-- 747: 
-- 748: /--
-- 749: If the Drazin spectral projector commutes with the Moore-Penrose right
-- 750: projector, then its commutator with the conformal dilation generator is exactly
-- 751: minus one half of the left-projector chiral anomaly.
-- 752: -/
```

## 2. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralAnomaly_eq_zero`

- Score: `351.91875`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `804`

Doc:

If the Drazin spectral projector commutes with the Moore-Penrose right
projector and the chiral anomaly vanishes, then it commutes with the conformal
dilation generator.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_3cb1f1d5b1962fec6ebe66ccaf1d7bb552dbb45a`
- SCC: `scc_f5ba48c8e7a284588bfe41de9faae3e1050aefb8`
- Witness backed: `True`

```lean
-- 800:   exact
-- 801:     CI.spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_rightProjector_commute
-- 802:       (CI.rightProjector_commute_of_projectorAgreement_of_metricProjector_commute hProj hLeft)
-- 803: 
-- 804: /--
-- 805: If the Drazin spectral projector commutes with the Moore-Penrose right
-- 806: projector and the chiral anomaly vanishes, then it commutes with the conformal
-- 807: dilation generator.
-- 808: -/
```

## 3. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero`

- Score: `349.682667`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalAnomalySource`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- Line: `377`

Doc:

If the Drazin spectral projector commutes with the Moore-Penrose right
projector and the scalar chiral source vanishes, then the spectral projector
commutes with the conformal dilation generator.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_3085a5c88fe58fc226f1c4e05d8008d59def5084`
- SCC: `scc_0ed8d38384e4709fc449f1b319b77bbe4eed555c`
- Witness backed: `True`

```lean
-- 373:   have hAnomZero : CI.chiralAnomalyOperator = 0 :=
-- 374:     (nnnorm_eq_zero).1 hNormAnom
-- 375:   exact CI.projectors_commute_of_chiralAnomaly_eq_zero hAnomZero
-- 376: 
-- 377: /--
-- 378: If the Drazin spectral projector commutes with the Moore-Penrose right
-- 379: projector and the scalar chiral source vanishes, then the spectral projector
-- 380: commutes with the conformal dilation generator.
-- 381: -/
```

## 4. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_projectorAgreement_of_metricProjector_commute`

- Score: `340.209896`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `789`

Doc:

Structured dilation-source closure:
if left/right Moore-Penrose projectors agree and the Drazin projector commutes
with the left metric projector, then the dilation commutator is
`-1/2` times the left anomaly.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_ccb0786cbded330111ff88224e0453a508bffbfe`
- SCC: `scc_ac2a8033e3484870e10a5f5583c612e40ebf532e`
- Witness backed: `True`

```lean
-- 785:     (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
-- 786:     CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D := by
-- 787:   simpa [hProj] using hLeft
-- 788: 
-- 789: /--
-- 790: Structured dilation-source closure:
-- 791: if left/right Moore-Penrose projectors agree and the Drazin projector commutes
-- 792: with the left metric projector, then the dilation commutator is
-- 793: `-1/2` times the left anomaly.
```

## 5. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_of_rightProjector_commute`

- Score: `336.31463`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalAnomalySource`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- Line: `397`

Doc:

Operator-first dilation/anomaly bridge:
if the Drazin spectral projector commutes with the Moore-Penrose right
projector, the dilation commutator is exactly minus one half of the
projector-obstruction operator.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_f2d45a97583519623065bef26926078f291c6020`
- SCC: `scc_2f8d30c3578f7ce774e7bdcf7c59a06c0b14b7e0`
- Witness backed: `True`

```lean
-- 393:   exact
-- 394:     CI.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralAnomaly_eq_zero
-- 395:       hRight hAnomZero
-- 396: 
-- 397: /--
-- 398: Operator-first dilation/anomaly bridge:
-- 399: if the Drazin spectral projector commutes with the Moore-Penrose right
-- 400: projector, the dilation commutator is exactly minus one half of the
-- 401: projector-obstruction operator.
```

## 6. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.dilationSource_eq_neg_half_projectorObstruction_of_projectorAgreement_of_metricProjector_commute`

- Score: `316.003486`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalAnomalyOperator`
- Declaration kind: `theorem`
- Representation layer: `L3_Krein`
- Representation depth: `3`
- Representation slug: `krein`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalAnomalyOperator.lean`
- Line: `107`

Layer note: Krein/doubled-geometry substrate

Doc:

Primary structured dilation-source identity on the operator layer:
if left/right Moore-Penrose projectors agree and the Drazin projector commutes
with the left metric projector, the dilation commutator is `-1/2` times the
projector-obstruction operator.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_af184ebe2a5d80951fbe4d6d52eb72b7e0e721de`
- SCC: `scc_d4b7cbab103ffa4a217421035061828d761a5576`
- Witness backed: `True`

```lean
-- 103:   exact
-- 104:     CI.spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_of_rightProjector_commute
-- 105:       hRight
-- 106: 
-- 107: /--
-- 108: Primary structured dilation-source identity on the operator layer:
-- 109: if left/right Moore-Penrose projectors agree and the Drazin projector commutes
-- 110: with the left metric projector, the dilation commutator is `-1/2` times the
-- 111: projector-obstruction operator.
```

## 7. `InfoGeometry.Canonical.CertifiedInverseKernel.rightAnomalyGenerator`

- Score: `315.471324`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationAlgebra`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationAlgebra.lean`
- Line: `64`

Doc:

Right anomaly commutator `χ_R = [P_D, P_R]`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_bfaa8edb4469b74336d61e0011d47ac1f180a961`
- SCC: `scc_8e307615e476e5b6a686aea6b4bfc2bbc9f048c6`
- Witness backed: `True`

```lean
-- 60: /-- Left anomaly commutator `χ_L = [P_D, P_L]`. -/
-- 61: abbrev leftAnomalyGenerator : EndH :=
-- 62:   CIK.chiralAnomaly
-- 63: 
-- 64: /-- Right anomaly commutator `χ_R = [P_D, P_R]`. -/
-- 65: abbrev rightAnomalyGenerator : EndH :=
-- 66:   CIK.rightChiralAnomaly
-- 67: 
-- 68: /-- Canonical geometric/dilation identity `Γ_G = 2G`. -/
```

## 8. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.Q_D_mul_GammaS`

- Score: `313.959575`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `113`

Doc:

The Drazin complementary projector is a right `-1` eigen-operator of the spectral grading. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_fc33284c14f8f64ac709245864fa3ab692706c96`
- SCC: `scc_f963501b2270f1a7318e3a4dcd1e7fff3bdf7ac6`
- Witness backed: `True`

```lean
-- 109:     K.GammaS * K.Q_D = -K.Q_D := by
-- 110:   simpa [DPDKKT.GammaS, DPDKKT.Q_D] using
-- 111:     K.kernel.GammaS_mul_spectralComplementaryProjector
-- 112: 
-- 113: /-- The Drazin complementary projector is a right `-1` eigen-operator of the spectral grading. -/
-- 114: theorem Q_D_mul_GammaS :
-- 115:     K.Q_D * K.GammaS = -K.Q_D := by
-- 116:   have hComm : K.Q_D * K.GammaS = K.GammaS * K.Q_D := by
-- 117:     exact (K.kernel.isSpectralCompact_iff_commute_GammaS).1
```

## 9. `InfoGeometry.Canonical.InverseKernel.rightChiralAnomaly_eq_rightProjectorMismatch_commutator_mpRange`

- Score: `313.907627`
- Distance: `None`
- Module: `InfoGeometry.Canonical.InverseKernelAlgebra`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean`
- Line: `93`

Doc:

The right-projector anomaly is exactly the commutator of the right mismatch
with the Moore-Penrose range projector.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_5fdcaef19acbd5e96c218f79f2517a028b9a6af1`
- SCC: `scc_033090e4b31adbb5b7d2e909f65d2682dcef479e`
- Witness backed: `True`

```lean
-- 89:             noncomm_ring
-- 90:     _ = -((2 : ℝ) • IK.dilationGap) := by
-- 91:           rw [IK.projectorMismatch_sub_rightProjectorMismatch_eq_two_smul_dilationGap]
-- 92: 
-- 93: /--
-- 94: The right-projector anomaly is exactly the commutator of the right mismatch
-- 95: with the Moore-Penrose range projector.
-- 96: -/
-- 97: theorem rightChiralAnomaly_eq_rightProjectorMismatch_commutator_mpRange :
```

## 10. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators`

- Score: `312.21571`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `702`

Doc:

The commutator of the Drazin spectral projector with the dilation operator
decomposes into the difference of its commutators with the Moore-Penrose range
and domain projectors.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_316345d0c7b962a4f4675b9337133013d47d62b3`
- SCC: `scc_fbce6e42e04d3ebea9f4a6b8ef75bf08ead3f09e`
- Witness backed: `True`

```lean
-- 698:       = -CI.leftChiralAnomalyOperator := by
-- 699:   simpa [leftChiralAnomalyOperator] using
-- 700:     CI.einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement hProj
-- 701: 
-- 702: /--
-- 703: The commutator of the Drazin spectral projector with the dilation operator
-- 704: decomposes into the difference of its commutators with the Moore-Penrose range
-- 705: and domain projectors.
-- 706: -/
```

## 11. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT`

- Score: `309.807449`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `inductive`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `34`

Doc:

Canonical KKT-style algebra slice already latent in the repo:
a certified inverse kernel together with its spectral/geometric gradings,
dilation gap, mismatch, and left/right anomaly operators.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_741bd8db3081d8ecaf4d2cefb60a8ad0aee4e4dd`
- SCC: `scc_5aafcce3bf00396493f275865dd3b32abc1fea77`
- Witness backed: `True`

```lean
-- 30: /-- Repo-owned anticommutator on the Drazin–Penrose–dilation lane. -/
-- 31: @[rep_depth operator]
-- 32: def anticommutator (X Y : EndH) : EndH := X * Y + Y * X
-- 33: 
-- 34: /--
-- 35: Canonical KKT-style algebra slice already latent in the repo:
-- 36: a certified inverse kernel together with its spectral/geometric gradings,
-- 37: dilation gap, mismatch, and left/right anomaly operators.
-- 38: -/
```

## 12. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.rightSupercharge`

- Score: `309.196314`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `76`

Doc:

Right odd generator / anomaly operator `χ_R = [P_D, P_R]`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_a5359bab3f6f4804f0b8b86d0bc98db807af0578`
- SCC: `scc_f409bb94a395c9d12a947264f14852e5d3848b15`
- Witness backed: `True`

```lean
-- 72: 
-- 73: /-- Left odd generator / anomaly operator `χ_L = [P_D, P_L]`. -/
-- 74: abbrev leftSupercharge : EndH := K.kernel.leftAnomalyGenerator
-- 75: 
-- 76: /-- Right odd generator / anomaly operator `χ_R = [P_D, P_R]`. -/
-- 77: abbrev rightSupercharge : EndH := K.kernel.rightAnomalyGenerator
-- 78: 
-- 79: /-- The repo geometric grading is exactly twice the dilation gap. -/
-- 80: theorem two_smul_G_eq_GammaG :
```

## 13. `InfoGeometry.Canonical.CertifiedInverseKernel.leftAnomalyGenerator`

- Score: `309.030923`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationAlgebra`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationAlgebra.lean`
- Line: `60`

Doc:

Left anomaly commutator `χ_L = [P_D, P_L]`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_f04299f2ef701c50781bc3bef89c72e7dd705622`
- SCC: `scc_5451be67eef610f4d9fe764b56b0fc6e3e97ddd8`
- Witness backed: `True`

```lean
-- 56: /-- Projector mismatch `Δ = P_D - P_L`. -/
-- 57: abbrev projectorMismatchGenerator : EndH :=
-- 58:   CIK.projectorMismatch
-- 59: 
-- 60: /-- Left anomaly commutator `χ_L = [P_D, P_L]`. -/
-- 61: abbrev leftAnomalyGenerator : EndH :=
-- 62:   CIK.chiralAnomaly
-- 63: 
-- 64: /-- Right anomaly commutator `χ_R = [P_D, P_R]`. -/
```

## 14. `InfoGeometry.Canonical.InverseKernel.spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute`

- Score: `307.025183`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CertifiedInverseKernel`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean`
- Line: `130`

Doc:

Right-projector commutation reduces the spectral/dilation commutator to the left anomaly. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_1a22366a2c246541e34ef4c6a9b99d9135010d90`
- SCC: `scc_24c53ed64544e1ef7f9bfd8fd128cb97a13c11f9`
- Witness backed: `True`

```lean
-- 126:   unfold InverseKernel.mpRangeProjector InverseKernel.metricProjector
-- 127:   simp [sub_eq_add_neg]
-- 128:   noncomm_ring
-- 129: 
-- 130: /-- Right-projector commutation reduces the spectral/dilation commutator to the left anomaly. -/
-- 131: theorem spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute
-- 132:     (hRight : IK.spectralProjector * IK.mpRangeProjector = IK.mpRangeProjector * IK.spectralProjector) :
-- 133:     IK.spectralProjector * IK.dilationGap - IK.dilationGap * IK.spectralProjector =
-- 134:       -((2 : ℝ)⁻¹) • IK.chiralAnomaly := by
```

## 15. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.anticommutator_GammaS_rightSupercharge_eq_zero`

- Score: `306.298049`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `159`

Doc:

The right odd generator anticommutes with the spectral grading. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_398c2538d1aa24bae419b99f9084a889972c6d9a`
- SCC: `scc_ccd8f0dbba8854dbd37b86bf2465643d8ef07047`
- Witness backed: `True`

```lean
-- 155:         = K.GammaS * K.leftSupercharge + -(K.GammaS * K.leftSupercharge) := by
-- 156:             rw [hAnti]
-- 157:     _ = 0 := by simp
-- 158: 
-- 159: /-- The right odd generator anticommutes with the spectral grading. -/
-- 160: theorem anticommutator_GammaS_rightSupercharge_eq_zero :
-- 161:     anticommutator K.GammaS K.rightSupercharge = 0 := by
-- 162:   have hAnti :
-- 163:       K.rightSupercharge * K.GammaS = -(K.GammaS * K.rightSupercharge) := by
```

## 16. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_of_projectorAgreement_of_metricProjector_commute`

- Score: `305.987896`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalAnomalySource`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- Line: `412`

Doc:

Structured operator-first dilation/anomaly bridge:
under Moore-Penrose projector agreement and left-metric commutation, the
dilation commutator is exactly minus one half of the projector-obstruction
operator.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_ccc94e28ab1754d2b9166ef20acfce95236e1209`
- SCC: `scc_1d7f079e49fb5e97645d5ce004fd497578f1edec`
- Witness backed: `True`

```lean
-- 408:   simpa [projectorObstruction] using
-- 409:     CI.spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_rightProjector_commute
-- 410:       hRight
-- 411: 
-- 412: /--
-- 413: Structured operator-first dilation/anomaly bridge:
-- 414: under Moore-Penrose projector agreement and left-metric commutation, the
-- 415: dilation commutator is exactly minus one half of the projector-obstruction
-- 416: operator.
```

## 17. `InfoGeometry.Canonical.CertifiedInverseKernel.mpRightProjector`

- Score: `305.944495`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationAlgebra`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationAlgebra.lean`
- Line: `52`

Doc:

Moore-Penrose right projector `P_R`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_22ff76e2a2e9dee69e7590d2e5adcfa7ad14189f`
- SCC: `scc_c08329ac0d22434a879ef668d9c6e214f7f7df3f`
- Witness backed: `True`

```lean
-- 48: /-- Moore-Penrose left projector `P_L`. -/
-- 49: abbrev mpLeftProjector : EndH :=
-- 50:   CIK.mpLeftProj
-- 51: 
-- 52: /-- Moore-Penrose right projector `P_R`. -/
-- 53: abbrev mpRightProjector : EndH :=
-- 54:   CIK.mpRightProj
-- 55: 
-- 56: /-- Projector mismatch `Δ = P_D - P_L`. -/
```

## 18. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.Delta`

- Score: `303.778188`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `70`

Doc:

Projector mismatch `Δ = P_D - P_L`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_955882867d0f6e7ba1d4baacd0cfacb97c8f2a27`
- SCC: `scc_495b8ad6c8a26291c31d5139d8c7f5138e1338aa`
- Witness backed: `True`

```lean
-- 66: 
-- 67: /-- Dilation gap `G = (1/2) (P_R - P_L)`. -/
-- 68: noncomputable abbrev G : EndH := K.kernel.dilationGenerator
-- 69: 
-- 70: /-- Projector mismatch `Δ = P_D - P_L`. -/
-- 71: abbrev Delta : EndH := K.kernel.projectorMismatchGenerator
-- 72: 
-- 73: /-- Left odd generator / anomaly operator `χ_L = [P_D, P_L]`. -/
-- 74: abbrev leftSupercharge : EndH := K.kernel.leftAnomalyGenerator
```

## 19. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.leftSupercharge`

- Score: `302.751038`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `73`

Doc:

Left odd generator / anomaly operator `χ_L = [P_D, P_L]`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_8186567d6b55ceda85988e0a74761a430b22c632`
- SCC: `scc_3f6ced7951598289191e950f8dc70c67428dc60a`
- Witness backed: `True`

```lean
-- 69: 
-- 70: /-- Projector mismatch `Δ = P_D - P_L`. -/
-- 71: abbrev Delta : EndH := K.kernel.projectorMismatchGenerator
-- 72: 
-- 73: /-- Left odd generator / anomaly operator `χ_L = [P_D, P_L]`. -/
-- 74: abbrev leftSupercharge : EndH := K.kernel.leftAnomalyGenerator
-- 75: 
-- 76: /-- Right odd generator / anomaly operator `χ_R = [P_D, P_R]`. -/
-- 77: abbrev rightSupercharge : EndH := K.kernel.rightAnomalyGenerator
```

## 20. `InfoGeometry.Canonical.CertifiedInverseKernel.projectorMismatchGenerator`

- Score: `302.07`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationAlgebra`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationAlgebra.lean`
- Line: `56`

Doc:

Projector mismatch `Δ = P_D - P_L`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_d6ac0437c91ad552ce56af6a91adee7547f2b1b4`
- SCC: `scc_1b87cfa9b673fed54751f05358ac42d59d956112`
- Witness backed: `True`

```lean
-- 52: /-- Moore-Penrose right projector `P_R`. -/
-- 53: abbrev mpRightProjector : EndH :=
-- 54:   CIK.mpRightProj
-- 55: 
-- 56: /-- Projector mismatch `Δ = P_D - P_L`. -/
-- 57: abbrev projectorMismatchGenerator : EndH :=
-- 58:   CIK.projectorMismatch
-- 59: 
-- 60: /-- Left anomaly commutator `χ_L = [P_D, P_L]`. -/
```

## 21. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_neg_half_einstein_plus_chiral`

- Score: `301.082545`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `734`

Doc:

Bridge identity between the singular/right-projector anomaly convention and the
conformal/left-projector anomaly convention.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_4fcce2fd526550fe1dca8cf9e86875b0cb264efd`
- SCC: `scc_11c0b5e5ffdacb12dd3cc3b7f5c8bc5198176120`
- Witness backed: `True`

```lean
-- 730:   rw [CI.spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators]
-- 731:   simp [chiralAnomalyOperator, chiralAnomaly, P_MP, metricChiralProjector,
-- 732:     IsMoorePenroseInverse.leftProjector]
-- 733: 
-- 734: /--
-- 735: Bridge identity between the singular/right-projector anomaly convention and the
-- 736: conformal/left-projector anomaly convention.
-- 737: -/
-- 738: theorem spectralProjector_commutator_dilation_eq_neg_half_einstein_plus_chiral :
```

## 22. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.P_D_mul_GammaS`

- Score: `300.16425`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `97`

Doc:

The Drazin projector is a right `+1` eigen-operator of the spectral grading. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_c628b2df3fc47c30a286aec588a462b93540b43a`
- SCC: `scc_21a7df11c4d3f4095f9a9a70985ddbc9415072c5`
- Witness backed: `True`

```lean
-- 93:     K.GammaS * K.P_D = K.P_D := by
-- 94:   simpa [DPDKKT.GammaS, DPDKKT.P_D] using
-- 95:     K.kernel.GammaS_mul_spectralProjector
-- 96: 
-- 97: /-- The Drazin projector is a right `+1` eigen-operator of the spectral grading. -/
-- 98: theorem P_D_mul_GammaS :
-- 99:     K.P_D * K.GammaS = K.P_D := by
-- 100:   have hComm : K.P_D * K.GammaS = K.GammaS * K.P_D := by
-- 101:     exact (K.kernel.isSpectralCompact_iff_commute_GammaS).1
```

## 23. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.anticommutator_GammaS_leftSupercharge_eq_zero`

- Score: `299.701317`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `145`

Doc:

The left odd generator anticommutes with the spectral grading. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_0a6d3bfe314c5882c9340a5a71f86788260e8fea`
- SCC: `scc_6f1e02c01d4ff9158d1c723855f57ed6db854d9d`
- Witness backed: `True`

```lean
-- 141:   simpa [commutator, DPDKKT.P_D, DPDKKT.G, DPDKKT.rightSupercharge,
-- 142:     DPDKKT.leftSupercharge] using
-- 143:     K.kernel.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies
-- 144: 
-- 145: /-- The left odd generator anticommutes with the spectral grading. -/
-- 146: theorem anticommutator_GammaS_leftSupercharge_eq_zero :
-- 147:     anticommutator K.GammaS K.leftSupercharge = 0 := by
-- 148:   have hAnti :
-- 149:       K.leftSupercharge * K.GammaS = -(K.GammaS * K.leftSupercharge) := by
```

## 24. `InfoGeometry.Canonical.CertifiedInverseKernel.mpLeftProjector`

- Score: `299.507645`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationAlgebra`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationAlgebra.lean`
- Line: `48`

Doc:

Moore-Penrose left projector `P_L`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_272180a4075fb50c0b6804148b4a419499bb0d28`
- SCC: `scc_4dd8ec4299d73751f98a885addb4c12ce0f17d4b`
- Witness backed: `True`

```lean
-- 44: /-- Drazin projector `P_D`. -/
-- 45: abbrev drazinProjector : EndH :=
-- 46:   CIK.drazinCoreProj
-- 47: 
-- 48: /-- Moore-Penrose left projector `P_L`. -/
-- 49: abbrev mpLeftProjector : EndH :=
-- 50:   CIK.mpLeftProj
-- 51: 
-- 52: /-- Moore-Penrose right projector `P_R`. -/
```

## 25. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.singularEinsteinAnomaly_eq_neg_leftChiralAnomaly_of_projectorAgreement`

- Score: `299.026549`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `689`

Doc:

Under left/right Moore-Penrose projector agreement, the singular Einstein
anomaly is the negative of the canonical left-projector anomaly `χ_L`.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_27c2621c5aa6f4b2484e0602534a2f354d06038a`
- SCC: `scc_bc0243efa60e98e0712b34743d7a83b3d1455289`
- Witness backed: `True`

```lean
-- 685:     InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D = -CI.chiralAnomalyOperator := by
-- 686:   rw [CI.einsteinAnomaly_eq_neg_rightChiralAnomaly]
-- 687:   simp [rightChiralAnomaly, chiralAnomalyOperator, chiralAnomaly, P_D, P_MP_right, P_MP, hProj]
-- 688: 
-- 689: /--
-- 690: Under left/right Moore-Penrose projector agreement, the singular Einstein
-- 691: anomaly is the negative of the canonical left-projector anomaly `χ_L`.
-- 692: -/
-- 693: theorem singularEinsteinAnomaly_eq_neg_leftChiralAnomaly_of_projectorAgreement
```

## 26. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_neg_half_leftChiralAnomaly_of_rightProjector_commute`

- Score: `298.257963`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `767`

Doc:

Right-projector commutation collapse, explicitly labeled by the canonical
left-projector anomaly `χ_L`.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_85e80828ace79d6f9b6acfc0c7021b9ce6c47df0`
- SCC: `scc_419923eab8b0cc8ce77e3e838bc364090a14d158`
- Witness backed: `True`

```lean
-- 763:     simpa [P_MP_right] using hRight
-- 764:   rw [hRightComm]
-- 765:   simp [sub_eq_add_neg, chiralAnomalyOperator, smul_sub, smul_neg]
-- 766: 
-- 767: /--
-- 768: Right-projector commutation collapse, explicitly labeled by the canonical
-- 769: left-projector anomaly `χ_L`.
-- 770: -/
-- 771: theorem spectralProjector_commutator_dilation_eq_neg_half_leftChiralAnomaly_of_rightProjector_commute
```

## 27. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.rightSupercharge_isSpectralNonCompact`

- Score: `296.675094`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `180`

Doc:

The right odd generator lies in the spectral noncompact sector. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_1e42803dbda2203e91fdf569f6e6e9d202d22c6b`
- SCC: `scc_9d35f7dcb9fd2f5174e1120c010f413e433a2386`
- Witness backed: `True`

```lean
-- 176:     T.IsSpectralNonCompact K.leftSupercharge := by
-- 177:   simpa [DPDKKT.leftSupercharge] using
-- 178:     K.kernel.chiralAnomaly_isSpectralNonCompact
-- 179: 
-- 180: /-- The right odd generator lies in the spectral noncompact sector. -/
-- 181: theorem rightSupercharge_isSpectralNonCompact :
-- 182:     let T := K.kernel.toInformationCartanTriple
-- 183:     T.IsSpectralNonCompact K.rightSupercharge := by
-- 184:   simpa [DPDKKT.rightSupercharge] using
```

## 28. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.GammaS_mul_Q_D`

- Score: `296.636572`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `107`

Doc:

The Drazin complementary projector is a `-1` eigen-operator of the spectral grading. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_be4f0e394013367397e59c4289e2b673813a075c`
- SCC: `scc_faf5f24610abf2b93210a1785aa681e185ba3853`
- Witness backed: `True`

```lean
-- 103:   calc
-- 104:     K.P_D * K.GammaS = K.GammaS * K.P_D := hComm
-- 105:     _ = K.P_D := K.GammaS_mul_P_D
-- 106: 
-- 107: /-- The Drazin complementary projector is a `-1` eigen-operator of the spectral grading. -/
-- 108: theorem GammaS_mul_Q_D :
-- 109:     K.GammaS * K.Q_D = -K.Q_D := by
-- 110:   simpa [DPDKKT.GammaS, DPDKKT.Q_D] using
-- 111:     K.kernel.GammaS_mul_spectralComplementaryProjector
```

## 29. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.rightChiralAnomaly`

- Score: `295.069601`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `647`

Doc:

Right-projector chiral anomaly.
This is the anomaly built from the Moore-Penrose range projector instead of the
left projector used in `CI.chiralAnomaly`.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_ce6e91975280506fae2b031d1c07805b530c4145`
- SCC: `scc_4eb3c81f4ed69708ec97a5f735ca3113c5b0ab20`
- Witness backed: `True`

```lean
-- 643:     (A := CI.chiralAnomalyOperator)
-- 644:     (CI.chiralAnomalyOperator_isGZero_of_kkt_wings
-- 645:       (X := X) hA hAMP hAD)
-- 646: 
-- 647: /--
-- 648: Right-projector chiral anomaly.
-- 649: This is the anomaly built from the Moore-Penrose range projector instead of the
-- 650: left projector used in `CI.chiralAnomaly`.
-- 651: -/
```

## 30. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.Q_D`

- Score: `295.03556`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `52`

Doc:

Drazin complementary projector. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_09666ffc4a30a5ad62536ba02e3bd447bcbe62a9`
- SCC: `scc_450077d9c2f0385febc1a50429a0327eb501c015`
- Witness backed: `True`

```lean
-- 48: 
-- 49: /-- Drazin spectral projector. -/
-- 50: abbrev P_D : EndH := K.kernel.drazinProjector
-- 51: 
-- 52: /-- Drazin complementary projector. -/
-- 53: abbrev Q_D : EndH := K.kernel.spectralComplementaryProjector
-- 54: 
-- 55: /-- Moore–Penrose range projector. -/
-- 56: abbrev P_R : EndH := K.kernel.mpRightProjector
```

## 31. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.P_D`

- Score: `294.984476`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `49`

Doc:

Drazin spectral projector. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_008b3a9f7adc260164874c93b8e71f03b6fd9c38`
- SCC: `scc_a00bfa29723ea0e76ad9a26c9936e687c088713d`
- Witness backed: `True`

```lean
-- 45: namespace DPDKKT
-- 46: 
-- 47: variable (K : DPDKKT E)
-- 48: 
-- 49: /-- Drazin spectral projector. -/
-- 50: abbrev P_D : EndH := K.kernel.drazinProjector
-- 51: 
-- 52: /-- Drazin complementary projector. -/
-- 53: abbrev Q_D : EndH := K.kernel.spectralComplementaryProjector
```

## 32. `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.rightChiralAnomaly`

- Score: `292.429281`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `140`

Doc:

Certified right-projector anomaly commutator. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_cf3354cbcd4b7d10c26af09dc3f031940768d687`
- SCC: `scc_42157c18c4ee420904d201fc1a597da4c8aebe7e`
- Witness backed: `True`

```lean
-- 136: 
-- 137: @[simp] theorem projectorObstructionOperator_eq_chiralAnomalyOperator :
-- 138:     CCI.projectorObstructionOperator = CCI.chiralAnomalyOperator := rfl
-- 139: 
-- 140: /-- Certified right-projector anomaly commutator. -/
-- 141: def rightChiralAnomaly : E →L[ℝ] E :=
-- 142:   CCI.spectralProjector * CCI.mpRangeProjector - CCI.mpRangeProjector * CCI.spectralProjector
-- 143: 
-- 144: /-- Certified operator alias for the right-projector anomaly. -/
```

## 33. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.P_R`

- Score: `218.940039`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `55`

Doc:

Moore–Penrose range projector. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_1d143d3c11747312405d0883e0f904e83bdf6855`
- SCC: `scc_6868717c0de20abcc6b97c244f32a5e44f68ba52`
- Witness backed: `True`

```lean
-- 51: 
-- 52: /-- Drazin complementary projector. -/
-- 53: abbrev Q_D : EndH := K.kernel.spectralComplementaryProjector
-- 54: 
-- 55: /-- Moore–Penrose range projector. -/
-- 56: abbrev P_R : EndH := K.kernel.mpRightProjector
-- 57: 
-- 58: /-- Moore–Penrose domain/metric projector. -/
-- 59: abbrev P_L : EndH := K.kernel.mpLeftProjector
```

## 34. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement`

- Score: `217.97959`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `677`

Doc:

If the Moore-Penrose left and right projectors coincide, then the singular
Einstein anomaly is the negative of the conformal left-projector anomaly.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_5a47b09b2628f4f13f35d9fb1db0e60702cb9339`
- SCC: `scc_f3336b4f386345083de35046f9bf0c2f72d1471a`
- Witness backed: `True`

```lean
-- 673:     InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D
-- 674:       = -CI.rightChiralAnomalyOperator := by
-- 675:   simpa [rightChiralAnomalyOperator] using CI.einsteinAnomaly_eq_neg_rightChiralAnomaly
-- 676: 
-- 677: /--
-- 678: If the Moore-Penrose left and right projectors coincide, then the singular
-- 679: Einstein anomaly is the negative of the conformal left-projector anomaly.
-- 680: -/
-- 681: theorem einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement
```

## 35. `InfoGeometry.Canonical.CertifiedInverseKernel.spectralCartanGenerator`

- Score: `217.279556`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationAlgebra`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationAlgebra.lean`
- Line: `32`

Doc:

Spectral Cartan grading `Γ_S`. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_0c224b3e0fb09a77161cd1d998b702fc5d981ddf`
- SCC: `scc_bbbe290636425d9a489f0eff528e9ebeecc1da66`
- Witness backed: `True`

```lean
-- 28: namespace CertifiedInverseKernel
-- 29: 
-- 30: variable (CIK : CertifiedInverseKernel E)
-- 31: 
-- 32: /-- Spectral Cartan grading `Γ_S`. -/
-- 33: noncomputable abbrev spectralCartanGenerator : EndH :=
-- 34:   CIK.GammaS
-- 35: 
-- 36: /-- Geometric Cartan grading `Γ_G = P_R - P_L`. -/
```

## 36. `InfoGeometry.Canonical.ConformalUnification.StarCertifiedConformalInference.rightChiralAnomaly`

- Score: `217.279556`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `333`

Doc:

Star-certified right-projector anomaly commutator. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_72377c7326a9f38276cbb00d2fa8e63f1597b92f`
- SCC: `scc_9b7527262d715b3a5430f12eb75ba976a9d90bd2`
- Witness backed: `True`

```lean
-- 329: 
-- 330: /-- Explicit star-certified left anomaly operator alias. -/
-- 331: abbrev leftChiralAnomalyOperator : E →L[ℝ] E := SCI.toCertifiedConformalInference.leftChiralAnomalyOperator
-- 332: 
-- 333: /-- Star-certified right-projector anomaly commutator. -/
-- 334: abbrev rightChiralAnomaly : E →L[ℝ] E := SCI.toCertifiedConformalInference.rightChiralAnomaly
-- 335: 
-- 336: /-- Star-certified operator alias for the right anomaly commutator. -/
-- 337: abbrev rightChiralAnomalyOperator : E →L[ℝ] E := SCI.toCertifiedConformalInference.rightChiralAnomalyOperator
```

## 37. `InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute`

- Score: `217.01425`
- Distance: `None`
- Module: `InfoGeometry.Canonical.CertifiedInverseKernel`
- Declaration kind: `theorem`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean`
- Line: `333`

Doc:

Certified right-projector commutation reduction of the spectral/dilation commutator. 

Faithful witness:

- Raw doc: `raw_info_nodes/raw_dddb962a9e1bc09310df65d6c98ce4443fe790c7`
- SCC: `scc_dfce8c2b37eda7cc8e3c5670da73ca0b52c8659d`
- Witness backed: `True`

```lean
-- 329:     CertifiedInverseKernel.rightChiralAnomaly, CertifiedInverseKernel.chiralAnomaly,
-- 330:     CertifiedInverseKernel.toInverseKernel'] using
-- 331:     CIK.toInverseKernel'.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies
-- 332: 
-- 333: /-- Certified right-projector commutation reduction of the spectral/dilation commutator. -/
-- 334: theorem spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute
-- 335:     (hRight : CIK.spectralProjector * CIK.mpRangeProjector = CIK.mpRangeProjector * CIK.spectralProjector) :
-- 336:     CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector =
-- 337:       -((2 : ℝ)⁻¹) • CIK.chiralAnomaly := by
```

## 38. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.toInverseKernel`

- Score: `216.544084`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `28`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_cffe231d9a557137968e63cdbf11e8177c22b634`
- SCC: `scc_d824b4af337cfd2e1a135aa81662f42e270f55d1`
- Witness backed: `True`

```lean
-- 24: Conformal Inference Structure.
-- 25: Formalizes the unification of Conformal Algebra, Generalized Inverses,
-- 26: and Geometric Chirality.
-- 27: -/
-- 28: structure ConformalInference (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
-- 29:     [CompleteSpace E] extends InfoGeometry.Canonical.InverseKernel E where
-- 30: 
-- 31: /--
-- 32: Certified conformal inference package.
```

## 39. `InfoGeometry.Canonical.ConformalUnification.ConformalInference.P_MP_right`

- Score: `216.015872`
- Distance: `None`
- Module: `InfoGeometry.Canonical.ConformalProjectorCore`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- Line: `490`

Doc:

Moore-Penrose range projector.
This is the right-projector convention used by `Singular.EinsteinAnomaly`.


Faithful witness:

- Raw doc: `raw_info_nodes/raw_ae928b6253ab6a8c827973bff9cf46df9f3e273b`
- SCC: `scc_8bc8d3dc3258f7b9403578ac99d04e487cba7c94`
- Witness backed: `True`

```lean
-- 486: 
-- 487: /-- Canonical naming alias for the metric chiral projector. -/
-- 488: abbrev metricChiralProjector : E →L[ℝ] E := CI.P_MP
-- 489: 
-- 490: /--
-- 491: Moore-Penrose range projector.
-- 492: This is the right-projector convention used by `Singular.EinsteinAnomaly`.
-- 493: -/
-- 494: def P_MP_right : E →L[ℝ] E := IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
```

## 40. `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.kernel`

- Score: `215.841996`
- Distance: `None`
- Module: `InfoGeometry.Canonical.DrazinPenroseDilationKKT`
- Declaration kind: `def`
- Representation layer: `None`
- Representation depth: `None`
- Representation slug: `None`
- File: `/home/goutev/repos/info-geometry-lean-fusion/lean/InfoGeometry/Canonical/DrazinPenroseDilationKKT.lean`
- Line: `41`

Faithful witness:

- Raw doc: `raw_info_nodes/raw_42859761619c885405d5a0b739a4abdef295cd7d`
- SCC: `scc_6b717908e2b901489e130a98cdd04a5bc090b31a`
- Witness backed: `True`

```lean
-- 37: dilation gap, mismatch, and left/right anomaly operators.
-- 38: -/
-- 39: structure DPDKKT (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
-- 40:     [CompleteSpace E] where
-- 41:   kernel : CertifiedInverseKernel E
-- 42: 
-- 43: attribute [spine_object] DPDKKT
-- 44: 
-- 45: namespace DPDKKT
```
