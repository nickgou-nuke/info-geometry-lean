# Quarantined Lean Proof Recovery Audit

Scope: every file in `proofs/_deprecated/removed_from_default_2026_06_15/`.

Policy: quarantined files are not active certificates.  This audit records what
is already covered by active Lean modules, what can be recovered as genuine
finite proofs, and what should remain a socket unless a full analytic/categorical
formalization is supplied.

Build baseline after this audit:

```text
cd proofs && lake build -R
Build completed successfully (8199 jobs).
```

## Immediate repaired certificate

- `PolynomialSymmetryOperators.lean` now contains the theorem cited by Chapter 3:

```lean
PolynomialSymmetry.pauliVec_sq
```

This proves the Pauli quadratic closure
`(x σ₁ + y σ₂ + z σ₃)^2 = (x^2+y^2+z^2) I`.

## Per-file recovery map

| Quarantined file | Existing active coverage | Missing/genuine recovery target |
| --- | --- | --- |
| `BiquaternionKANnilpotent.lean` | **PROMOTED** to active `proofs/BiquaternionKANnilpotent.lean`. | Now proves `K_N_is_nilpotent`, `modular_divergence_closes`, and `kan_nilpotent_synthesis`. |
| `BiquaternionLaplaceResolvent.lean` | 2-parameter resolvent proof exists in `BiquaternionMobiusSquashing.resolvent_det` and `resolvent_identity`; Pauli square in `BiquaternionExpClosure.tracelessPauli_sq`. | Recover full 4-parameter determinant/resolvent as finite matrix proof, likely by reusing `tracelessPauli_sq` and replacing old `!![...]` syntax. |
| `BiquaternionLogarithmMonodromy.lean` | `BiquaternionExpClosure.tracelessPauli_sq`; negative roots in `BiquaternionNegativeRootsLog`; Artin closure in `BraidNegativeIdentityMonodromy`. | Add normalized positive/negative Pauli square lemmas to active biquaternion module. Keep analytic logarithm branch interpretation as socket. |
| `CayleySchreierGauge.lean` | CPT/Pauli atoms exist in `CPTAtom`, `BiquaternionExpClosure`. | Recover finite antiunitary/time-reversal matrix identity as a small matrix theorem; Schreier/gauge interpretation remains socket. |
| `ChiralScratch.lean` | Scratch only. | No recovery target. It should stay deprecated. |
| `CliffordFiveFiveAnomaly.lean` | Superseded by `Clifford55AnomalyOSP.clifford_55_factor_dim`, `anomalyIndex_55_zero`, `osp_atom_anticommutator`, `TripLift_tripotent`. | No need to restore as-is; add aliases only if old theorem names are externally cited. |
| `CliffordInductiveTripotent.lean` | Tripotent anchors in `CubicJordanPeirceDecomposition.Pcanonical_is_tripotent`, `SuperBerezinianKlein`. | Recover Kronecker/tensor tripotency as a finite matrix theorem if needed; otherwise socket for infinite inductive tower. |
| `CptFractalClosure.lean` | **PROMOTED** to active `proofs/CptFractalClosure.lean`. | Now proves `light_cone_nilpotent_plus`, `light_cone_nilpotent_minus`, `conformal_scale_plus`, `conformal_scale_minus`. Fractal closure remains socket. |
| `CptTensorFractal.lean` | No active tensor-nilpotent theorem with that name. | Add finite theorem `(N^2=0) → (N⊗I)^2=0` or concrete 4x4 witness; fractal tensor limit remains socket. |
| `CuntzKriegerKTheory.lean` | `NoncommutativeTilingAlgebra` has K0/gap-label anchors and `CuntzFamily.toAllOnesCK`. | Recover determinant anchors for Penrose/Fibonacci matrices if useful. True K-theory is already socketed. |
| `DiracZeroModes.lean` | Superseded by `DiracResolventZeroModeTripotent.det_sI_minus_X`, `det_D_FM`, `bulk_zero_mode_matches_tripotent_defect`; `DiracFourierMellin.dirac_sq_laplacian`. | Old `tripotent_zero_mode`/`lightcone_dispersion` can be aliases to active theorems. |
| `FinalHolographicThesisSeal.lean` | CPT atoms in `CPTAtom`; thesis seal in `ThesisMaster`/`PublishedThesisArchitecture`; tripotents in `PolynomialSymmetryOperators.T_mat_is_tripotent`. | Do not restore monolithic seal; keep synthesis via active modules. |
| `GravitySoldering.lean` | **PROMOTED** to active `proofs/GravitySoldering.lean`. | Now aliases `CartanWeylBogoliubovGravity.pauli_solder_metric` and proves `metric_00`, `metric_11`, `metric_01`, `gravity_soldering_synthesis`. |
| `HolographicDictionarySynthesis.lean` | Superseded by `InfoGeometry`, `ThesisMaster`, `PublishedThesisArchitecture`. | Keep as deprecated; dictionary is a socket/synthesis, not a standalone proof. |
| `HolographicErlangenCompletion.lean` | CPT atoms in `CPTAtom`; spin determinant in `PublishedThesisArchitecture`; tripotents in `PolynomialSymmetryOperators`. | Recover only finite trace/det/charpoly aliases if cited; Erlangen completion remains socket. |
| `HolographicScaleExtinctions.lean` | Similar active result: `BrillouinKleinNilpotentAttractor.nonzero_fixed_line_mode_not_odd`. | Recover as a finite parity/extinction theorem using `ZMod 2` or integer parity; no analytic claims. |
| `KasparovKreinDoubling.lean` | Krein/Bogoliubov anchors in `DiracKreinMetriplectic`; K-theory sockets in `KasparovKreinCategory`. | Fix `BdG_Matrix` as real/complex 2x2 matrix and prove trace/chiral symmetry. True Kasparov claim remains socket. |
| `KleinGeometrySupergraded.lean` | Glide/eigenspace anchors in `GlideSymmetricInvariant`, `SuperBerezinianKlein.pgGlide_sq`. | Recover finite parity composition lemmas if useful. |
| `KleinNilpotentThermo.lean` | Nilpotent/barrier anchors in `InformationGeometricCutoff`, `LogDetSuperKahlerBarrier`. | Replace unavailable matrix exponential import with finite identity `N^2=0 → exp₂(N)=I+N`; analytic exponential remains socket. |
| `LiuCollinsAffineInvariance.lean` | Projective/affine invariance covered in `ProjectivePenrosePGA.affine_crossRatio_invariant`. | Recover simple reflection/scaling commutation as finite matrix proof if cited. |
| `NonOrientableBraid.lean` | Better finite anchors in `ArtinCentralizerMonodromy`, `ArtinMonodromyPin55`, `ExceptionalKleinGlideEP`. | Old abelian charge accumulation should be replaced by current Artin/Klein word theorems. |
| `OctonionMatrixObstruction.lean` | Split/Zorn finite anchors exist in `OctonionMatrixEncodings`, `SplitOctonionMinkowski`, `ZornScalingFlow`. | Nonassociative obstruction is genuine but needs careful statement. Keep as socket unless proving a concrete associator counterexample. |
| `OctonionicStandardModel.lean` | `Clifford55AnomalyOSP.clifford_55_factor_dim`, `UnifiedGaugeField` sockets. | Dimension/anomaly scalar anchors already active; Standard Model embedding remains socket. |
| `PaperwallDiscreteSUSY.lean` | Supercharge anchors in `SuperchargeSquare`, `GlideSuperchargeCasimir`, `ProjectiveGlideSuperchargeUnification`. | Old theorem names can alias current `Q_sq`, `Q_anticommutator`, glide square roots. |
| `PaperwallSUSY.lean` | CAR/Fock and supercharge finite anchors exist in `CARCCRCantorFock`, `SuperchargeSquare`. | Recover finite CAR nilpotent/anticommutator matrix proofs if not duplicate. |
| `PlatycosmKTheory.lean` | No full active K-theory proof; related topology sockets in projective/Klein modules. | Keep as socket. Do not present `platycosm_k_theory_iso` as a theorem until K-theory machinery is formalized. |
| `ProjectiveCrystalTopology.lean` | Projective crystal anchors in `ProjectiveCrystalKappa`, `ProjectiveCrystalMackeyDecomposition`, `ProjectiveKappaKleinMobius`. | Replace by aliases to `kMirrorGlide_sq`, `kappaM_square_in_lattice`, or current synthesis theorem. |
| `ProjectiveSymmetryAlgebra.lean` | Cocycle anchor exists in `ProjectiveCrystalMackeyDecomposition.signFactor_cocycle`. | Recover abstract associativity-implies-cocycle theorem if useful; finite Z2Pair cocycle already active. |
| `RGFixedPoint.lean` | Squashing/fixed point anchors in `BiquaternionMobiusSquashing.scalarCayley_fixed_poly_of_fixed`, `FredholmModularRegularization`. | Recover tiny 2x2 boost/Bures closure only if cited; RG physical claim remains socket. |
| `RP3Octupole.lean` | Related projective/Klein topology anchors active. | Needs rewrite away from unavailable `Real.pi`; can recover finite reflection/permutation identity. |
| `SouriauGaussian.lean` | Stronger active module: `SouriauBiquaternionGaussian.Bβ_det`, `Bβ_square_closed`, `Bβ_char`. | No restore needed except aliases. |
| `SplitOctonionNilpotent.lean` | Zorn/split-octonion anchors active in `ZornParavectorNullspace`, `SplitOctonionMinkowski`, `OctonionMatrixEncodings`. | Recover concrete `Z_mode_nonzero`, `Z_mode_nilpotent`, `Z_mode_null` if not duplicate. |
| `TripotentPenroseHolography.lean` | Tripotent active anchors in `PolynomialSymmetryOperators.T_mat_is_tripotent`, `SuperBerezinianKlein`, Penrose matrix anchors in `ProjectivePenrosePGA`/`NoncommutativeTilingAlgebra`. | Recover Penrose trace/determinant if cited; holography remains socket. |
| `TwistedHeckeKleinBottle.lean` | Klein/glide active anchors in `SuperBerezinianKlein.pgGlide_sq`, `ExceptionalKleinGlideEP`, `GlideModularJ`. | Recover finite orientation-reversal affine map theorem; Hecke interpretation remains socket. |
| `WallpaperClassification.lean` | Crystallographic obstruction active in thesis/`ThesisMaster.five_not_crystallographic_order`; related wallpaper modules active. | Recover exact valid-order theorem as finite integer/trig-free arithmetic if cited. |
| `WallpaperIsometry.lean` | **PROMOTED** to active `proofs/WallpaperIsometry.lean`. | Now proves `glide_sq_is_translation` and `reflectionX_sq` by finite affine function extensionality. |
| `WallpaperSemidirectProduct.lean` | Wallpaper/group sockets and finite projective cocycles active elsewhere. | Recover semidirect product composition theorem only after fixing old syntax; otherwise keep socket. |

## Suggested promotion order

1. Alias/supersede-only modules: `CliffordFiveFiveAnomaly`, `DiracZeroModes`,
   `SouriauGaussian`, `PaperwallDiscreteSUSY`, `ProjectiveCrystalTopology`.
2. Remaining small finite matrix repairs: `CuntzKriegerKTheory`,
   plus optional aliases for promoted modules if old theorem names are cited.
3. Medium algebraic repairs: `BiquaternionLaplaceResolvent`,
   `BiquaternionLogarithmMonodromy`, `KasparovKreinDoubling`,
   `SplitOctonionNilpotent`.
4. Keep socket/deprecated unless major infrastructure is added:
   `PlatycosmKTheory`, `HolographicDictionarySynthesis`,
   `HolographicErlangenCompletion`, `OctonionicStandardModel`, full
   nonassociative obstruction/standard-model/platycosm K-theory claims.
