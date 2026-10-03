# external_refs/auto vs nickgou-nuke/auto formalization audit

Generated from live local repository state. No SSH private key material was read or printed; SSH was used only through `git ls-remote` / existing git refs.

## 1. Git state comparison

- local path: `/home/goutev/repos/info-geometry-lean/external_refs/auto`
- local branch: `main`
- local HEAD: `f84764108e96fa86bfa875cf3b954877823f940e`
- origin/main / github.com:nickgou-nuke/auto.git HEAD: `89fa975235fb942672bb74980aa40c761bff72ad`
- ahead/behind `HEAD...origin/main`: `0	11` (local ahead, remote ahead)
- local worktree is dirty; do not merge/pull until these are handled.

### Remote commits not in local HEAD
```text
89fa975 Document theorem-honest refactor roadmap in README
787e144 Update README with final Holographic Quasicrystal architecture state
e444c90 Add THEOREM_MAP.md classifying all manuscript claims
fa0e5ac Refine V2 Architecture Plan with theorem-honest academic framing
67d6974 Add V2 Architecture Plan and Roadmap
9ae2e6a Add refactor plan for thesis architecture
b105da1 Seal holographic thesis formalization
cf37744 Formalized Holographic Quasicrystal Spin Geometry: A Clifford-Cuntz-Krieger Framework
233ac4a Finalize O(5,5) Zorn Matrix framing and Spinor Isomorphism paper
a3802ab revise manuscript representation framing
b481a4a formalize photonic topological braid stack
```

### Local modified/staged tracked files
```text
M	README.md
M	proofs/CuntzKTheoryPairing.lean
M	proofs/CuntzKTheoryPairing.py
A	proofs/GT_FromText.lean
M	proofs/HilbertPolyaBivariant.lean
M	proofs/KanCayley.lean
M	proofs/KasparovKreinCategory.lean
M	proofs/KasparovKreinCategory.py
M	proofs/KreinVacuumKMSBridge.lean
M	proofs/lakefile.toml
M	proofs/test_simp.lean
M	proofs/tomita_kms_v4.lean
M	proofs/tomita_kms_v4.py
```

### Local untracked files
```text
proofs/BraidCliffordIntegration.lean
proofs/FibonacciCliffordBridge.lean
proofs/LieFlowCompilerBridge.lean
proofs/LieFlowMatching.lean
proofs/LieFlowMatching.py
```

## 2. Topic inventory counts

### HEAD

Extension counts: .cfg=3, .css=2, .dot=3, .html=2, .in=2, .js=3, .json=12, .jsx=2, .lean=166, .md=57, .mjs=1, .png=2, .py=196, .sh=11, .svg=4, .toml=2, .ts=9, .txt=5, .vulkan=1, .yml=3
Topic-hit file counts:
- wallpaper_klein_brillouin_glide: 45
- determinant_sign_mobius: 161
- biquaternion_quaternion: 28
- clifford_o55_pin_spin: 113
- group_braid_weyl_root: 166
- sage_gap_galgebra_sympy_hooks: 201
- fibonacci_anyons: 57

### origin/main

Extension counts: .aux=2, .bib=2, .cfg=3, .css=2, .csv=1, .dot=3, .html=2, .in=2, .js=3, .json=15, .jsx=2, .lean=305, .md=67, .mjs=1, .out=2, .pdf=2, .png=2, .py=343, .sh=11, .svg=4
Topic-hit file counts:
- wallpaper_klein_brillouin_glide: 168
- determinant_sign_mobius: 319
- biquaternion_quaternion: 115
- clifford_o55_pin_spin: 230
- group_braid_weyl_root: 327
- sage_gap_galgebra_sympy_hooks: 359
- fibonacci_anyons: 84

## 3. High-value files added on origin/main

- `THE_SPINOR_ISOMORPHISM.tex` — clifford_o55_pin_spin
- `jones_calculus.py` — fibonacci_anyons
- `mzi_braid_synthesis.py` — group_braid_weyl_root
- `nhse_chain_sympy.py` — sage_gap_galgebra_sympy_hooks
- `nonlinear_braid_operator.py` — group_braid_weyl_root
- `proofs/ArtinParityFlowWitness.lean` — group_braid_weyl_root
- `proofs/AtomicCliffordKAN.lean` — clifford_o55_pin_spin
- `proofs/BiquaternionCliffordIso.lean` — biquaternion_quaternion, clifford_o55_pin_spin
- `proofs/BiquaternionExpClosure.lean` — biquaternion_quaternion
- `proofs/BiquaternionKANnilpotent.lean` — biquaternion_quaternion
- `proofs/BiquaternionLaplaceResolvent.lean` — biquaternion_quaternion
- `proofs/BiquaternionLaplaceTripotent.lean` — biquaternion_quaternion
- `proofs/BiquaternionLogarithmMonodromy.lean` — biquaternion_quaternion
- `proofs/BiquaternionMobiusSquashing.lean` — determinant_sign_mobius, biquaternion_quaternion
- `proofs/BiquaternionNegativeRootsLog.lean` — biquaternion_quaternion, group_braid_weyl_root
- `proofs/BraidCliffordIntegration.lean` — clifford_o55_pin_spin, group_braid_weyl_root
- `proofs/BraidNegativeIdentityMonodromy.lean` — group_braid_weyl_root
- `proofs/BrillouinKleinNilpotentAttractor.lean` — wallpaper_klein_brillouin_glide
- `proofs/CartanWeylBogoliubovGravity.lean` — group_braid_weyl_root
- `proofs/Clifford55AnomalyOSP.lean` — clifford_o55_pin_spin
- `proofs/CliffordFiveFiveAnomaly.lean` — clifford_o55_pin_spin
- `proofs/CliffordInductiveTripotent.lean` — clifford_o55_pin_spin
- `proofs/CuntzKriegerFibonacciK.lean` — fibonacci_anyons
- `proofs/DeterminantMoebiusFunctor.lean` — determinant_sign_mobius
- `proofs/ExceptionalBraidTopology.lean` — group_braid_weyl_root
- `proofs/ExceptionalKleinGlideEP.lean` — wallpaper_klein_brillouin_glide
- `proofs/ExceptionalNonorientableTopology.lean` — wallpaper_klein_brillouin_glide
- `proofs/FibonacciCliffordBridge.lean` — clifford_o55_pin_spin, fibonacci_anyons
- `proofs/FixedLineRiemannKlein.lean` — wallpaper_klein_brillouin_glide
- `proofs/FractalKleinSUSYFramework.lean` — wallpaper_klein_brillouin_glide
- `proofs/GlideDiracSelectionRule.lean` — wallpaper_klein_brillouin_glide
- `proofs/GlideModularJ.lean` — wallpaper_klein_brillouin_glide
- `proofs/GlideSuperchargeCasimir.lean` — wallpaper_klein_brillouin_glide
- `proofs/KleinGeometrySupergraded.lean` — wallpaper_klein_brillouin_glide
- `proofs/KleinGrapheneTunneling.lean` — wallpaper_klein_brillouin_glide
- `proofs/KleinNilpotentThermo.lean` — wallpaper_klein_brillouin_glide
- `proofs/LOGICAL_GAP_CLOSURE_PLAN.md` — sage_gap_galgebra_sympy_hooks
- `proofs/LogDetSuperKahlerBarrier.lean` — determinant_sign_mobius
- `proofs/MinkowskiBiquaternion.lean` — biquaternion_quaternion
- `proofs/MobiusWittenIndex.lean` — determinant_sign_mobius
- `proofs/MobiusWittenKleinIndex.lean` — wallpaper_klein_brillouin_glide, determinant_sign_mobius
- `proofs/ModularAutomorphismGroup.lean` — group_braid_weyl_root
- `proofs/ModularGlideCPT.lean` — wallpaper_klein_brillouin_glide
- `proofs/ModularItakuraBiquaternion.lean` — biquaternion_quaternion
- `proofs/MorandiWallpaperCohomology.lean` — wallpaper_klein_brillouin_glide
- `proofs/NonOrientableBraid.lean` — wallpaper_klein_brillouin_glide, group_braid_weyl_root
- `proofs/OpticalAndreevSpinor.lean` — clifford_o55_pin_spin
- `proofs/PaperwallDiscreteSUSY.lean` — wallpaper_klein_brillouin_glide
- `proofs/PaperwallHolographicSUSY.lean` — wallpaper_klein_brillouin_glide
- `proofs/PaperwallSUSY.lean` — wallpaper_klein_brillouin_glide
- `proofs/PentagonPenroseWallpaperFractal.lean` — wallpaper_klein_brillouin_glide, fibonacci_anyons
- `proofs/PlatycosmKTheory.lean` — wallpaper_klein_brillouin_glide
- `proofs/ProjectiveGlideSuperchargeUnification.lean` — wallpaper_klein_brillouin_glide
- `proofs/ProjectiveKappaKleinMobius.lean` — wallpaper_klein_brillouin_glide, determinant_sign_mobius
- `proofs/ProjectiveWallpaperGaugePSA.lean` — wallpaper_klein_brillouin_glide
- `proofs/RelativisticBiquaternionKAN.lean` — biquaternion_quaternion
- `proofs/RiemannKleinDuality.lean` — wallpaper_klein_brillouin_glide
- `proofs/SolderingSpinConnectionBogoliubov.lean` — clifford_o55_pin_spin
- `proofs/SouriauBiquaternionGaussian.lean` — biquaternion_quaternion
- `proofs/SouriauMoebiusCoupling.lean` — determinant_sign_mobius
- `proofs/SpacetimeIsSpin.lean` — clifford_o55_pin_spin
- `proofs/SpinorMonodromySteppingStone.lean` — clifford_o55_pin_spin
- `proofs/SplitOctonionBraidSU3.lean` — group_braid_weyl_root
- `proofs/TitsBruhatBrillouinKlein.lean` — wallpaper_klein_brillouin_glide, group_braid_weyl_root
- `proofs/TripotentCliffordColimit.lean` — clifford_o55_pin_spin
- `proofs/TwistedHeckeKleinBottle.lean` — wallpaper_klein_brillouin_glide, group_braid_weyl_root
- `proofs/UnifiedKleinHolographicArchitecture.lean` — wallpaper_klein_brillouin_glide
- `proofs/VerberckWallpaperFourier.lean` — wallpaper_klein_brillouin_glide
- `proofs/WallpaperBulkAnyonProjection.lean` — wallpaper_klein_brillouin_glide, fibonacci_anyons
- `proofs/WallpaperClassification.lean` — wallpaper_klein_brillouin_glide
- `proofs/WallpaperCohomology.lean` — wallpaper_klein_brillouin_glide
- `proofs/WallpaperFermionSuperconductingGap.lean` — wallpaper_klein_brillouin_glide, sage_gap_galgebra_sympy_hooks
- `proofs/WallpaperIsometry.lean` — wallpaper_klein_brillouin_glide
- `proofs/WallpaperMetamaterialDataset.lean` — wallpaper_klein_brillouin_glide
- `proofs/WallpaperSemidirectProduct.lean` — wallpaper_klein_brillouin_glide
- `proofs/WaveguideEPBraidSpec.lean` — group_braid_weyl_root
- `proofs/Z2NonAbelianBraiding.lean` — group_braid_weyl_root
- `proofs/ZornParavectorNullspace.lean` — biquaternion_quaternion
- `proofs/ZornScalingFlow.lean` — biquaternion_quaternion
- `proofs/ZornScalingFlowOrdered.lean` — biquaternion_quaternion
- `proofs/artin_parity_braid_witness.py` — group_braid_weyl_root
- `proofs/atomic_clifford_kan_sympy.py` — clifford_o55_pin_spin, sage_gap_galgebra_sympy_hooks
- `proofs/biquaternion_clifford_iso.py` — biquaternion_quaternion, clifford_o55_pin_spin
- `proofs/biquaternion_exp_closure.py` — biquaternion_quaternion
- `proofs/biquaternion_kan_nilpotent_sympy.py` — biquaternion_quaternion, sage_gap_galgebra_sympy_hooks
- `proofs/biquaternion_laplace_resolvent_sympy.py` — biquaternion_quaternion, sage_gap_galgebra_sympy_hooks
- `proofs/biquaternion_laplace_tripotent.py` — biquaternion_quaternion
- `proofs/biquaternion_logarithm_monodromy.py` — biquaternion_quaternion
- `proofs/biquaternion_mobius_squashing.py` — determinant_sign_mobius, biquaternion_quaternion
- `proofs/biquaternion_negative_roots_log.py` — biquaternion_quaternion, group_braid_weyl_root
- `proofs/braid_clifford_integration_sympy.py` — clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks
- `proofs/braid_negative_identity_monodromy.py` — group_braid_weyl_root
- `proofs/brillouin_klein_nilpotent_attractor.py` — wallpaper_klein_brillouin_glide
- `proofs/cartan_weyl_bogoliubov_gravity.py` — group_braid_weyl_root
- `proofs/cayley_schreier_gauge_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/clifford_55_anomaly_osp.py` — clifford_o55_pin_spin
- `proofs/clifford_5_5_anomaly_sympy.py` — clifford_o55_pin_spin, sage_gap_galgebra_sympy_hooks
- `proofs/clifford_inductive_tripotent_sympy.py` — clifford_o55_pin_spin, sage_gap_galgebra_sympy_hooks
- `proofs/cpt_atom_signum.py` — determinant_sign_mobius
- `proofs/cpt_atom_signum_sympy.py` — determinant_sign_mobius, sage_gap_galgebra_sympy_hooks
- `proofs/cpt_fractal_closure_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/cpt_tensor_fractal_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/cuntz_krieger_fibonacci_k.py` — fibonacci_anyons
- `proofs/cuntz_krieger_ktheory_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/dirac_fourier_mellin_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/dirac_zero_modes_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/exceptional_doubling_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/exceptional_klein_glide_ep.py` — wallpaper_klein_brillouin_glide
- `proofs/exceptional_nonorientable_topology.py` — wallpaper_klein_brillouin_glide
- `proofs/fibonacci_clifford_bridge_sympy.py` — clifford_o55_pin_spin, sage_gap_galgebra_sympy_hooks, fibonacci_anyons
- `proofs/fixed_line_riemann_klein.py` — wallpaper_klein_brillouin_glide
- `proofs/fractal_klein_susy_framework.py` — wallpaper_klein_brillouin_glide
- `proofs/fredholm_regularization_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/glide_dirac_selection_rule.py` — wallpaper_klein_brillouin_glide
- `proofs/glide_modular_j.py` — wallpaper_klein_brillouin_glide
- `proofs/glide_supercharge_casimir.py` — wallpaper_klein_brillouin_glide
- `proofs/grand_holographic_theorem_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/gravity_soldering_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/holographic_dictionary_synthesis_sympy.py` — sage_gap_galgebra_sympy_hooks
- `proofs/holographic_scale_extinctions_sympy.py` — sage_gap_galgebra_sympy_hooks

## 4. Debt signals in topic Lean files

### HEAD

- `external_refs/braids_better/BraidProject/Cancellability.lean` — topics=group_braid_weyl_root; theorem/lemma=8; def/struct=0; sorry=2
- `external_refs/braids_better/BraidProject/GridsTwo.lean` — topics=group_braid_weyl_root; theorem/lemma=12; def/struct=6; sorry=2
- `external_refs/braids_better/BraidProject/PartialGrids.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=8; def/struct=9; no grep debt
- `external_refs/braids_better/BraidProject/Reversing.lean` — topics=group_braid_weyl_root; theorem/lemma=5; def/struct=6; sorry=4
- `external_refs/braids_better/BraidProject/Stability.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=11; def/struct=1; no grep debt
- `formal-theory-quantum.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=2; def/struct=11; no grep debt
- `formal-theory.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=6; def/struct=3; no grep debt
- `proofs/ASTExtractor.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=0; def/struct=3; no grep debt
- `proofs/AnomalousKMSFlow.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=22; def/struct=14; no grep debt
- `proofs/BostConnesDeformation.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=23; def/struct=27; no grep debt
- `proofs/CanonicalSouriauPauliThermodynamics.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=16; def/struct=18; no grep debt
- `proofs/ChiralTwistedFibration.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks, fibonacci_anyons; theorem/lemma=37; def/struct=30; no grep debt
- `proofs/ComplexTemperatureRH.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=11; def/struct=18; no grep debt
- `proofs/ConcreteCliffordDiracTower.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=8; def/struct=7; no grep debt
- `proofs/ConnesSpectralAction.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=5; def/struct=1; no grep debt
- `proofs/Crystallographic.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=1; def/struct=0; no grep debt
- `proofs/DeterminantSupergrading.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius; theorem/lemma=21; def/struct=7; no grep debt
- `proofs/DiracColimit.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=5; def/struct=4; no grep debt
- `proofs/FenchelSpacetime.lean` — topics=clifford_o55_pin_spin; theorem/lemma=9; def/struct=1; no grep debt
- `proofs/FockSpaceDerivation.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=1; def/struct=7; no grep debt
- `proofs/FureyZornFermionBridge.lean` — topics=biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=5; def/struct=6; no grep debt
- `proofs/GeometricZeta.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=6; def/struct=8; no grep debt
- `proofs/HilbertPolyaBivariant.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=3; def/struct=2; no grep debt
- `proofs/HurwitzQuaternionSpectrum.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=16; def/struct=17; no grep debt
- `proofs/HurwitzTwistedSector.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=29; def/struct=21; no grep debt
- `proofs/J_duality_chain.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=19; def/struct=7; no grep debt
- `proofs/KleinBottle.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=12; def/struct=7; no grep debt
- `proofs/KleinBottleKANCoordinates.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius; theorem/lemma=4; def/struct=4; no grep debt
- `proofs/KleinBottleParafermionInvariant.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=1; def/struct=0; no grep debt
- `proofs/KleinBottleSymmetry.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=2; def/struct=0; no grep debt
- `proofs/KleinFourAnomalyCancellation.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=3; def/struct=8; no grep debt
- `proofs/KleinParafermionCohomology.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=9; def/struct=4; no grep debt
- `proofs/KreinVacuumKMSBridge.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=7; def/struct=1; axiom=2
- `proofs/KreinVacuumPropagator.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=12; def/struct=6; no grep debt
- `proofs/PartitionPoleCriterion.lean` — topics=clifford_o55_pin_spin; theorem/lemma=8; def/struct=7; no grep debt
- `proofs/PauliZornTrifactor.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=12; def/struct=12; no grep debt
- `proofs/PenroseArithmetic.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=18; def/struct=15; no grep debt
- `proofs/PrimonCuntzTower.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=23; def/struct=18; no grep debt
- `proofs/RiemannHypothesis.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=15; def/struct=22; no grep debt
- `proofs/RunExtractor.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=0; def/struct=0; no grep debt
- `proofs/SolderingForms.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=25; def/struct=10; no grep debt
- `proofs/SolderingRoundTrip.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=8; def/struct=6; no grep debt
- `proofs/SouriauHestenesKrein.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=13; def/struct=11; no grep debt
- `proofs/SouriauHestenesMobiusPole.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=12; def/struct=12; no grep debt
- `proofs/SouriauThermoColimit.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=14; def/struct=29; no grep debt
- `proofs/SpectralYangBaxter.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=8; def/struct=6; no grep debt
- `proofs/TestImport2.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=0; def/struct=0; no grep debt
- `proofs/TestImportKB.lean` — topics=wallpaper_klein_brillouin_glide; theorem/lemma=0; def/struct=0; no grep debt
- `proofs/TransformsAndScale.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=9; def/struct=7; no grep debt
- `proofs/TrifactorGeometry.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=10; def/struct=10; no grep debt
- `proofs/ZetaSpectralBridge.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=15; def/struct=10; no grep debt
- `proofs/ZornAssociatorSplitOctonion.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=13; def/struct=17; no grep debt
- `proofs/ZornOPParavector.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=14; def/struct=11; no grep debt
- `proofs/_deprecated/FibAnyonThm4_bridge.lean` — topics=group_braid_weyl_root, sage_gap_galgebra_sympy_hooks, fibonacci_anyons; theorem/lemma=6; def/struct=6; sorry=4
- `proofs/_deprecated/test_tl.lean` — topics=fibonacci_anyons; theorem/lemma=1; def/struct=4; sorry=1
- `proofs/_deprecated/test_tl2.lean` — topics=fibonacci_anyons; theorem/lemma=1; def/struct=4; sorry=1
- `proofs/bridge_full.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=6; def/struct=12; no grep debt
- `proofs/clifford_seed.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=6; def/struct=5; no grep debt
- `proofs/determinant_weyl_gauge.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=42; def/struct=24; no grep debt
- `proofs/goutev_principle.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=5; def/struct=39; no grep debt
- `proofs/penrose_wallpaper_colimit.lean` — topics=wallpaper_klein_brillouin_glide, clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks, fibonacci_anyons; theorem/lemma=6; def/struct=22; no grep debt
- `proofs/primon_system.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=12; def/struct=7; no grep debt
- `proofs/rigorous_proofs.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=31; def/struct=10; no grep debt
- `proofs/tomita_kms_v4.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=4; def/struct=10; no grep debt
- `proofs/uhf_cantor_boundary.lean` — topics=biquaternion_quaternion; theorem/lemma=3; def/struct=10; no grep debt
- `proofs/uhf_ladder.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=12; def/struct=12; no grep debt
- `proofs/zeta_zeros_moebius_klein.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=13; def/struct=11; no grep debt

### origin/main

- `external_refs/braids_better/BraidProject/Cancellability.lean` — topics=group_braid_weyl_root; theorem/lemma=8; def/struct=0; sorry=2
- `external_refs/braids_better/BraidProject/GridsTwo.lean` — topics=group_braid_weyl_root; theorem/lemma=12; def/struct=6; sorry=2
- `external_refs/braids_better/BraidProject/PartialGrids.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=8; def/struct=9; no grep debt
- `external_refs/braids_better/BraidProject/Reversing.lean` — topics=group_braid_weyl_root; theorem/lemma=5; def/struct=6; sorry=4
- `external_refs/braids_better/BraidProject/Stability.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=11; def/struct=1; no grep debt
- `formal-theory-quantum.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=2; def/struct=11; no grep debt
- `formal-theory.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=6; def/struct=3; no grep debt
- `proofs/ASTExtractor.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=0; def/struct=3; no grep debt
- `proofs/AnomalousKMSFlow.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=22; def/struct=14; no grep debt
- `proofs/ArtinParityFlowWitness.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=11; def/struct=10; no grep debt
- `proofs/AtomicCliffordKAN.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=18; def/struct=16; no grep debt
- `proofs/BiquaternionCliffordIso.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin; theorem/lemma=19; def/struct=7; no grep debt
- `proofs/BiquaternionExpClosure.lean` — topics=biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=2; def/struct=6; no grep debt
- `proofs/BiquaternionKANnilpotent.lean` — topics=biquaternion_quaternion; theorem/lemma=2; def/struct=2; no grep debt
- `proofs/BiquaternionLaplaceResolvent.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=2; def/struct=4; no grep debt
- `proofs/BiquaternionLaplaceTripotent.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=10; def/struct=12; no grep debt
- `proofs/BiquaternionLogarithmMonodromy.lean` — topics=biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=6; def/struct=5; no grep debt
- `proofs/BiquaternionMobiusSquashing.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=8; def/struct=12; no grep debt
- `proofs/BiquaternionNegativeRootsLog.lean` — topics=biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=6; def/struct=5; no grep debt
- `proofs/BogoliubovFrameTransport.lean` — topics=clifford_o55_pin_spin; theorem/lemma=13; def/struct=8; no grep debt
- `proofs/BostConnesDeformation.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=23; def/struct=27; no grep debt
- `proofs/BraidCliffordIntegration.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks, fibonacci_anyons; theorem/lemma=24; def/struct=19; no grep debt
- `proofs/BraidNegativeIdentityMonodromy.lean` — topics=biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=7; def/struct=4; no grep debt
- `proofs/BrillouinKleinNilpotentAttractor.lean` — topics=wallpaper_klein_brillouin_glide, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=9; def/struct=15; no grep debt
- `proofs/CPTAtom.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=8; def/struct=10; no grep debt
- `proofs/CanonicalSouriauPauliThermodynamics.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=16; def/struct=18; no grep debt
- `proofs/CartanWeylBogoliubovGravity.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=5; def/struct=18; no grep debt
- `proofs/CayleySchreierGauge.lean` — topics=biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=1; def/struct=9; no grep debt
- `proofs/ChiralTwistedFibration.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks, fibonacci_anyons; theorem/lemma=37; def/struct=30; no grep debt
- `proofs/Clifford55AnomalyOSP.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=11; def/struct=12; no grep debt
- `proofs/CliffordFiveFiveAnomaly.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=3; def/struct=0; no grep debt
- `proofs/CliffordInductiveTripotent.lean` — topics=clifford_o55_pin_spin; theorem/lemma=1; def/struct=1; no grep debt
- `proofs/CompleteHolographicDictionary.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=11; def/struct=14; no grep debt
- `proofs/ComplexTemperatureRH.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=11; def/struct=18; no grep debt
- `proofs/ConcreteCliffordDiracTower.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=8; def/struct=7; no grep debt
- `proofs/ConnesSpectralAction.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=5; def/struct=1; no grep debt
- `proofs/Crystallographic.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=1; def/struct=0; no grep debt
- `proofs/DeterminantSupergrading.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius; theorem/lemma=21; def/struct=7; no grep debt
- `proofs/DiracColimit.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=5; def/struct=4; no grep debt
- `proofs/DiracFourierMellin.lean` — topics=biquaternion_quaternion, clifford_o55_pin_spin; theorem/lemma=2; def/struct=3; no grep debt
- `proofs/DiracResolventZeroModeTripotent.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=10; def/struct=8; no grep debt
- `proofs/DiracZeroModes.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=3; def/struct=1; no grep debt
- `proofs/ExceptionalBraidTopology.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=3; def/struct=2; no grep debt
- `proofs/ExceptionalKleinGlideEP.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=5; def/struct=5; no grep debt
- `proofs/ExceptionalNonorientableTopology.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=8; def/struct=12; no grep debt
- `proofs/ExceptionalPointMonodromy.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=15; def/struct=7; no grep debt
- `proofs/ExceptionalTopologicalBandStructures.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=10; def/struct=13; no grep debt
- `proofs/FenchelSpacetime.lean` — topics=clifford_o55_pin_spin; theorem/lemma=9; def/struct=1; no grep debt
- `proofs/FibonacciCliffordBridge.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, fibonacci_anyons; theorem/lemma=17; def/struct=22; no grep debt
- `proofs/FinalHolographicThesisSeal.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=7; def/struct=8; no grep debt
- `proofs/FixedLineRiemannKlein.lean` — topics=wallpaper_klein_brillouin_glide, biquaternion_quaternion; theorem/lemma=7; def/struct=10; no grep debt
- `proofs/FockSpaceDerivation.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=1; def/struct=7; no grep debt
- `proofs/FractalKleinSUSYFramework.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=11; def/struct=6; no grep debt
- `proofs/FredholmModularRegularization.lean` — topics=biquaternion_quaternion, sage_gap_galgebra_sympy_hooks; theorem/lemma=5; def/struct=8; no grep debt
- `proofs/FureyZornFermionBridge.lean` — topics=biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=5; def/struct=6; no grep debt
- `proofs/GT_FromText.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=0; def/struct=30; axiom=12
- `proofs/GeometricZeta.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=6; def/struct=8; no grep debt
- `proofs/GlideDiracSelectionRule.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius; theorem/lemma=11; def/struct=3; no grep debt
- `proofs/GlideModularJ.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=7; def/struct=4; no grep debt
- `proofs/GlideSuperchargeCasimir.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=6; def/struct=13; no grep debt
- `proofs/GrandHolographicLoop.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin; theorem/lemma=11; def/struct=17; no grep debt
- `proofs/GrandHolographicTheorem.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=13; def/struct=12; true_trivial=1
- `proofs/HilbertPolyaBivariant.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=3; def/struct=2; no grep debt
- `proofs/HolographicDictionarySynthesis.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin; theorem/lemma=1; def/struct=0; no grep debt
- `proofs/HolographicErlangenCompletion.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=9; def/struct=12; no grep debt
- `proofs/HolographicScaleExtinctions.lean` — topics=wallpaper_klein_brillouin_glide; theorem/lemma=3; def/struct=2; no grep debt
- `proofs/HurwitzQuaternionSpectrum.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=16; def/struct=17; no grep debt
- `proofs/HurwitzTwistedSector.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=29; def/struct=21; no grep debt
- `proofs/J_duality_chain.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=19; def/struct=7; no grep debt
- `proofs/KANFourierMellinDirac.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=8; def/struct=14; no grep debt
- `proofs/KasparovKreinDoubling.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=2; def/struct=3; sorry=1
- `proofs/KleinBottle.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=12; def/struct=7; no grep debt
- `proofs/KleinBottleKANCoordinates.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius; theorem/lemma=4; def/struct=4; no grep debt
- `proofs/KleinBottleParafermionInvariant.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=1; def/struct=0; no grep debt
- `proofs/KleinBottleSymmetry.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=2; def/struct=0; no grep debt
- `proofs/KleinFourAnomalyCancellation.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=3; def/struct=8; no grep debt
- `proofs/KleinGeometrySupergraded.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=4; def/struct=2; no grep debt
- `proofs/KleinGrapheneTunneling.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=10; def/struct=9; no grep debt
- `proofs/KleinNilpotentThermo.lean` — topics=wallpaper_klein_brillouin_glide; theorem/lemma=2; def/struct=2; sorry=2
- `proofs/KleinParafermionCohomology.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=9; def/struct=4; no grep debt
- `proofs/KreinVacuumKMSBridge.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=7; def/struct=1; axiom=2
- `proofs/KreinVacuumPropagator.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=12; def/struct=6; no grep debt
- `proofs/LieFlowMatching.lean` — topics=group_braid_weyl_root; theorem/lemma=5; def/struct=8; axiom=1
- `proofs/LiuCollinsAffineInvariance.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=2; def/struct=3; no grep debt
- `proofs/LogDetSuperKahlerBarrier.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=6; def/struct=7; no grep debt
- `proofs/MinkowskiBiquaternion.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=3; def/struct=2; no grep debt
- `proofs/MobiusWittenKleinIndex.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius; theorem/lemma=8; def/struct=6; no grep debt
- `proofs/ModularGlideCPT.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=3; def/struct=4; no grep debt
- `proofs/ModularHolographicMetric.lean` — topics=biquaternion_quaternion; theorem/lemma=6; def/struct=13; no grep debt
- `proofs/ModularItakuraBiquaternion.lean` — topics=biquaternion_quaternion, sage_gap_galgebra_sympy_hooks; theorem/lemma=6; def/struct=9; no grep debt
- `proofs/MorandiWallpaperCohomology.lean` — topics=wallpaper_klein_brillouin_glide, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=8; def/struct=13; no grep debt
- `proofs/NilpotentItakuraSaito.lean` — topics=biquaternion_quaternion; theorem/lemma=6; def/struct=6; no grep debt
- `proofs/NonHermitianKitaevCuntzChain.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=7; def/struct=7; no grep debt
- `proofs/NonHermitianSMatrixDefect.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=6; def/struct=6; no grep debt
- `proofs/NonInvertiblePenroseCategoricalSymmetry.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=10; def/struct=7; no grep debt
- `proofs/NonOrientableBraid.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=1; def/struct=2; no grep debt
- `proofs/OctonionMatrixEncodings.lean` — topics=biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=5; def/struct=12; no grep debt
- `proofs/OctonionMatrixObstruction.lean` — topics=biquaternion_quaternion; theorem/lemma=4; def/struct=12; no grep debt
- `proofs/OctonionicStandardModel.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=2; def/struct=1; no grep debt
- `proofs/OpticalAndreevSpinor.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=13; def/struct=16; no grep debt
- `proofs/PaperwallDiscreteSUSY.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=5; def/struct=3; no grep debt
- `proofs/PaperwallHolographicSUSY.lean` — topics=wallpaper_klein_brillouin_glide, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=8; def/struct=6; no grep debt
- `proofs/PaperwallSUSY.lean` — topics=wallpaper_klein_brillouin_glide; theorem/lemma=7; def/struct=3; no grep debt
- `proofs/PartitionPoleCriterion.lean` — topics=clifford_o55_pin_spin; theorem/lemma=8; def/struct=7; no grep debt
- `proofs/PauliZornTrifactor.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=12; def/struct=12; no grep debt
- `proofs/PenroseArithmetic.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=18; def/struct=15; no grep debt
- `proofs/PentagonPenroseWallpaperFractal.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=10; def/struct=11; no grep debt
- `proofs/PlatycosmKTheory.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=0; def/struct=3; axiom=1
- `proofs/PolynomialSymmetryOperators.lean` — topics=wallpaper_klein_brillouin_glide, biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=3; def/struct=6; no grep debt
- `proofs/PrimonCuntzTower.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=23; def/struct=18; no grep debt
- `proofs/ProjectiveCrystalKappa.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=7; def/struct=11; no grep debt
- `proofs/ProjectiveCrystalMackeyDecomposition.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius; theorem/lemma=8; def/struct=17; no grep debt
- `proofs/ProjectiveCrystalSymmetry.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=8; def/struct=11; no grep debt
- `proofs/ProjectiveCrystalTopology.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius; theorem/lemma=1; def/struct=0; no grep debt
- `proofs/ProjectiveGlideSuperchargeUnification.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=5; def/struct=12; no grep debt
- `proofs/ProjectiveKappaKleinMobius.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=11; def/struct=16; no grep debt
- `proofs/ProjectiveSymmetryAlgebra.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=1; def/struct=2; no grep debt
- `proofs/ProjectiveWallpaperGaugePSA.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=11; def/struct=21; no grep debt
- `proofs/PublishedThesisArchitecture.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin, sage_gap_galgebra_sympy_hooks; theorem/lemma=8; def/struct=13; no grep debt
- `proofs/RGFixedPoint.lean` — topics=biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=1; def/struct=2; no grep debt
- `proofs/RP3Octupole.lean` — topics=wallpaper_klein_brillouin_glide; theorem/lemma=1; def/struct=5; no grep debt
- `proofs/RelativisticBiquaternionKAN.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin; theorem/lemma=10; def/struct=12; no grep debt
- `proofs/RiemannHypothesis.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=15; def/struct=22; no grep debt
- `proofs/RiemannKleinDuality.lean` — topics=wallpaper_klein_brillouin_glide, clifford_o55_pin_spin; theorem/lemma=2; def/struct=2; no grep debt
- `proofs/RunExtractor.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=0; def/struct=0; no grep debt
- `proofs/ScatteringSMatrix.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=6; def/struct=4; no grep debt
- `proofs/SolderingForms.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=25; def/struct=10; no grep debt
- `proofs/SolderingRoundTrip.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=8; def/struct=6; no grep debt
- `proofs/SolderingSpinConnectionBogoliubov.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin; theorem/lemma=5; def/struct=13; no grep debt
- `proofs/SouriauBiquaternionGaussian.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin; theorem/lemma=6; def/struct=5; no grep debt
- `proofs/SouriauGaussian.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=1; def/struct=2; no grep debt
- `proofs/SouriauHestenesKrein.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=13; def/struct=11; no grep debt
- `proofs/SouriauHestenesMobiusPole.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=12; def/struct=12; no grep debt
- `proofs/SouriauThermoColimit.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=14; def/struct=29; no grep debt
- `proofs/SpacetimeIsSpin.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=7; def/struct=8; no grep debt
- `proofs/SpectralYangBaxter.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=8; def/struct=6; no grep debt
- `proofs/SpinorMonodromySteppingStone.lean` — topics=biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=10; def/struct=7; no grep debt
- `proofs/SplitOctonionBraidSU3.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=11; def/struct=18; no grep debt
- `proofs/SplitOctonionMinkowski.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin; theorem/lemma=13; def/struct=15; no grep debt
- `proofs/SplitOctonionNilpotent.lean` — topics=determinant_sign_mobius, biquaternion_quaternion; theorem/lemma=3; def/struct=12; no grep debt
- `proofs/TestImport2.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=0; def/struct=0; no grep debt
- `proofs/TestImportKB.lean` — topics=wallpaper_klein_brillouin_glide; theorem/lemma=0; def/struct=0; no grep debt
- `proofs/ThesisMaster.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin; theorem/lemma=12; def/struct=16; true_trivial=1
- `proofs/TitsBruhatBrillouinKlein.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=10; def/struct=10; no grep debt
- `proofs/TransformsAndScale.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=9; def/struct=7; no grep debt
- `proofs/TrifactorGeometry.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=10; def/struct=10; no grep debt
- `proofs/TripotentCliffordColimit.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin; theorem/lemma=10; def/struct=13; no grep debt
- `proofs/TripotentPenroseHolography.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, fibonacci_anyons; theorem/lemma=3; def/struct=3; no grep debt
- `proofs/TwistedHeckeKleinBottle.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=3; def/struct=3; no grep debt
- `proofs/UnifiedKleinHolographicArchitecture.lean` — topics=wallpaper_klein_brillouin_glide, biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=3; def/struct=7; no grep debt
- `proofs/VerberckWallpaperFourier.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=8; def/struct=5; no grep debt
- `proofs/WallpaperBulkAnyonProjection.lean` — topics=wallpaper_klein_brillouin_glide, clifford_o55_pin_spin, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=9; def/struct=7; no grep debt
- `proofs/WallpaperClassification.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=1; def/struct=2; no grep debt
- `proofs/WallpaperCohomology.lean` — topics=wallpaper_klein_brillouin_glide, clifford_o55_pin_spin, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=1; def/struct=2; no grep debt
- `proofs/WallpaperFermionSuperconductingGap.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, sage_gap_galgebra_sympy_hooks; theorem/lemma=8; def/struct=14; no grep debt
- `proofs/WallpaperIsometry.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=1; def/struct=6; no grep debt
- `proofs/WallpaperMetamaterialDataset.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=11; def/struct=14; no grep debt
- `proofs/WallpaperSemidirectProduct.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=0; def/struct=2; no grep debt
- `proofs/WaveguideEPBraidSpec.lean` — topics=clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=5; def/struct=6; no grep debt
- `proofs/ZetaSpectralBridge.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=15; def/struct=10; no grep debt
- `proofs/ZornAssociatorSplitOctonion.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=13; def/struct=17; no grep debt
- `proofs/ZornOPParavector.lean` — topics=determinant_sign_mobius, biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=14; def/struct=11; no grep debt
- `proofs/ZornParavectorNullspace.lean` — topics=biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=6; def/struct=11; no grep debt
- `proofs/ZornScalingFlow.lean` — topics=biquaternion_quaternion, group_braid_weyl_root; theorem/lemma=6; def/struct=11; no grep debt
- `proofs/ZornScalingFlowOrdered.lean` — topics=biquaternion_quaternion, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks; theorem/lemma=5; def/struct=11; no grep debt
- `proofs/_deprecated/FibAnyonThm4_bridge.lean` — topics=group_braid_weyl_root, sage_gap_galgebra_sympy_hooks, fibonacci_anyons; theorem/lemma=6; def/struct=6; sorry=4
- `proofs/_deprecated/test_tl.lean` — topics=fibonacci_anyons; theorem/lemma=1; def/struct=4; sorry=1
- `proofs/_deprecated/test_tl2.lean` — topics=fibonacci_anyons; theorem/lemma=1; def/struct=4; sorry=1
- `proofs/bridge_full.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=6; def/struct=12; no grep debt
- `proofs/clifford_seed.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=6; def/struct=5; no grep debt
- `proofs/determinant_weyl_gauge.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=42; def/struct=24; no grep debt
- `proofs/goutev_principle.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, biquaternion_quaternion, clifford_o55_pin_spin, group_braid_weyl_root, fibonacci_anyons; theorem/lemma=5; def/struct=39; no grep debt
- `proofs/penrose_wallpaper_colimit.lean` — topics=wallpaper_klein_brillouin_glide, clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks, fibonacci_anyons; theorem/lemma=6; def/struct=22; no grep debt
- `proofs/primon_system.lean` — topics=wallpaper_klein_brillouin_glide, group_braid_weyl_root; theorem/lemma=12; def/struct=7; no grep debt
- `proofs/rigorous_proofs.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=31; def/struct=10; no grep debt
- `proofs/tomita_kms_v4.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, group_braid_weyl_root; theorem/lemma=4; def/struct=10; no grep debt
- `proofs/uhf_cantor_boundary.lean` — topics=biquaternion_quaternion; theorem/lemma=3; def/struct=10; no grep debt
- `proofs/uhf_ladder.lean` — topics=determinant_sign_mobius, clifford_o55_pin_spin, group_braid_weyl_root; theorem/lemma=12; def/struct=12; no grep debt
- `proofs/zeta_zeros_moebius_klein.lean` — topics=wallpaper_klein_brillouin_glide, determinant_sign_mobius, clifford_o55_pin_spin; theorem/lemma=13; def/struct=11; no grep debt

## 5. Cross-map: origin/main additions vs current info-geometry owner surfaces

### `THE_SPINOR_ISOMORPHISM.tex`
- topics: clifford_o55_pin_spin
  - no obvious current repo filename match; inspect before creating new owner surface
### `jones_calculus.py`
- topics: fibonacci_anyons
  - score 2: `lean/InfoGeometry/Optics/OperatorialJonesCalculus.lean`
  - score 2: `lean/InfoGeometry/OperatorAlgebra/OperatorialJonesCalculus.lean`
### `mzi_braid_synthesis.py`
- topics: group_braid_weyl_root
  - no obvious current repo filename match; inspect before creating new owner surface
### `nhse_chain_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/capstone_bridge_chain.py`
### `nonlinear_braid_operator.py`
- topics: group_braid_weyl_root
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/ArtinParityFlowWitness.lean`
- topics: group_braid_weyl_root
  - score 2: `lean/InfoGeometry/Canonical/ParityTraceWitness.lean`
### `proofs/AtomicCliffordKAN.lean`
- topics: clifford_o55_pin_spin
  - score 1: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 1: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `lean/InfoGeometry/Twistor/CliffordBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/CliffordFractalWaveletBridge.lean`
  - score 1: `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`
  - score 1: `lean/InfoGeometry/Quantum/RealSplitClifford.lean`
### `proofs/BiquaternionCliffordIso.lean`
- topics: biquaternion_quaternion, clifford_o55_pin_spin
  - score 2: `lean/InfoGeometry/Clifford/Cl44C8Comparison.lean`
  - score 2: `lean/InfoGeometry/Clifford/Biquaternion.lean`
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 1: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
### `proofs/BiquaternionExpClosure.lean`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/BiquaternionKANnilpotent.lean`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/BiquaternionLaplaceResolvent.lean`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/BiquaternionLaplaceTripotent.lean`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/BiquaternionLogarithmMonodromy.lean`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/BiquaternionMobiusSquashing.lean`
- topics: determinant_sign_mobius, biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/BiquaternionNegativeRootsLog.lean`
- topics: biquaternion_quaternion, group_braid_weyl_root
  - score 2: `lean/InfoGeometry/Topology/V4RootSystem.lean`
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
### `proofs/BraidCliffordIntegration.lean`
- topics: clifford_o55_pin_spin, group_braid_weyl_root
  - score 3: `lean/InfoGeometry/External/Auto/BraidCliffordIntegration.lean`
  - score 1: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 1: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `lean/InfoGeometry/Twistor/CliffordBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/CliffordFractalWaveletBridge.lean`
  - score 1: `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`
### `proofs/BraidNegativeIdentityMonodromy.lean`
- topics: group_braid_weyl_root
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/BrillouinKleinNilpotentAttractor.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 2: `tools/sympy/transformer_klein_brillouin.py`
  - score 2: `tools/sympy/brillouin_klein_gauge_fields.py`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinGaugeInvariant.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinExceptionalTopology.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinBraid.lean`
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
### `proofs/CartanWeylBogoliubovGravity.lean`
- topics: group_braid_weyl_root
  - score 2: `lean/InfoGeometry/Canonical/BogoliubovCartanFrameInterpretation.lean`
  - score 2: `lean/InfoGeometry/Canonical/BogoliubovCartanEigenOperator.lean`
### `proofs/Clifford55AnomalyOSP.lean`
- topics: clifford_o55_pin_spin
  - score 1: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 1: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `lean/InfoGeometry/Twistor/CliffordBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/CliffordFractalWaveletBridge.lean`
  - score 1: `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`
  - score 1: `lean/InfoGeometry/Quantum/RealSplitClifford.lean`
### `proofs/CliffordFiveFiveAnomaly.lean`
- topics: clifford_o55_pin_spin
  - score 3: `lean/InfoGeometry/Canonical/SplitCliffordFiveGradingTrace.lean`
  - score 3: `lean/InfoGeometry/Canonical/SplitCliffordFiveGrading.lean`
  - score 3: `lean/InfoGeometry/Canonical/DrazinFiveGradedTKKAnomalyBridge.lean`
  - score 2: `tools/sympy/symmetry_closure/closure_involution_five_grade.py`
  - score 2: `lean/InfoGeometry/Twistor/FiveGradedIncidence.lean`
  - score 2: `lean/InfoGeometry/OperatorAlgebra/FiveGradedInformationLedger.lean`
### `proofs/CliffordInductiveTripotent.lean`
- topics: clifford_o55_pin_spin
  - score 2: `lean/InfoGeometry/Clifford/InductiveColimitCrystal.lean`
  - score 1: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 1: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `lean/InfoGeometry/Twistor/CliffordBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/CliffordFractalWaveletBridge.lean`
  - score 1: `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`
### `proofs/CuntzKriegerFibonacciK.lean`
- topics: fibonacci_anyons
  - score 2: `lean/InfoGeometry/External/Auto/CuntzKriegerPrimon.lean`
### `proofs/DeterminantMoebiusFunctor.lean`
- topics: determinant_sign_mobius
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/ExceptionalBraidTopology.lean`
- topics: group_braid_weyl_root
  - score 3: `tools/sympy/nonorientable_exceptional_braid_topology.py`
  - score 3: `lean/InfoGeometry/Topology/NonorientableExceptionalBraids.lean`
  - score 2: `lean/InfoGeometry/Topology/TwistedBoundaryExceptionalPoints.lean`
  - score 2: `lean/InfoGeometry/Topology/ParafermionBraiding.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinExceptionalTopology.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinBraid.lean`
### `proofs/ExceptionalKleinGlideEP.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinExceptionalTopology.lean`
  - score 2: `lean/InfoGeometry/Canonical/KleinExceptionalBraid.lean`
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
  - score 1: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 1: `tools/sympy/transformer_klein_brillouin.py`
  - score 1: `tools/sympy/selfdual_weyl_klein_bridge.py`
### `proofs/ExceptionalNonorientableTopology.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 3: `tools/sympy/nonorientable_exceptional_braid_topology.py`
  - score 3: `lean/InfoGeometry/Topology/NonorientableExceptionalBraids.lean`
  - score 2: `lean/InfoGeometry/Topology/TwistedBoundaryExceptionalPoints.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinExceptionalTopology.lean`
  - score 2: `lean/InfoGeometry/CognitiveTopology/ExceptionalPoints.lean`
  - score 2: `lean/InfoGeometry/CognitiveTopology/ExceptionalPointGrokking.lean`
### `proofs/FibonacciCliffordBridge.lean`
- topics: clifford_o55_pin_spin, fibonacci_anyons
  - score 2: `lean/InfoGeometry/External/Auto/FibonacciCliffordBridge.lean`
  - score 2: `lean/InfoGeometry/Clifford/FibonacciCl55Carrier.lean`
  - score 1: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 1: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `lean/InfoGeometry/Twistor/CliffordBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/CliffordFractalWaveletBridge.lean`
### `proofs/FixedLineRiemannKlein.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
  - score 1: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 1: `tools/sympy/transformer_klein_brillouin.py`
  - score 1: `tools/sympy/selfdual_weyl_klein_bridge.py`
  - score 1: `tools/sympy/non_hermitian_klein_bottle_ep.py`
  - score 1: `tools/sympy/hestenes_krein_klein_witness.py`
### `proofs/FractalKleinSUSYFramework.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
  - score 1: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 1: `tools/sympy/transformer_klein_brillouin.py`
  - score 1: `tools/sympy/selfdual_weyl_klein_bridge.py`
  - score 1: `tools/sympy/non_hermitian_klein_bottle_ep.py`
  - score 1: `tools/sympy/hestenes_krein_klein_witness.py`
### `proofs/GlideDiracSelectionRule.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/pin55_reflection_glide.py`
  - score 1: `tools/sympy/pin55_glide_reflection.py`
  - score 1: `lean/InfoGeometry/Topology/Pin55ReflectionGlide.lean`
  - score 1: `lean/InfoGeometry/Physics/Pin55Glide.lean`
  - score 1: `lean/InfoGeometry/Clifford/Pin55ReflectionGlide.lean`
### `proofs/GlideModularJ.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/pin55_reflection_glide.py`
  - score 1: `tools/sympy/pin55_glide_reflection.py`
  - score 1: `lean/InfoGeometry/Topology/Pin55ReflectionGlide.lean`
  - score 1: `lean/InfoGeometry/Physics/Pin55Glide.lean`
  - score 1: `lean/InfoGeometry/Clifford/Pin55ReflectionGlide.lean`
### `proofs/GlideSuperchargeCasimir.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/pin55_reflection_glide.py`
  - score 1: `tools/sympy/pin55_glide_reflection.py`
  - score 1: `lean/InfoGeometry/Topology/Pin55ReflectionGlide.lean`
  - score 1: `lean/InfoGeometry/Physics/Pin55Glide.lean`
  - score 1: `lean/InfoGeometry/Clifford/Pin55ReflectionGlide.lean`
### `proofs/KleinGeometrySupergraded.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 2: `lean/InfoGeometry/Topology/WallpaperKleinBottlePresentation.lean`
  - score 2: `lean/InfoGeometry/Topology/VarlamovV4TrifactorKleinBridge.lean`
  - score 2: `lean/InfoGeometry/Topology/TwistedHeckeKleinBottle.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinGaugeInvariant.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinExceptionalTopology.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinBraid.lean`
### `proofs/KleinGrapheneTunneling.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
  - score 1: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 1: `tools/sympy/transformer_klein_brillouin.py`
  - score 1: `tools/sympy/selfdual_weyl_klein_bridge.py`
  - score 1: `tools/sympy/non_hermitian_klein_bottle_ep.py`
  - score 1: `tools/sympy/hestenes_krein_klein_witness.py`
### `proofs/KleinNilpotentThermo.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 2: `lean/InfoGeometry/Thermodynamics/AsanoKleinFourSymmetry.lean`
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
  - score 1: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 1: `tools/sympy/transformer_klein_brillouin.py`
  - score 1: `tools/sympy/selfdual_weyl_klein_bridge.py`
  - score 1: `tools/sympy/non_hermitian_klein_bottle_ep.py`
### `proofs/LOGICAL_GAP_CLOSURE_PLAN.md`
- topics: sage_gap_galgebra_sympy_hooks
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/LogDetSuperKahlerBarrier.lean`
- topics: determinant_sign_mobius
  - score 3: `lean/InfoGeometry/OptimalTransport/LogDetBarrier.lean`
  - score 2: `lean/InfoGeometry/Thermo/FromLogDet.lean`
  - score 2: `lean/InfoGeometry/OperatorAlgebra/TopologicalSuperconductorEdge.lean`
  - score 2: `lean/InfoGeometry/Jordan/LogDet.lean`
  - score 2: `lean/InfoGeometry/External/Auto/KANLogDetUnification.lean`
  - score 2: `lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean`
### `proofs/MinkowskiBiquaternion.lean`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/MobiusWittenIndex.lean`
- topics: determinant_sign_mobius
  - score 2: `tools/sympy/witten_parity_index.py`
  - score 2: `tools/sympy/witten_mobius_bekenstein_complement.py`
  - score 2: `tools/sympy/primon_gas_witten_index.py`
  - score 2: `tools/sympy/mobius_witten_weyl_denominator.py`
  - score 2: `tools/sympy/kudinoor_witten_index_bridge.py`
  - score 2: `lean/InfoGeometry/Holography/WittenMobiusBekensteinComplement.lean`
### `proofs/MobiusWittenKleinIndex.lean`
- topics: wallpaper_klein_brillouin_glide, determinant_sign_mobius
  - score 2: `tools/sympy/witten_parity_index.py`
  - score 2: `tools/sympy/witten_mobius_bekenstein_complement.py`
  - score 2: `tools/sympy/primon_gas_witten_index.py`
  - score 2: `tools/sympy/mobius_witten_weyl_denominator.py`
  - score 2: `tools/sympy/kudinoor_witten_index_bridge.py`
  - score 2: `lean/InfoGeometry/Holography/WittenMobiusBekensteinComplement.lean`
### `proofs/ModularAutomorphismGroup.lean`
- topics: group_braid_weyl_root
  - score 2: `lean/InfoGeometry/Geometry/DiscreteModularSubgroup.lean`
  - score 2: `lean/InfoGeometry/Canonical/ModularNilpotentAutomorphism.lean`
  - score 2: `lean/InfoGeometry/Algebra/NilpotentModularAutomorphism.lean`
### `proofs/ModularGlideCPT.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 2: `lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean`
  - score 1: `tools/sympy/pin55_reflection_glide.py`
  - score 1: `tools/sympy/pin55_glide_reflection.py`
  - score 1: `lean/InfoGeometry/Topology/Pin55ReflectionGlide.lean`
  - score 1: `lean/InfoGeometry/Physics/Pin55Glide.lean`
  - score 1: `lean/InfoGeometry/Clifford/Pin55ReflectionGlide.lean`
### `proofs/ModularItakuraBiquaternion.lean`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/MorandiWallpaperCohomology.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
  - score 1: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 1: `lean/InfoGeometry/Topology/WallpaperToWeylBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/WallpaperSymmetry.lean`
### `proofs/NonOrientableBraid.lean`
- topics: wallpaper_klein_brillouin_glide, group_braid_weyl_root
  - score 3: `tools/sympy/nonorientable_exceptional_braid_topology.py`
  - score 3: `lean/InfoGeometry/Topology/NonorientableExceptionalBraids.lean`
  - score 2: `tools/sympy/nonorientable_weyl_semimetal.py`
  - score 2: `tools/sympy/non_orientable_ep_twisted_boundary.py`
  - score 2: `lean/InfoGeometry/CondensedMatter/NonOrientableWeylSemimetal.lean`
  - score 2: `lean/InfoGeometry/Canonical/StableFibonacciAnyonBraidLimit.lean`
### `proofs/OpticalAndreevSpinor.lean`
- topics: clifford_o55_pin_spin
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/PaperwallDiscreteSUSY.lean`
- topics: wallpaper_klein_brillouin_glide
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/PaperwallHolographicSUSY.lean`
- topics: wallpaper_klein_brillouin_glide
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/PaperwallSUSY.lean`
- topics: wallpaper_klein_brillouin_glide
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/PentagonPenroseWallpaperFractal.lean`
- topics: wallpaper_klein_brillouin_glide, fibonacci_anyons
  - score 2: `lean/InfoGeometry/External/Auto/penrose_wallpaper_colimit.lean`
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
  - score 1: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 1: `lean/InfoGeometry/Topology/WallpaperToWeylBridge.lean`
### `proofs/PlatycosmKTheory.lean`
- topics: wallpaper_klein_brillouin_glide
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/ProjectiveGlideSuperchargeUnification.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 2: `lean/InfoGeometry/GrandUnification/Su2Su3ProjectiveBridge.lean`
  - score 2: `lean/InfoGeometry/GrandUnification/ProjectiveCharacterGWBridge.lean`
  - score 1: `tools/sympy/pin55_reflection_glide.py`
  - score 1: `tools/sympy/pin55_glide_reflection.py`
  - score 1: `lean/InfoGeometry/Topology/Pin55ReflectionGlide.lean`
  - score 1: `lean/InfoGeometry/Physics/Pin55Glide.lean`
### `proofs/ProjectiveKappaKleinMobius.lean`
- topics: wallpaper_klein_brillouin_glide, determinant_sign_mobius
  - score 2: `lean/InfoGeometry/Projective/Quadrics/PluckerKlein.lean`
  - score 2: `lean/InfoGeometry/Projective/KleinQuadricPlucker.lean`
  - score 2: `lean/InfoGeometry/Projective/KleinQuadricIncidence.lean`
  - score 2: `lean/InfoGeometry/Projective/KleinQuadric.lean`
  - score 2: `lean/InfoGeometry/Projective/KleinCrossRatioInvariant.lean`
  - score 2: `lean/InfoGeometry/OperatorAlgebra/O44PinMobiusProjective.lean`
### `proofs/ProjectiveWallpaperGaugePSA.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 2: `lean/InfoGeometry/Projective/GaugeReduction.lean`
  - score 2: `lean/InfoGeometry/Projective/GaugeQuotient.lean`
  - score 2: `lean/InfoGeometry/Arithmetic/ProjectiveWeylGauge.lean`
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
### `proofs/RelativisticBiquaternionKAN.lean`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/RiemannKleinDuality.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
  - score 1: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 1: `tools/sympy/transformer_klein_brillouin.py`
  - score 1: `tools/sympy/selfdual_weyl_klein_bridge.py`
  - score 1: `tools/sympy/non_hermitian_klein_bottle_ep.py`
  - score 1: `tools/sympy/hestenes_krein_klein_witness.py`
### `proofs/SolderingSpinConnectionBogoliubov.lean`
- topics: clifford_o55_pin_spin
  - score 2: `lean/InfoGeometry/OperatorAlgebra/SpinBogoliubovStinespring.lean`
  - score 2: `lean/InfoGeometry/OperatorAlgebra/SpinBogoliubovFrame.lean`
  - score 2: `lean/InfoGeometry/Canonical/SpinConnection.lean`
### `proofs/SouriauBiquaternionGaussian.lean`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/SouriauMoebiusCoupling.lean`
- topics: determinant_sign_mobius
  - score 2: `lean/InfoGeometry/Canonical/SouriauDiracHodgeCoupling.lean`
### `proofs/SpacetimeIsSpin.lean`
- topics: clifford_o55_pin_spin
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/SpinorMonodromySteppingStone.lean`
- topics: clifford_o55_pin_spin
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/SplitOctonionBraidSU3.lean`
- topics: group_braid_weyl_root
  - score 2: `lean/InfoGeometry/Projective/SplitOctonions/ZornLogVolume.lean`
  - score 2: `lean/InfoGeometry/Projective/SplitOctonions/ZornInstance.lean`
  - score 2: `lean/InfoGeometry/Projective/SplitOctonions/ZornDetSignGrading.lean`
  - score 2: `lean/InfoGeometry/Projective/SplitOctonions/ZornConcrete.lean`
  - score 2: `lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsTraceIncidence.lean`
  - score 2: `lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsProjectivePolar.lean`
### `proofs/TitsBruhatBrillouinKlein.lean`
- topics: wallpaper_klein_brillouin_glide, group_braid_weyl_root
  - score 2: `tools/sympy/transformer_klein_brillouin.py`
  - score 2: `tools/sympy/brillouin_klein_gauge_fields.py`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinGaugeInvariant.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinExceptionalTopology.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinBraid.lean`
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
### `proofs/TripotentCliffordColimit.lean`
- topics: clifford_o55_pin_spin
  - score 2: `lean/InfoGeometry/Clifford/InductiveColimitCrystal.lean`
  - score 1: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 1: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `lean/InfoGeometry/Twistor/CliffordBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/CliffordFractalWaveletBridge.lean`
  - score 1: `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`
### `proofs/TwistedHeckeKleinBottle.lean`
- topics: wallpaper_klein_brillouin_glide, group_braid_weyl_root
  - score 4: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 4: `lean/InfoGeometry/Topology/TwistedHeckeKleinBottle.lean`
  - score 2: `tools/sympy/non_hermitian_klein_bottle_ep.py`
  - score 2: `lean/InfoGeometry/Topology/WallpaperKleinBottlePresentation.lean`
  - score 2: `lean/InfoGeometry/External/Auto/KleinBottleSymmetry.lean`
  - score 2: `lean/InfoGeometry/External/Auto/KleinBottleParafermionInvariant.lean`
### `proofs/UnifiedKleinHolographicArchitecture.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 2: `lean/InfoGeometry/External/Auto/UnifiedAnomalyArchitecture.lean`
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
  - score 1: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 1: `tools/sympy/transformer_klein_brillouin.py`
  - score 1: `tools/sympy/selfdual_weyl_klein_bridge.py`
  - score 1: `tools/sympy/non_hermitian_klein_bottle_ep.py`
### `proofs/VerberckWallpaperFourier.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
  - score 1: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 1: `lean/InfoGeometry/Topology/WallpaperToWeylBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/WallpaperSymmetry.lean`
### `proofs/WallpaperBulkAnyonProjection.lean`
- topics: wallpaper_klein_brillouin_glide, fibonacci_anyons
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
  - score 1: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 1: `lean/InfoGeometry/Topology/WallpaperToWeylBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/WallpaperSymmetry.lean`
### `proofs/WallpaperClassification.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
  - score 1: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 1: `lean/InfoGeometry/Topology/WallpaperToWeylBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/WallpaperSymmetry.lean`
### `proofs/WallpaperCohomology.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
  - score 1: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 1: `lean/InfoGeometry/Topology/WallpaperToWeylBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/WallpaperSymmetry.lean`
### `proofs/WallpaperFermionSuperconductingGap.lean`
- topics: wallpaper_klein_brillouin_glide, sage_gap_galgebra_sympy_hooks
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
  - score 1: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 1: `lean/InfoGeometry/Topology/WallpaperToWeylBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/WallpaperSymmetry.lean`
### `proofs/WallpaperIsometry.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
  - score 1: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 1: `lean/InfoGeometry/Topology/WallpaperToWeylBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/WallpaperSymmetry.lean`
### `proofs/WallpaperMetamaterialDataset.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
  - score 1: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 1: `lean/InfoGeometry/Topology/WallpaperToWeylBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/WallpaperSymmetry.lean`
### `proofs/WallpaperSemidirectProduct.lean`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/wallpaper_to_weyl_bridge.py`
  - score 1: `tools/sympy/wallpaper_symmetry_crystal.py`
  - score 1: `tools/sympy/wallpaper_mirror_attention_bridge.py`
  - score 1: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 1: `lean/InfoGeometry/Topology/WallpaperToWeylBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/WallpaperSymmetry.lean`
### `proofs/WaveguideEPBraidSpec.lean`
- topics: group_braid_weyl_root
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/Z2NonAbelianBraiding.lean`
- topics: group_braid_weyl_root
  - score 2: `tools/sympy/emergent_nonabelian_gauge.py`
  - score 2: `lean/InfoGeometry/Canonical/FiniteMajoranaProjectiveBraiding.lean`
  - score 2: `lean/InfoGeometry/Canonical/FiniteMajoranaBraiding.lean`
  - score 2: `lean/InfoGeometry/Canonical/FiniteFibonacciHigherAnyonBraiding.lean`
  - score 2: `lean/InfoGeometry/Canonical/FiniteFibonacciAnyonBraiding.lean`
  - score 2: `lean/InfoGeometry/Canonical/EmergentNonAbelianGauge.lean`
### `proofs/ZornParavectorNullspace.lean`
- topics: biquaternion_quaternion
  - score 2: `lean/InfoGeometry/Geometry/ParavectorZornBoundary.lean`
  - score 2: `lean/InfoGeometry/External/Auto/ZornOPParavector.lean`
### `proofs/ZornScalingFlow.lean`
- topics: biquaternion_quaternion
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/ZornScalingFlowOrdered.lean`
- topics: biquaternion_quaternion
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/artin_parity_braid_witness.py`
- topics: group_braid_weyl_root
  - score 2: `lean/InfoGeometry/Canonical/ParityTraceWitness.lean`
### `proofs/atomic_clifford_kan_sympy.py`
- topics: clifford_o55_pin_spin, sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/zeta_kan_dirichlet_factorization.py`
  - score 2: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 2: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 2: `tools/sympy/holographic_kan_cuntz.py`
  - score 2: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `lean/InfoGeometry/Twistor/CliffordBridge.lean`
### `proofs/biquaternion_clifford_iso.py`
- topics: biquaternion_quaternion, clifford_o55_pin_spin
  - score 2: `lean/InfoGeometry/Clifford/Cl44C8Comparison.lean`
  - score 2: `lean/InfoGeometry/Clifford/Biquaternion.lean`
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 1: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
### `proofs/biquaternion_exp_closure.py`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/biquaternion_kan_nilpotent_sympy.py`
- topics: biquaternion_quaternion, sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/zeta_kan_dirichlet_factorization.py`
  - score 2: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 2: `tools/sympy/kan_wallpaper_isomorphism.py`
  - score 2: `tools/sympy/holographic_kan_cuntz.py`
  - score 2: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 2: `tools/sympy/biquaternion_tomita.py`
### `proofs/biquaternion_laplace_resolvent_sympy.py`
- topics: biquaternion_quaternion, sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 2: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 2: `tools/sympy/biquaternion_tomita.py`
  - score 2: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 2: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 2: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/biquaternion_laplace_tripotent.py`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/biquaternion_logarithm_monodromy.py`
- topics: biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/biquaternion_mobius_squashing.py`
- topics: determinant_sign_mobius, biquaternion_quaternion
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
  - score 1: `tools/sympy/biquaternion_kahler_legendre_finite.py`
### `proofs/biquaternion_negative_roots_log.py`
- topics: biquaternion_quaternion, group_braid_weyl_root
  - score 2: `lean/InfoGeometry/Topology/V4RootSystem.lean`
  - score 1: `tools/sympy/section33_pauli_biquaternion_completion.py`
  - score 1: `tools/sympy/biquaternion_torsion_bridge.py`
  - score 1: `tools/sympy/biquaternion_tomita.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic_noether_bridge.py`
  - score 1: `tools/sympy/biquaternion_kahler_symplectic.py`
### `proofs/braid_clifford_integration_sympy.py`
- topics: clifford_o55_pin_spin, group_braid_weyl_root, sage_gap_galgebra_sympy_hooks
  - score 3: `lean/InfoGeometry/External/Auto/BraidCliffordIntegration.lean`
  - score 2: `tools/sympy/su2_su3_parafermion_braiding.py`
  - score 2: `tools/sympy/nonorientable_exceptional_braid_topology.py`
  - score 2: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 2: `tools/sympy/formal_theory_quantum/chapter4_braided_category.py`
  - score 2: `tools/sympy/clifford_o55_projective_reconciliation.py`
### `proofs/braid_negative_identity_monodromy.py`
- topics: group_braid_weyl_root
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/brillouin_klein_nilpotent_attractor.py`
- topics: wallpaper_klein_brillouin_glide
  - score 2: `tools/sympy/transformer_klein_brillouin.py`
  - score 2: `tools/sympy/brillouin_klein_gauge_fields.py`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinGaugeInvariant.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinExceptionalTopology.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinBraid.lean`
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
### `proofs/cartan_weyl_bogoliubov_gravity.py`
- topics: group_braid_weyl_root
  - score 2: `lean/InfoGeometry/Canonical/BogoliubovCartanFrameInterpretation.lean`
  - score 2: `lean/InfoGeometry/Canonical/BogoliubovCartanEigenOperator.lean`
### `proofs/cayley_schreier_gauge_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/spinor_gauge_fields.py`
  - score 2: `tools/sympy/md_010_gauge_ssb.py`
  - score 2: `tools/sympy/emergent_nonabelian_gauge.py`
  - score 2: `tools/sympy/brillouin_klein_gauge_fields.py`
### `proofs/clifford_55_anomaly_osp.py`
- topics: clifford_o55_pin_spin
  - score 1: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 1: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `lean/InfoGeometry/Twistor/CliffordBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/CliffordFractalWaveletBridge.lean`
  - score 1: `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`
  - score 1: `lean/InfoGeometry/Quantum/RealSplitClifford.lean`
### `proofs/clifford_5_5_anomaly_sympy.py`
- topics: clifford_o55_pin_spin, sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/witten_parity_anomaly_bridge.py`
  - score 2: `tools/sympy/o55_tkk_anomaly_annihilation.py`
  - score 2: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 2: `tools/sympy/clifford_o55_projective_reconciliation.py`
  - score 1: `lean/InfoGeometry/Twistor/CliffordBridge.lean`
  - score 1: `lean/InfoGeometry/Topology/CliffordFractalWaveletBridge.lean`
### `proofs/clifford_inductive_tripotent_sympy.py`
- topics: clifford_o55_pin_spin, sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/uhf_inductive_colimit_boundary.py`
  - score 2: `tools/sympy/tripotent_universe.py`
  - score 2: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 2: `tools/sympy/inductive_colimit_crystal.py`
  - score 2: `tools/sympy/drazin_tripotent_trifactor_bridge.py`
  - score 2: `tools/sympy/clifford_o55_projective_reconciliation.py`
### `proofs/cpt_atom_signum.py`
- topics: determinant_sign_mobius
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/cpt_atom_signum_sympy.py`
- topics: determinant_sign_mobius, sage_gap_galgebra_sympy_hooks
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/cpt_fractal_closure_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/symmetry_closure/z3_yang_baxter.py`
  - score 2: `tools/sympy/symmetry_closure/supercharge_central_charge_closure.py`
  - score 2: `tools/sympy/symmetry_closure/split_triality_kernel.py`
  - score 2: `tools/sympy/symmetry_closure/sector_closure_conformal_blocks.py`
  - score 2: `tools/sympy/symmetry_closure/run_all.py`
  - score 2: `tools/sympy/symmetry_closure/operator_cartan_superbracket_closure.py`
### `proofs/cpt_tensor_fractal_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/cuntz_krieger_fibonacci_k.py`
- topics: fibonacci_anyons
  - score 2: `lean/InfoGeometry/External/Auto/CuntzKriegerPrimon.lean`
### `proofs/cuntz_krieger_ktheory_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/voa_cuntz_oscillator.py`
  - score 2: `tools/sympy/primitive_cuntz_exactness_bridge.py`
  - score 2: `tools/sympy/mirror_phase_cuntz_attention.py`
  - score 2: `tools/sympy/kashiwara_cuntz_cohomology.py`
  - score 2: `tools/sympy/holographic_kan_cuntz.py`
  - score 2: `tools/sympy/discrete_gradient_cuntz.py`
### `proofs/dirac_fourier_mellin_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/wick_rotated_dirac_boundary.py`
  - score 2: `tools/sympy/mellin_dirichlet_convolution_symmetry.py`
  - score 2: `tools/sympy/mellin_colimit_trifactor.py`
  - score 2: `tools/sympy/dirac_boundary_algebra.py`
### `proofs/dirac_zero_modes_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/wick_rotated_dirac_boundary.py`
  - score 2: `tools/sympy/siegel_modular_zeros.py`
  - score 2: `tools/sympy/padic_filtration_trivial_zero.py`
  - score 2: `tools/sympy/low_lying_zeros_quaternion.py`
  - score 2: `tools/sympy/dirac_boundary_algebra.py`
  - score 2: `lean/InfoGeometry/Canonical/SupergradedRandomWalkZeroModes.lean`
### `proofs/exceptional_doubling_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/nonorientable_exceptional_braid_topology.py`
  - score 2: `tools/sympy/exceptional_point_grokking.py`
  - score 2: `tools/sympy/exceptional_grokking_attention.py`
### `proofs/exceptional_klein_glide_ep.py`
- topics: wallpaper_klein_brillouin_glide
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinExceptionalTopology.lean`
  - score 2: `lean/InfoGeometry/Canonical/KleinExceptionalBraid.lean`
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
  - score 1: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 1: `tools/sympy/transformer_klein_brillouin.py`
  - score 1: `tools/sympy/selfdual_weyl_klein_bridge.py`
### `proofs/exceptional_nonorientable_topology.py`
- topics: wallpaper_klein_brillouin_glide
  - score 3: `tools/sympy/nonorientable_exceptional_braid_topology.py`
  - score 3: `lean/InfoGeometry/Topology/NonorientableExceptionalBraids.lean`
  - score 2: `lean/InfoGeometry/Topology/TwistedBoundaryExceptionalPoints.lean`
  - score 2: `lean/InfoGeometry/Topology/BrillouinKleinExceptionalTopology.lean`
  - score 2: `lean/InfoGeometry/CognitiveTopology/ExceptionalPoints.lean`
  - score 2: `lean/InfoGeometry/CognitiveTopology/ExceptionalPointGrokking.lean`
### `proofs/fibonacci_clifford_bridge_sympy.py`
- topics: clifford_o55_pin_spin, sage_gap_galgebra_sympy_hooks, fibonacci_anyons
  - score 2: `tools/sympy/v4_semidirect_s3_fibonacci.py`
  - score 2: `tools/sympy/prime_fibonacci_lattice.py`
  - score 2: `tools/sympy/md_013_clifford_algebraic_structures.py`
  - score 2: `tools/sympy/formal_theory_quantum/chapter6_fibonacci_mtc.py`
  - score 2: `tools/sympy/fibonacci_osp12_bridge.py`
  - score 2: `tools/sympy/clifford_o55_projective_reconciliation.py`
### `proofs/fixed_line_riemann_klein.py`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
  - score 1: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 1: `tools/sympy/transformer_klein_brillouin.py`
  - score 1: `tools/sympy/selfdual_weyl_klein_bridge.py`
  - score 1: `tools/sympy/non_hermitian_klein_bottle_ep.py`
  - score 1: `tools/sympy/hestenes_krein_klein_witness.py`
### `proofs/fractal_klein_susy_framework.py`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/varlamov_v4_trifactor_klein_bridge.py`
  - score 1: `tools/sympy/twisted_hecke_klein_bottle.py`
  - score 1: `tools/sympy/transformer_klein_brillouin.py`
  - score 1: `tools/sympy/selfdual_weyl_klein_bridge.py`
  - score 1: `tools/sympy/non_hermitian_klein_bottle_ep.py`
  - score 1: `tools/sympy/hestenes_krein_klein_witness.py`
### `proofs/fredholm_regularization_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - no obvious current repo filename match; inspect before creating new owner surface
### `proofs/glide_dirac_selection_rule.py`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/pin55_reflection_glide.py`
  - score 1: `tools/sympy/pin55_glide_reflection.py`
  - score 1: `lean/InfoGeometry/Topology/Pin55ReflectionGlide.lean`
  - score 1: `lean/InfoGeometry/Physics/Pin55Glide.lean`
  - score 1: `lean/InfoGeometry/Clifford/Pin55ReflectionGlide.lean`
### `proofs/glide_modular_j.py`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/pin55_reflection_glide.py`
  - score 1: `tools/sympy/pin55_glide_reflection.py`
  - score 1: `lean/InfoGeometry/Topology/Pin55ReflectionGlide.lean`
  - score 1: `lean/InfoGeometry/Physics/Pin55Glide.lean`
  - score 1: `lean/InfoGeometry/Clifford/Pin55ReflectionGlide.lean`
### `proofs/glide_supercharge_casimir.py`
- topics: wallpaper_klein_brillouin_glide
  - score 1: `tools/sympy/pin55_reflection_glide.py`
  - score 1: `tools/sympy/pin55_glide_reflection.py`
  - score 1: `lean/InfoGeometry/Topology/Pin55ReflectionGlide.lean`
  - score 1: `lean/InfoGeometry/Physics/Pin55Glide.lean`
  - score 1: `lean/InfoGeometry/Clifford/Pin55ReflectionGlide.lean`
### `proofs/grand_holographic_theorem_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/symmetry_closure/holographic_entanglement_triality.py`
  - score 2: `tools/sympy/holographic_kan_cuntz.py`
  - score 2: `tools/sympy/grand_unification_algebra.py`
### `proofs/gravity_soldering_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/torsion_soldering_channels.py`
  - score 2: `tools/sympy/quaternionic_emergent_gravity_foundation.py`
  - score 2: `tools/sympy/emergent_gravity_action_variation.py`
### `proofs/holographic_dictionary_synthesis_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/symmetry_closure/holographic_entanglement_triality.py`
  - score 2: `tools/sympy/holographic_kan_cuntz.py`
  - score 2: `lean/InfoGeometry/Canonical/HolographicBoundaryBulkDictionary.lean`
### `proofs/holographic_scale_extinctions_sympy.py`
- topics: sage_gap_galgebra_sympy_hooks
  - score 2: `tools/sympy/symmetry_closure/holographic_entanglement_triality.py`
  - score 2: `tools/sympy/holographic_kan_cuntz.py`
  - score 2: `tools/sympy/bcs_bec_scale_separation.py`

## 6. Ranked formalization packet recommendations

### P0 remote-state hygiene before vendoring
external_refs/auto local checkout is dirty and 11 commits behind origin/main; merge/rebase would collide with local edits and untracked files.

### P1 Biquaternion / quaternion algebra packet
origin/main adds BiquaternionCliffordIso, Biquaternion* closure/log/resolvent/KAN files and current repo already has BiQuaternionKahler*, SplitQuaternion*, QuaternionEmbedding surfaces. Good SymPy+Lean twin target; use concrete 2x2 complex / 4x4 real matrices and determinant/norm laws.

### P1 Wallpaper/Klein/Brillouin/glide packet
origin/main adds BrillouinKleinNilpotentAttractor, MorandiWallpaperCohomology, WallpaperClassification/Cohomology/Isometry, Glide* and ExceptionalKlein* files; current repo has Topology/WallpaperKleinBottlePresentation, BrillouinKlein*, External/Auto/Klein*. Good GAP/Sage group-action + Lean finite-presentation bridge target.

### P1 Clifford/O(5,5)/Pin/Spin packet
origin/main adds Clifford55AnomalyOSP, CliffordFiveFiveAnomaly, AtomicCliffordKAN, SpinorMonodromy; current repo has HestenesAffineO55ClosureBridge and O55TKKAnomalyAnnihilation. Use clifford/galgebra + Sage/GAP for finite certificate, avoid global analytic anomaly claims.

### P2 determinant/sign decomposition packet
many auto and repo files contain determinant/sign/Mobius/logdet/Berezinian surfaces. Formalize finite determinant multiplicativity, sign/parity, superdeterminant list/product laws before analytic continuations.

### P2 group/braid/Weyl/root packet
auto contains Artin/Braid/Fibonacci/Weyl/Tits/Bruhat/projective crystal surfaces. Use GAP/Sage for finite Coxeter/Weyl/group order checks, Lean for finite presentations and invariants.

## 7. Guardrails

- Treat external_refs/auto as proposal/source material, not proof authority. Vendor only after reading theorem bodies and compiling in this repo.
- Do not pull/merge origin/main into `external_refs/auto` while local dirty tracked/untracked files are present.
- For finite algebraic claims: SymPy/assertions first, then Lean theorem; for group/root claims use Sage/GAP; for Clifford/O(5,5) use `.venv-123` clifford/galgebra plus Lean.
- Do not promote wallpaper/Klein/glide finite relations into manifold/topological/Pin classification claims unless the Lean owner theorem proves that exact statement.