# Lattice Formalized Context Pack

This context pack distills the exact Lean 4 signatures, verified mathematical bridges, non-conflation boundaries, and graph/ontology receipts for `"lattice"` across `info-geometry-lean`.

---

## 1. Authoritative Counts & Graph Receipts (Observed 2026-11-22)

- **Full-Codebase Ripgrep Scan (`reports/lattice.matches.jsonl`, `reports/lattice.scan_stats.md`):**
  - `35,057` total submatches (`31,412` lines across `5,609` files) partitioned by surface:
    - `external-ref`: `16,536` matches / `3,777` files (`CFSG`: 16,453; `FrogBird`: 83; compiled `OAI.GroupTheory.FiniteLattice`: 14 files / 132 decls via `lakefile.lean:925`)
    - `repo-owned`: `13,718` matches / `1,476` files (`1,892` Lean declaration lines; `500` files in `lean/InfoGeometry`, `222` files in `lean/Omega`, plus `src/` mirrors and `tools/`/`tests/`)
    - `archive-or-cache`: `4,193` matches / `241` files
    - `docs`: `532` matches / `107` files
    - `generated-artifact`: `78` matches / `8` files
- **Compiler DAG & Auto-Ontology Receipts (`reports/lattice_auto_ontology_dag.json`, `reports/lattice_dag_strata.json`, `reports/lattice_ontology_projection_receipt.json`):**
  - Local DAG (`artifacts/dag/index/{decls,edges}.jsonl`): `2,101` lattice declarations across `211` modules in `6` strictly acyclic topological strata (`depth 0..5`), connected by `9,323` internal compiler edges (`4,090` `type`, `5,233` `value`) across `226` cross-module pairs.
  - Auto-Ontology Offline Validation (`ontology_bridge_data.run_offline_jsonl_dry_run`): `status = dry_run_ok`, `source_digest = 198bf6098005ca219daf0a58fe13bdc202401e3504e064f92ea150d5047e5f2e`.
  - Auto-Ontology REST (`http://127.0.0.1:3001`): `lattice = 1,609` terms, `Hurwitz = 728`, `Quasilattice = 122`, `Birkhoff = 85`, `Plaquette = 84`, `Sublattice = 35`, `Phylogen = 35`, `Taxonom = 25`, `CompleteLattice = 22`.
  - ArangoDB `infogeometry` (`decls_g_ig_full_20261115_b`): `1,874` lattice declarations; `36` lattice-related `evo_commits`.

---

## 2. Core Signatures & Mathematical Bridges

```lean
-- 1. Order / Boolean / Complete / Galois Lattices (Clade I)
inductive KreinSector | bot | minus | plus | top
def Sector (n : ℕ) : Type := Set (BinaryWord n) × KreinSector
instance (n : ℕ) : BooleanAlgebra (Sector n)
noncomputable instance (n : ℕ) : CompleteLattice (Sector n)
theorem sector_galois_connection (n : ℕ) : GaloisConnection refineSector coarseSector
def kreinSectorToAlg : KreinSector → CliffordAlgebra splitQ11

-- 2. Noncommutative Projector Clabjects & Phylogenesis (Clade I, src/InfoGeometry & lean/)
def projectorSubspace (P : B) : Set B := {x : B | P * x = x}
def cladeSubsumes (Psub Panc : B) : Prop := Psub * Panc = Psub ∧ Panc * Psub = Psub
def cladeComplement (Psub Panc : B) : B := Panc - Psub
def cladeFork (Pl Pr : B) : B := Pl - Pr
def cladeJoin (Pl Pr : B) : B := Pl + Pr
theorem cladeSubsumes_projectorSubspace_subset :
    cladeSubsumes Psub Panc → projectorSubspace Psub ⊆ projectorSubspace Panc
theorem drazin_core_null_unique_projector_decomposition (S : DrazinSurgery A) (x : B) :
    ∃! parts : B × B, parts.1 ∈ projectorSubspace S.coreProjector ∧
      parts.2 ∈ projectorSubspace S.nullProjector ∧ parts.1 + parts.2 = x

-- 3. Integral / Dual / Zorn / E8 / Leech / Charge Z-Lattices (Clade II)
def IsD4 (x : Fin 4 → ℤ) : Prop := coordinateSum x % 2 = 0
def D4.latticeToDualSubgroup : D4.latticeSubgroup →+ D4.dualSubgroup
theorem ExceptionalRootLatticeWeyl.cantorWordPermRep_injective :
    Function.Injective (cantorWordPermRep τ)
theorem D4CantorWeylAction.cantorWordOperatorUnitRep_injective :
    Function.Injective cantorWordOperatorUnitRep
def ZornVectorMatrix.dualLattice (L : AddSubgroup (ZornVectorMatrix ℚ)) :
    AddSubgroup (ZornVectorMatrix ℚ)
def SplitCharge.hyperbolicNorm {n : ℕ} (q : SplitCharge n) : ℤ :=
    ∑ i : Fin n, 2 * (q.momentum i * q.winding i)
def LeechLattice.numerator : Set (Fin 24 → ℤ) := evenBranch ∪ oddBranch

-- 4. Arithmetic Prime-Bit & Hilbert-Pólya Spectral Lattices (Clade III)
theorem primeBitEnergy_eq_log_primeBitInteger :
    primeBitEnergy L ε.1 = Real.log (primeBitInteger L ε : ℝ)
theorem primeBitFermionicPartition_eq_factorizedRealRpow :
    primeBitFermionicPartition L β = ∏ p ∈ L.primes, (1 + (p : ℝ) ^ (-β))
theorem FiniteMajoranaLattice.D_sq_eq_H : M.D ^ 2 = M.H

-- 5. Omega Birkhoff-Gödel Divisibility & Cycle-Theta Lattices (Clade IV)
theorem paper_xi_godel_birkhoff_ideal_lattice_squarefree :
    Function.Injective (xi_godel_birkhoff_ideal_lattice_squarefree_code (r := r) q) ∧
      (∀ I J, code (meet I J) = Nat.gcd (code I) (code J)) ∧
      (∀ I J, code (join I J) = Nat.lcm (code I) (code J))
theorem paper_pom_cycle_lattice_theta_poisson_duality :
    thetaBulk D = thetaDual D ∧ treeNormalizedGram D = weightedTreeRatio D

-- 6. Lattice Gauge / Plaquette / Elitzur Projection (Clade V)
theorem plaquetteAction_gauge_invariant :
    plaquetteAction lattice (gaugeTransform lattice gauge links) = plaquetteAction lattice links
theorem elitzur_local_gauge_expectation_zero :
    IsGaugeInvariant w → IsCovariant O χ → ∑ g : G, χ g = 0 → gibbsExpectation w O = 0

-- 7. Quasilattice Index, JKO/RG Flow & Crystallographic/Period Lattices (Clades VI & VII)
noncomputable def quasilatticeChiralKernelSlicePlus V X t : Submodule ℝ (DoubledSpace E) :=
    LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap ⊓
      LinearMap.range (KreinGradedModule.gradeProjPlus).toLinearMap
theorem common_lattice_d4_coherence (g : Fin 8) (t : Z2) :
    realifyLattice (d4_action_on_Z2 g t) = realD4Action g (realifyLattice t) ∧
      matVec5 (weylD5CrossSection2 g) (latticeEmbed t) = latticeEmbed (d4_action_on_Z2 g t)
theorem circulationPeriod_eq_residuePairing (w : WindingPair) :
    circulationPeriod w = residuePairing w * (2 * Real.pi * Complex.I : ℂ)
```

---

## 3. Reasoning & Socratic Pitfalls to Avoid

1. **Order Lattices vs. $\mathbb{Z}$-Lattices vs. Finite Cell Lattices:** Never silently transport theorems between `Lattice α` (Mathlib order typeclass: `sup, inf`), `AddSubgroup` / `Submodule ℤ` (metric/bilinear $\mathbb{Z}$-lattices like `D4RootLattice` or `ZornDualLattice`), and `PlaquetteLattice Vertex Edge Face` (cellular 2-complex for gauge links). Any connection requires a named morphism (e.g., `kreinSectorToAlg`, `xi_godel_birkhoff_ideal_lattice_squarefree_code`, `latticeEquivNat`, `common_lattice_d4_coherence`).
2. **Prose / Socket Boundaries:**
   - [`HurwitzLattice.lean`](../lean/InfoGeometry/Projective/HurwitzLattice.lean) documents deferred ring-closure/multiplication proofs (`hurwitzToTwistorBlock`).
   - [`HestenesD4HurwitzBridge.lean`](../lean/InfoGeometry/Krein/HestenesD4HurwitzBridge.lean) is an explicit hypothesis-carrying socket (`D4LatticeKacMoodyBridge`), not an internal construction of Hurwitz maximal orders.
   - [`ViazovskaMagicFunctionRoots.lean`](../lean/InfoGeometry/Canonical/ViazovskaMagicFunctionRoots.lean) proves `e8ShellRadius` squares (`2`, `4`), not modular-form optimality.
   - `OntologyRing.lean` sits in [`src/InfoGeometry/OperatorAlgebra/OntologyRing.lean`](../src/InfoGeometry/OperatorAlgebra/OntologyRing.lean) while [`CladisticPhylogenesisBridge.lean`](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CladisticPhylogenesisBridge.lean) sits in `lean/`.
3. **Continuum Limits vs. Finite-Cutoff / Finite-Stage Identities:** `PrimeBitLattice`, `FinitePlaquette`, `FiniteGibbsModel`, `ElitzurLatticeGaugeProjection`, and `GolayLeechMOGSheetPoset` prove exact finite-register / finite-group / finite-ring identities; infinite-dimensional continuum field theory and Monster VOA modular invariance remain open horizons.
4. **Cantor Lattice Cardinality & Boolean Ring Boundaries:** [`CantorCylinderLattice.lean`](../lean/InfoGeometry/Canonical/CantorCylinderLattice.lean) forms the powerset lattice on `BinaryWord n` (`Fin n → Bool`), which has $2^{2^n}$ elements, whereas `B(P)` (`Finset.powerset` / squarefree divisors) has $2^{|P|}$ elements. Use the order-faithful injections [`supportCone`](../lean/InfoGeometry/Canonical/PrimeBooleanCantorBridge.lean#L71-L106), [`downsetCylinder`](../lean/InfoGeometry/Canonical/PrimeBooleanCantorCylinderBridge.lean#L82-L121), or [`atomCylinderMap`](../lean/InfoGeometry/Canonical/PrimeBooleanCantorCylinderBridge.lean#L133-L202) rather than claiming an isomorphism `B(P) ≃ Set (BinaryWord P)`. Similarly, `splitClCartanProj` in [`SplitCl11GradedTensorTower.lean`](../lean/InfoGeometry/Clifford/SplitCl11GradedTensorTower.lean#L149-L241) is the commuting Boolean Cartan subalgebra inside noncommutative $\mathrm{Cl}(1,1)^{\otimes n}$ (`splitClPower_one_noncomm`).
5. **Typed Relation Discipline Across ASTAQL Clusters & Char-0 Characters:** Shared ArangoDB hashes ([`reports/lattice_astaql_hash_unification.json`](../reports/lattice_astaql_hash_unification.json)) and `1,831` module import edges are structural clues, not equivalence proofs. Keep `SignedPerm` action on finite `Sector P` ([`FiniteOperatorBooleanAlgebra.lean`](../lean/InfoGeometry/Canonical/FiniteOperatorBooleanAlgebra.lean#L231-L265), where `instSignedPermAction` is now closed), character Euler supertraces ([`FiniteCyclotomicCharacterSupertraceBridge.lean`](../lean/InfoGeometry/Arithmetic/FiniteCyclotomicCharacterSupertraceBridge.lean), [`FiniteQuadraticCharacterFiveBridge.lean`](../lean/InfoGeometry/Arithmetic/FiniteQuadraticCharacterFiveBridge.lean)), the explicit quadratic-character homomorphism `cyclotomicToBooleanSign` and `prod_cyclotomicToBooleanSign_eq_weylSign` ([`CyclotomicQuadraticBooleanSignBridge.lean`](../lean/InfoGeometry/Algebra/CyclotomicQuadraticBooleanSignBridge.lean#L45-L163)), and [`BostConnesClassFieldTheoryBridge.lean`](../lean/InfoGeometry/Algebra/BostConnesClassFieldTheoryBridge.lean) typed cleanly rather than assuming an unproved equality beyond finite cutoffs.
6. **Wallpapers, Crystallographic $\Phi_6/\Phi_3$, and Two Levels of Operator-Ring Cyclotomics:** Do not conflate: (i) crystallographic point-group cyclotomic restriction on `ReciprocalCoord` ([`CrystallographicRootCyclotomicBridge.lean`](../lean/InfoGeometry/Canonical/CrystallographicRootCyclotomicBridge.lean#L59-L176)), (ii) cyclotomic Fourier spectral projectors for $U^n = 1$ / $T^3 = T$ mapped into corner `Matrix (Fin n) (Fin n) A` blocks ([`FourthRootSpectralProjectors.lean`](../lean/InfoGeometry/Algebra/FourthRootSpectralProjectors.lean), [`CyclotomicOperatorProjectors.lean`](../lean/InfoGeometry/Algebra/CyclotomicOperatorProjectors.lean), [`CyclotomicPeirceMatrix.lean`](../lean/InfoGeometry/Algebra/CyclotomicPeirceMatrix.lean)), and (iii) `GaloisGroupAction` / `ModularPhaseFlow` covariance on `BostConnesStructure A Γ` ([`BostConnesClassFieldTheoryBridge.lean`](../lean/InfoGeometry/Algebra/BostConnesClassFieldTheoryBridge.lean), [`BostConnesModularAutomorphismBridge.lean`](../lean/InfoGeometry/Algebra/BostConnesModularAutomorphismBridge.lean)). No theorem identifies a wallpaper group with a cyclotomic Galois group, nor claims full $\mathrm{Gal}(\mathbb{Q}^{\mathrm{ab}}/\mathbb{Q})$ faithfulness on all operator idempotents.

---

## 4. The 6-Level $\mathbb{F}_2^P$ Unifying Spine & ASTAQL Hash Clusters (Seed Signatures)

```lean
-- Level 1 -> Level 3: Boolean cube <-> squarefree divisors <-> A₁^P Weyl denominator
BooleanCubeDictionary.fullDictionaryEquiv        -- stateToSubsetEquiv / subsetToArithmeticEquiv
FormalPrimeRootSystem.weylAlternatingSum_eq_prod_one_sub
PrimeBooleanCantorCylinderBridge.downsetCylinder_injective

-- Level 4: Closed hyperoctahedral group action (ℤ/2)^P ⋊ S_P on Sector P
FiniteOperatorBooleanAlgebra.instSignedPermAction : MulAction (SignedPerm P) (Sector P)
FiniteOperatorBooleanAlgebra.signedPerm_compl
FiniteOperatorBooleanAlgebra.primeSubsetOps_mul_eq_zero_of_mem_symmDiff

-- Level 6: Noncommutative Cl(1,1)^n tower, Krein P_plus, Zorn D₄ dual & KK analytical index
SplitCl11GradedTensorTower.splitClPower_one_noncomm : ∃ a b : SplitClPower 1, a * b ≠ b * a
Krein.Representation.cl11Rep_kreinSectorPlus_eq_P_plus
Algebra.WallpaperZornDualLatticeBridge.zornPlaneEmbed_mem_dualLattice_iff
KK.QuasilatticeBooleanIndexBridge.quasilatticeAnalyticalIndex_cast_eq_booleanAlternatingIndex
```

- **Verified ArangoDB ASTAQL Clusters (`decls_g_ig_full_20261115_b`: `335,101` decls / `2,313,219` edges):** `17` anchors, `21` `(canonicalTypeHash, canonicalValueHash)` carrier clusters (notably `13708595792875408638 / 221004736247398889` $\mathbb{R}^2$ across `34` modules and `8311462266753216155 / 1059564743757507425` `Fin n → Bool` across `19` modules), `17` de Bruijn `lean-expr-debruijn-v4` theorem clusters (including `exists_noncomm_pair` across `34` modules and `8` `CrystallographicRootCyclotomicBridge` ↔ `D6ReciprocalLatticeBrillouinZone` pairs), and `15,926` 2-hop multi-apex shared nodes centered on the **Prime/Weyl** and **Clifford/Krein/Fredholm** hubs.
- **Validation Scope:** All 13 unification modules passed `axiom_check.py --batch-size 5` (`13 passed, 0 failed`) and locked `lake build` (`9194` jobs); `FiniteOperatorBooleanAlgebra.lean` and `QuasilatticeBooleanIndexBridge.lean` passed strict single-file `run_locked_lean.py -- -DwarningAsError=true`. See [`docs/LATTICE_ONTOLOGY_TAXONOMY_PHYLOGENESIS.md`](LATTICE_ONTOLOGY_TAXONOMY_PHYLOGENESIS.md) Sections 7–8.

---

## 5. Wallpaper ↔ Lattice ↔ Crystallographic $\Phi_6$ ↔ Operator Cyclotomic ↔ Bost–Connes Signatures

```lean
-- Wallpapers, affine Weyl quotients & mod-2 F₂ parity
Wallpaper.glide_squared_eq_x_translation (p : Lattice2D) : G (G p) = T_x p
Wallpaper.wallpaperOperatorRep_injective : Function.Injective wallpaperOperatorRep
BrillouinKleinWallpaperCommonLatticeBridge.latticeParity_d4_action (g : Fin 8) (t : IntegralLattice) :
    latticeParity (d4_action_on_Z2 g t) = parityD4Action g (latticeParity t)
Pin55WeylWallpaper.weyl_wallpaper_quotient_packet
CrystallographicRootCyclotomicBridge.axialRotateEnd_cyclotomic_six :
    axialRotateEnd ^ 2 - axialRotateEnd + 1 = 0
CrystallographicRootCyclotomicBridge.x6_sub_one_cyclotomic (x : ℤ) :
    x ^ 6 - 1 = (x - 1) * (x + 1) * (x ^ 2 + x + 1) * (x ^ 2 - x + 1)

-- Level (a) Cyclotomic polynomials on operators -> Peirce corner matrix
FourthRootSpectralProjectors.fourthRootReadout (U : Module.End ℂ E) (hU : U ^ 4 = 1) :
    FourierCyclotomicReadout (K := ℂ) (A := Module.End ℂ E) U 4
CyclotomicOperatorProjectors.npotent_nonzero_isIdempotent {x : R} {n : ℕ} (hn : 2 ≤ n) (hx : IsNPotent x n) :
    IsIdempotent (npotentNonzeroProjector x n)
CyclotomicPhasePolarization.coordinateProjector_idempotent
CyclotomicPeirceMatrix.blocks_mul (X Y : A) : blocks F (X * Y) = blocks F X * blocks F Y
CyclotomicPeirceMatrix.blocks_one : blocks F 1 = Matrix.diagonal F.projector

-- Level (b) Galois & modular covariance + Char-0 Boolean sign bridge
CyclotomicQuadraticBooleanSignBridge.cyclotomicToBooleanSign (L : FormalPrimeRootLattice) :
    (ZMod (squarefreeCode L.primes))ˣ →* ({p // p ∈ L.primes} → ℤˣ)
CyclotomicQuadraticBooleanSignBridge.prod_cyclotomicToBooleanSign_eq_weylSign
BostConnesClassFieldTheory.GaloisGroupAction.galois_P_invariance (g : G) (n : ℕ+) :
    (GA.galois_structure B g).P n = B.P n
BostConnesModularAutomorphism.ModularPhaseFlow.sigma_hecke_coprime
```

- **18-Module Verification Receipt (`561` Wallpaper / `9,079` Cyclotomic / `528` Co-Occurrence Scan Context):** `run_locked_lake_build.py --wait-for-build-lock` (`Build completed successfully (9416 jobs)`) + `axiom_index.py` across all `18` referenced owners (`18 / 18` modules clean, `602` decls, `0` nonstandard axioms); `opengauss_screener.py --strict` reported `0` errors across all `18` files (`14` clean, `4` with heuristic `T4`/`T17` warnings). See [`docs/LATTICE_ONTOLOGY_TAXONOMY_PHYLOGENESIS.md`](LATTICE_ONTOLOGY_TAXONOMY_PHYLOGENESIS.md#L308) Section 9.
