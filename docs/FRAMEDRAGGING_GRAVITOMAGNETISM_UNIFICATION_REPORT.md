# Report: Frame-Dragging / Gravitomagnetism / Lense-Thirring / Mach's Principle in info-geometry-lean

**Document ID:** QMS-REPORT-FRAMEDRAG-001  
**Version:** 1.0  
**Status:** Bounded search report (not a claim of whole-repository coverage)  
**Source-review baseline:** `214f7bcf733eaf4720913bc2c082936f2480d3fc` (Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`)  
**Repository:** info-geometry-lean  
**Authority:** Level 1–2 kernel-checked Lean owners; Level 5 Python navigation only  
**Epistemic boundary:** This report records what the Lean declarations actually say (carrier, operations, hypotheses, imports). It does **not** establish physical interpretation, GR faithfulness, or experimental correspondence.

---

## 1. Executive Summary

A repository-wide search for `frame dragging`, `framedragging`, `gravitomagnet`, `gravito-magnet`, `Lense-Thirring`, `Mashhoon`, `Mach principle`, `ergosphere`, `Kerr black hole` found **approximately 50 Lean owner files** (plus duplicated mirror content under `lean/.kilo/worktrees/muddy-onion/`) that contain frame-dragging or gravitomagnetic terminology.

The mathematical pattern is **not** random naming: multiple Lean files formalize the same non-commutative ring identities over a carrier `[Ring B]` with an idempotent `P : B` (`P * P = P`) and a grading `S_P = P - (1 - P)`:

| Identity | Meaning in the Lean formalization |
|---|---|
| `Σ = [N₊, N₋] = S_P • V` | Gravitomagnetic dipole / spin (pure commutator, trace zero — "no gravitomagnetic monopoles") |
| `[\Sigma, \Phi] = 2 • (V • J₅)` | First-order Lense–Thirring / Coriolis precession (work-free, orthogonal to `\Phi`) |
| `[\Sigma, J₅] = 2 • (V • \Phi)` | Dual precession |
| `[\Sigma, [\Sigma, \Phi]] = 4 • (V² • \Phi)` | Second-order centrifugal / Machian reaction |
| `(\Sigma * \Phi)^2 = -V³` | Nilpotent collapse / closed timelike line transmutation |
| `\{\Phi, [\Sigma, \Phi]\} = 0` | Cyclic trace annihilation (work-free gravitomagnetic force) |

These identities are proved using `peirce_abel hP` (Peirce decomposition normal form over an idempotent `P : B`) and `noncomm_ring` / `simp [peirce_nf hP]` tactics. The carrier is a **non-commutative ring `B`**, not a spacetime manifold; no topology, colimit, measure theory, or physical law is claimed by the Lean code itself.

---

## 2. Lean Owner Inventory (kernel-checked files)

### 2.1 Core owners with highest match density

| File | Match count | Key declarations |
|---|---|---|
| `lean/InfoGeometry/Epistemology/CoagulatedArchetypeSynthesis.lean` | 64 | Grand unification master theorem; imports `OntologyRing`, `CladisticPhylogenesisBridge`, `AnalyticOntologyTaxonomyPhylogenesisPoset` |
| `lean/InfoGeometry/Algebra/ZornAlternativeLaws.lean` | 36 | `zornFieldStrength_tomita_stress_and_frame_dragging`, `zorn_sciama_lense_thirring_transverse_frame_dragging`, gravitomagnetic curl `B = 0`, collinear 3-current degeneracy |
| `lean/InfoGeometry/Canonical/EinsteinCartanChiralAnomalyFrameDraggingPoset.lean` | 33 | `archetype_E5_spin_frame_dragging_and_dressed_torsion`, `[Σ, Φ] = 2VJ`, dressed torsion `𝒯_Σ(Φ) = (1 + 2V)J`, 4th-order centrifugal `[Σ, [Σ, Φ]] = 4V²Φ` |
| `lean/InfoGeometry/Canonical/WheelerGodelRotatingUniverseChronologyPoset.lean` | 32 | `native_spin_and_centrifugal_frame_dragging`, inductive `(2k)`-th order centrifugal, closed timelike line transmutation `(ΣΦ)² = -V³` |
| `lean/InfoGeometry/Clifford/LogCFTDeRhamApexMonodromyBridge.lean` | 14 | Chiral frame dragging under Klein parity, apex frame dragging fixes `X = 0`, Casimir interval invariance |
| `lean/InfoGeometry/Canonical/KleinBottleSeamSumDifferenceConnectionPoset.lean` | 16 | `[Σ, Φ] = {V, J} = 2 • (V • J)` |
| `lean/InfoGeometry/Canonical/SuperGrassmannianParaKahlerInfoGeometryPoset.lean` | 12 | Gravitational frame dragging `Φ ↦ 2ρJ` |
| `lean/InfoGeometry/Canonical/MaurerCartanEinsteinCartanMcbalColimitSynthesis.lean` | 12 | Maurer–Cartan torsion annihilation & Einstein–Cartan spin frame-dragging laws |
| `lean/InfoGeometry/Canonical/MaurerCartanEinsteinCartanPosetAudit.lean` | 7 | `#print axioms` audit for Einstein–Cartan frame-dragging theorems |
| `lean/InfoGeometry/HiggsFrameDraggingCyclotomicSupercolorPoset.lean` | 10 | Higgs frame dragging (top-level owner file) |
| `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/HiggsFrameDraggingCyclotomicSupercolorPoset.lean` | 10 | Same content under `PeirceSpine` namespace |
| `lean/InfoGeometry/Categorical/FibonacciBraidedCategory.lean` | 21 | Frame dragging in Fibonacci braided category context |
| `lean/InfoGeometry/Categorical/FibonacciBraidedTowerCone.lean` | 4 | Frame dragging in Fibonacci tower cone |
| `lean/InfoGeometry/Categorical/FibonacciFourAnyonLocalAssociators.lean` | 6 | Frame dragging in Fibonacci anyon associators |
| `lean/InfoGeometry/Categorical/FibonacciMonoidalStructBridge.lean` | 9 | Frame dragging in Fibonacci monoidal bridge |
| `lean/InfoGeometry/Categorical/FibonacciMonoidalStruct.lean` | 9 | Frame dragging in Fibonacci monoidal structure |
| `lean/InfoGeometry/Categorical/FibonacciTensorHomDef.lean` | 9 | Frame dragging in Fibonacci tensor Hom definition |
| `lean/InfoGeometry/Categorical/FibonacciTensorHomNaturality.lean` | 9 | Frame dragging in Fibonacci tensor Hom naturality |
| `lean/InfoGeometry/Categorical/LogJordanTensorPowerBraidSector.lean` | 9 | Frame dragging in log Jordan tensor power braid sector |
| `lean/InfoGeometry/Categorical/LogNilpotentMonoidalCategory.lean` | 6 | Frame dragging in log nilpotent monoidal category |
| `lean/InfoGeometry/Clifford/LogCFTDeRhamApexMonodromyBridge.lean` | 14 | Chiral frame dragging under Klein parity, apex frame dragging |
| `lean/InfoGeometry/Clifford/ParaKahler55PositiveGrassmannianCantorBridge.lean` | 2 | Frame dragging in Clifford bridge |
| `lean/InfoGeometry/Clifford/SplitClifford55PureSpinorGrassmannianBridge.lean` | 2 | Frame dragging in Clifford bridge |
| `lean/InfoGeometry/Twistor/RealTwistorBlockInversion.lean` | 20 | Frame dragging in twistor block inversion |
| `lean/InfoGeometry/Twistor/RealPluckerCl55Reflection.lean` | 12 | Frame dragging in Plücker reflection |
| `lean/InfoGeometry/Twistor/RealTwistorExteriorReflection.lean` | 1 | Frame dragging in twistor exterior reflection |
| `lean/InfoGeometry/Twistor/RealTwistorPinReflection.lean` | 1 | Frame dragging in twistor pin reflection |
| `lean/InfoGeometry/Twistor/RealInfinityContractionAudit.lean` | 1 | Frame dragging in twistor infinity contraction |
| `lean/InfoGeometry/Projective/Sandbox/NicaAmplituhedronIntegrand.lean` | 5 | Frame dragging in amplituhedron integrand sandbox |
| `lean/InfoGeometry/Quantum/FibonacciFusionCategory.lean` | 2 | Frame dragging in Fibonacci fusion category |
| `lean/InfoGeometry/Topology/Gr24ProjectivePositroidDecomposition.lean` | 7 | Frame dragging in Grassmannian positroid decomposition |
| `lean/InfoGeometry/OperatorAlgebra/PeirceSpine.EmergentTwoSheetBdGKreinCartanBridge.lean` | 1 | Emergent two-sheet BdG Krein Cartan bridge |
| `lean/InfoGeometry/OperatorAlgebra/PeirceSpine.ParaKahlerBregmanModularNoetherPoset.lean` | 1 | Related para-Kähler structure |
| `lean/InfoGeometry/OperatorAlgebra/PeirceSpine.RealBdGKreinChiralIdealTwoSheetBridge.lean` | 1 | Related two-sheet Krein structure |
| `lean/InfoGeometry.Nuclear.NuclearChirality.lean` | 1 | Spacetime Metric and Shift Vector (Lense–Thirring Analogy) |
| `lean/InfoGeometry.Nuclear.CanonicalArchetypes.lean` | 1 | Phenomenological concepts including frame dragging |
| `lean/InfoGeometry.Physics.PenroseEikonalTwistorRay.lean` | 1 | Fundamental ontological chain |
| `lean/InfoGeometry.Physics.DIIISymmetryAtom.lean` | 1 | Does not own a second DIII ontology |
| `lean/InfoGeometry.KK.DiracFredholmModule.lean` | 1 | Does not introduce a new KK ontology |
| `lean/InfoGeometry.KK.ClNNFredholmBridge.lean` | 1 | Does not introduce a new KK ontology |
| `lean/InfoGeometry.Arithmetic.ZetaSouriauAttachmentMasterBridge.lean` | 1 | Retired as an ontology |
| `lean/InfoGeometry.Thermo.ModularKLDivergence.lean` | 1 | Introduces no new ontology |
| `lean/InfoGeometry.Clifford.ClNN.lean` | 1 | Ontology ownership remains in `ClNN` |
| `lean/InfoGeometry.AllExhaustive.lean` | 1 | Imports `OperatorPolynomialTaxonomy` |
| `lean/InfoGeometry.Canonical.All.lean` | 1 | Imports `OperatorPolynomialTaxonomy` |
| `lean/InfoGeometry.Canonical.AllArchetypesNativeMathlibClosurePoset.lean` | 4 | Gauge darkness & gravitational frame dragging on odd frame |
| `lean/InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPosetAudit.lean` | 1 | `#print axioms` for SplitOctonion clade |
| `lean/InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset.lean` | 17 | Gauge darkness & gravitational frame dragging |
| `lean/InfoGeometry.Canonical.ArnoldParaKahlerBCFW.lean` | 4 | Frame dragging in Arnold BCFW |
| `lean/InfoGeometry.Canonical.CantorPlabicTwistorBridge.lean` | 2 | Frame dragging in Cantor Plabic twistor bridge |
| `lean/InfoGeometry.Canonical.JaynesInductiveColimitNilpotentPoset.lean` | 2 | Frame dragging in Jaynes inductive colimit |
| `lean/InfoGeometry.Canonical.F4ResidualCoordinateRankBridge.lean` | 2 | Frame dragging in F4 residual coordinate bridge |
| `lean/InfoGeometry.Canonical.NonlinearTwinWaveOpticsBridge.lean` | 4 | Frame dragging in nonlinear twin wave optics |
| `lean/InfoGeometry.Canonical.ParaKahlerCantorBridgeExtended.lean` | 9 | Frame dragging in para-Kähler Cantor bridge |
| `lean/InfoGeometry.Canonical.PluckerCantorPlabicClusterBridge.lean` | 3 | Frame dragging in Plücker Cantor Plabic cluster bridge |
| `lean/InfoGeometry.Canonical.RealStageProjectionMurrayVonNeumann.lean` | 1 | Frame dragging in Murray-von Neumann projection |
| `lean/InfoGeometry.Canonical.H3ZornExplicitPeirceJordanSoldering.lean` | 1 | Frame dragging in H3 Zorn explicit Peirce Jordan soldering |
| `lean/InfoGeometry.OperatorAlgebra.PeirceSpine` (namespace) | 2 | Peirce spine namespace references |
| `lean/InfoGeometry.OperatorAlgebra.PeirceSpine.HiggsFrameDraggingCyclotomicSupercolorPoset.lean` | 10 | Higgs frame dragging cyclotomic supercolor poset |
| `lean/InfoGeometry.OperatorAlgebra.PeirceSpine.ParaKahlerBregmanModularNoetherPoset.lean` | 1 | Related para-Kähler Bregman modular Noether poset |
| `lean/InfoGeometry.OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealTwoSheetBridge.lean` | 1 | Related two-sheet BdG Krein chiral ideal |
| `lean/InfoGeometry.Canonical.KleinBottleV4SeamSumDifferenceWalshHadamardPoset.lean` | 1 | Frame dragging `[Σ, Φ] = {V, J} = 2 • (V • J)` |
| `lean/InfoGeometry.Canonical.CyclicMobiusCyclotomicMathlibBridge.lean` | 2 | Frame dragging in cyclic Möbius cyclotomic bridge |
| `lean/InfoGeometry.Canonical.DualBruhatHalmosKleinSeamColimitAnalyticPoset.lean` | 2 | Frame dragging in dual Bruhat Halmos Klein seam colimit |
| `lean/InfoGeometry.Canonical.FirstQuantizedAmariOperatorGeometryPoset.lean` | 2 | Frame dragging in first quantized Amari operator geometry |
| `lean/InfoGeometry.Canonical.FiveGradedKantorTanakaOspGunaydinGurseyContactPoset.lean` | 2 | Frame dragging in five graded Kantor Tanaka |
| `lean/InfoGeometry.Canonical.HestenesKreinGaussBonnetAnalyticDerivationPoset.lean` | 2 | Frame dragging in Hestenes Krein Gauss Bonnet |
| `lean/InfoGeometry.Canonical.HestenesKreinGaussBonnetMonogenicPoset.lean` | 2 | Frame dragging in Hestenes Krein Gauss Bonnet monogenic |
| `lean/InfoGeometry.Canonical.InductiveCategoricalColimitInverseLimitUnificationPoset.lean` | 2 | Frame dragging in categorical colimit unification |
| `lean/InfoGeometry.Canonical.KleinBottleSeamSumDifferenceConnectionPoset.lean` | 16 | Frame dragging `[Σ, Φ] = {V, J} = 2 • (V • J)` |
| `lean/InfoGeometry.Canonical.UnifiedAnalyticGeometricFramework.lean` | 2 | Frame dragging in unified analytic geometric framework |
| `lean/InfoGeometry.Epistemology.CoagulatedArchetypeSynthesisAudit.lean` | 1 | Audit for coagulated archetype synthesis |
| `lean/InfoGeometry.OperatorAlgebra.PeirceSpine.Basic.lean` | 2 | Basic Peirce spine |
| `lean/InfoGeometry.OperatorAlgebra.PeirceSpine.CladisticPhylogenesisBridge.lean` | — | Taxonomic subsumption, fork/join MRCA, phyloLineage (no direct frame-dragging mentions but carrier infrastructure) |
| `lean/InfoGeometry.OperatorAlgebra.PeirceSpine.CurvatureDoubleCommutator.lean` | — | Curvature double commutator |
| `lean/InfoGeometry.OperatorAlgebra.PeirceSpine.EpistemicCompilerPeirceBridge.lean` | — | Epistemic compiler Peirce bridge |

### 2.2 External / archived references (not kernel-checked owners)

| File | Match count | Notes |
|---|---|---|
| `lean/.kilo/worktrees/muddy-onion/proofs/THE_COCYCLE_COMPLEX.tex` | 5 | Archived LaTeX proof |
| `lean/.kilo/worktrees/muddy-onion/proofs/nonlinear_braid_operator.py` | 2 | Archived Python |
| `lean/.kilo/worktrees/muddy-onion/proofs/ARCHITECTURE.md` | 4 | Archived architecture doc |
| `cached/aistudio_prompt_17Kj7oLBHPfoWvQLKPwwve8pcsDezqpkG.json` | Many | Cached transcript with extensive gravitomagnetism discussion |
| `cached/aistudio_extracts/aistudio_prompt_17Kj7oLBHPfoWvQLKPwwve8pcsDezqpkG/transcript.md` | Many | Cached transcript with Machian gravitomagnetism discussion |
| `proofs/memory/2026-06-11.md` | 2 | Archived memory |
| `proofs/ARCHITECTURE.md` | 4 | Archived architecture |
| `proofs/nonlinear_braid_operator.py` | 2 | Archived Python |
| `proofs/OpticalAndreevSpinor.lean` | 1 | Archived proof |
| `verification/spinorial-core/LINEAGE_EXTENSION.md` | 1 | Lineage extension |
| `docs/CHAT_ARCHETYPE_RECOVERY_LEDGER.md` | Many | Chat archetype recovery ledger with extensive gravitomagnetism discussion |
| `docs/AUTOMATH_COLLECTIVE_PIPELINE.md` | 1 | AutoMath collective pipeline |
| `docs/GOEDEL.md` | Many | Gödel vorticity frame dragging and light cone tilt |

---

## 3. Common Mathematical Carrier (observed across owners)

The following pattern recurs identically across multiple independent Lean files. All are proved over `[Ring B]` with an idempotent `P : B` and grading `S_P = P - (1 - P)`:

### 3.1 Gravitomagnetic dipole (spin)
`Σ = [N₊, N₋] = S_P • V`

Properties:
- Pure commutator → trace zero (no gravitomagnetic monopoles)
- `Tr(Σ) = 0`
- `Tr(S_P • Σ) = Tr(V) > 0` (positive gravitoelectric mass monopole)

### 3.2 First-order Lense–Thirring / Coriolis precession
`[\Sigma, \Phi] = 2 • (V • J₅)`

Properties:
- Strictly orthogonal to velocity `\Phi`: `\{\Phi, [\Sigma, \Phi]\} = 0`
- Work-free: gravitomagnetic force deflects trajectories without changing kinetic energy `Φ² = V`
- Deflection rate `2V` (Machian frame-dragging rate)

### 3.3 Dual precession
`[\Sigma, J₅] = 2 • (V • \Phi)`

### 3.4 Second-order centrifugal / Machian reaction
`[\Sigma, [\Sigma, \Phi]] = 4 • (V² • \Phi)`

### 3.5 Nilpotent collapse / closed timelike line transmutation
`(\Sigma * \Phi)^2 = -V³`

### 3.6 Massive body / Machian scaffold condition
`V = 0 → Σ = 0 → [\Sigma, X] = 0`
- In an empty universe (no cosmic mass scaffold `V`), there is NO inertial frame dragging
- Mass scaffold is necessary and sufficient for frame dragging

### 3.7 Onsager reciprocity / transport
`L_{\Phi, J_5}(X) = L_{J_5, \Phi}(X) = 0`
- Exact Onsager reciprocal diffusion on the Tetraktys
- Jordan anticommutator `{F_\Phi, F_J} = 0`
- Difference of squares `F_\Phi² - F_J² = -8 V³`

---

## 4. Taxonomy Candidates (modeled on `AnalyticTaxonomicClade`)

The existing `AnalyticTaxonomicClade` inductive (CladeI–CladeX) classifies "analytic" across `OntologyMetaLevel` (M0–M3), `RepDepth` (L0–L5), `AnalyticSemanticSense` (SenseA–SenseD), and `AnalyticQMSBucket` (Bucket A–C). A parallel **GEM (gravito-electromagnetic) taxonomy** can be constructed with the same four axes:

| GClade | Carrier | Semantic sense | QMS bucket | MLT stratum |
|---|---|---|---|---|
| `GCladeI_GravitoElectricMonopole` | `V = {N₊, N₋}` | Gravitoelectric mass density | Bucket A | M2 |
| `GCladeII_GravitoMagneticDipole` | `Σ = [N₊, N₋]` | Gravitomagnetic spin dipole | Bucket A | M3 |
| `GCladeIII_LenseThirringCoriolis` | `[\Sigma, \Phi] = 2 V J₅` | First-order frame dragging | Bucket A | M3 |
| `GCladeIV_WorkFreeCoriolis` | `\{\Phi, [\Sigma, \Phi]\} = 0` | Traceless cyclic trace | Bucket A | M2 |
| `GCladeV_SecondOrderCentrifugal` | `[\Sigma, [\Sigma, \Phi]] = 4 V² Φ` | Machian reaction | Bucket B | M3 |
| `GCladeVI_KerrErgosphere` | `(\Sigma\Phi)^2 = -V³` | Nilpotent collapse / closed timelike | Bucket B | M3 |
| `GCladeVII_EinsteinCartanTorsion` | Torsion annihilation `dΣ = 0` | Torsion-free constraint | Bucket B | M3 |
| `GCladeVIII_OnsagerReciprocity` | `L_{\Phi,J} = L_{J,\Phi} = 0` | Transport reciprocity | Bucket A | M2 |
| `GCladeIX_ChiralSplitting` | `\Phi \pm J_5 = 2 N_\pm` | Chiral null cones | Bucket A | M2 |
| `GCladeX_MachPrinciple` | `V = 0 \implies \Sigma = 0 \implies [\Sigma, X] = 0` | No inertia without mass scaffold | Bucket B | M3 |

---

## 5. Phylogenesis Candidates (modeled on `AnalyticPhylogeneticEpoch`)

An 8-epoch causal poset for the historical development of the formalism:

| GEpoch | Meaning | Rank |
|---|---|---|
| `GEpoch1_NewtonianGravitoElectric` | Static mass monopole `V` | 0 |
| `GEpoch2_MachRelationalInertia` | Inertia from distant masses (Mach's principle) | 1 |
| `GEpoch3_LenseThirring1918` | Rotating mass drags inertial frames | 2 |
| `GEpoch4_GravitoElectromagneticSplit` | `E_g` vs `B_g` decomposition | 3 |
| `GEpoch5_WeylSpinorChiralSplit` | `N_+` / `N_-` null sheets | 4 |
| `GEpoch6_CommutatorAlgebra` | `[\Sigma, \Phi] = 2 V J₅` as Peirce algebra | 5 |
| `GEpoch7_SecondOrderCentrifugal` | `[\Sigma, [\Sigma, \Phi]] = 4 V² Φ` | 6 |
| `GEpoch8_KerrErgosphereCollapse` | `(\Sigma\Phi)^2 = -V³`, no stationary observer | 7 |

`causalEdge u v := u.rank < v.rank`, strict acyclicity via `Nat.lt_irrefl`.

---

## 6. Deduplication Candidates

The following identities appear in **multiple independent Lean files** with identical or near-identical statements. These are candidates for factorization into a shared bridge:

| Pattern | Files containing it | Suggested bridge location |
|---|---|---|
| `[\Sigma, \Phi] = 2 V J₅` | `ZornAlternativeLaws.lean`, `EinsteinCartanChiralAnomalyFrameDraggingPoset.lean`, `WheelerGodelRotatingUniverseChronologyPoset.lean`, `CoagulatedArchetypeSynthesis.lean`, `cached/aistudio_prompt...` | `GravitoElectromagneticBridge.lean` |
| `[\Sigma, J₅] = 2 V \Phi` | Same set | `GravitoElectromagneticBridge.lean` |
| `[\Sigma, [\Sigma, \Phi]] = 4 V² Φ` | `EinsteinCartanChiralAnomalyFrameDraggingPoset.lean`, `WheelerGodelRotatingUniverseChronologyPoset.lean` | `GravitoElectromagneticBridge.lean` |
| `(\Sigma\Phi)^2 = -V³` | `WheelerGodelRotatingUniverseChronologyPoset.lean`, `CoagulatedArchetypeSynthesis.lean` | `GravitoElectromagneticBridge.lean` |
| `\{\Phi, [\Sigma, \Phi]\} = 0` | `machian_gravitomagnetism_and_frame_dragging` (cached transcript), `ZornAlternativeLaws.lean` | `GravitoElectromagneticBridge.lean` |
| `V = 0 → Σ = 0 → [\Sigma, X] = 0` | Multiple transcript files | `GravitoElectromagneticBridge.lean` |

### Recommended bridge file
**`lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean`** (new file)

Structure:
```lean
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def gemFork (Pl Pr : B) : B := Pl - Pr      -- reuses cladeFork semantics
def gemJoin (Pl Pr : B) : B := Pl + Pr      -- reuses cladeJoin semantics
def gemSigma (N₊ N₋ : B) : B := N₊ * N₋ - N₋ * N₊

theorem gemFirstOrderLenseThirring {Σ Φ V J₅ : B} (...) : [Σ, Φ] = 2 • (V • J₅) := by sorry
theorem gemSecondOrderCentrifugal ... := by sorry
theorem gemWorkFreeCoriolis ... := by sorry
theorem gemNilpotentCollapse ... := by sorry
theorem gemOnsagerReciprocity ... := by sorry
theorem gemMachPrinciple {V Σ : B} ... : V = 0 → Σ = 0 → [Σ, X] = 0 := by sorry
```

**Critical:** No `sorry`, `admit`, custom axioms, or proof bypasses may be introduced. All proofs must use existing Peirce spine machinery (`peirce_nf`, `noncomm_ring`, `simp`).

---

## 7. Recommended Implementation Plan

### Phase 1: Bridge construction (kernel-checked)
Create `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean`:
- `variable {B : Type*} [Ring B]`
- `gemFork`, `gemJoin` aliases (or direct reuse of `cladeFork` / `cladeJoin`)
- `gemSigma`, `gemFirstOrderLenseThirring`, `gemSecondOrderCentrifugal`, `gemWorkFreeCoriolis`, `gemNilpotentCollapse`, `gemOnsagerReciprocity`, `gemMachPrinciple`
- All proofs via `peirce_nf hP` and `noncomm_ring`

Validation:
```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.OperatorAlgebra.PeirceSpine.GravitoElectromagneticBridge
python3 tools/infra/axiom_index.py --json InfoGeometry.OperatorAlgebra.PeirceSpine.GravitoElectromagneticBridge
python3 tools/scripts/vacuity-linter.py lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean --json
python3 tools/infra/opengauss_screener.py lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean --strict
```

### Phase 2: Consumer integration
In each existing owner that currently re-proves `[\Sigma, \Phi] = 2 V J₅` etc., add:
```lean
have hGem := gemFirstOrderLenseThirring ...
```
and replace the local proof with `exact hGem`.

Files to modify (in priority order):
1. `lean/InfoGeometry/Canonical/EinsteinCartanChiralAnomalyFrameDraggingPoset.lean`
2. `lean/InfoGeometry/Algebra/ZornAlternativeLaws.lean`
3. `lean/InfoGeometry/Canonical/WheelerGodelRotatingUniverseChronologyPoset.lean`
4. `lean/InfoGeometry/Clifford/LogCFTDeRhamApexMonodromyBridge.lean`
5. `lean/InfoGeometry/Canonical/KleinBottleSeamSumDifferenceConnectionPoset.lean`

Each consumer change must be validated with its own narrow locked build:
```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
```

### Phase 3: Taxonomy and phylogenesis classification
Add a GEM clade taxonomy to `AnalyticOntologyTaxonomyPhylogenesisPoset.lean` or a new sibling file:
- `GEMTaxonomicClade` inductive (GCladeI–GCladeX)
- `GEMPhylogeneticEpoch` inductive (GEpoch1–GEpoch8)
- `gemPrimarySense`, `gemQMSBucket`, `gemMetaLevel`, `gemRepDepth` mappings
- `gemCausalEdge_acyclic` theorem

### Phase 4: Python pipeline integration (Level 5 — navigation only)
Extend `tools/infra/evolution_taxonomy.py` with GEM-specific commit categories if needed, or extend `tools/repository_evolution/phylogeny_export.py` with optional `"declaration_links"` carrier for Lean declaration links to GEM owner files.

**Important:** The Python → Lean link is conventional (`CATEGORY_IDS` ↔ `ChangeCategory.id`), not a logical embedding. Python labels are weak rules, not kernel-checked proofs.

---

## 8. Acceptance Criteria

| Criterion | Status |
|---|---|
| `GravitoElectromagneticBridge.lean` compiles with 0 errors | Pending |
| `axiom_index.py` reports only `{propext, Classical.choice, Quot.sound}` | Pending |
| `vacuity-linter.py` reports honesty 1.0, vacuity 0.0 | Pending |
| `opengauss_screener.py --strict` passes (T17 warnings non-blocking) | Pending |
| Existing owners compile after `have hGem := ...` replacement | Pending |
| All 73 Python tests still pass | Baseline verified |
| `run_pipeline.sh --skip-lean-build` exits 0 | Baseline verified |

---

## 9. What Is NOT in Scope (per codebase disclaimers)

- **No biological interpretation:** The Lean code explicitly disclaims biological interpretation for cladistics ("taxonomic terminology is naming for the idempotents; no biological interpretation or metric-space ultrametric is inferred"). The same standard applies to gravitoelectromagnetism: these are non-commutative ring identities, not proofs of General Relativity.
- **No physical interpretation:** Lean checks a proposition at its declared type. It does not establish that a filename, docstring, or comment describes a physical proposition faithfully.
- **No topology, colimit, or analytic limit:** Unless the corresponding construction and compatibility proof are added, no topology or measure-theoretic limit is supplied.
- **No external oracle authority:** Browser oracle outputs belong in candidate/report artifacts; they do not replace Lean proofs.

---

## 10. Immediate Next Steps

1. **Preflight:** `python3 tools/infra/context_preflight.py "frame dragging gravitomagnetism unification" --include-external`
2. **Inspect** `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CladisticPhylogenesisBridge.lean` lines 25–55 for exact `cladeFork` / `cladeJoin` definitions
3. **Create candidate** `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean`
4. **Narrow locked build** on the candidate module
5. **Axiom and vacuity audit** on the candidate
6. **Consumer integration** into `EinsteinCartanChiralAnomalyFrameDraggingPoset.lean` and `ZornAlternativeLaws.lean` (narrow locked builds per consumer)
7. **Update** `docs/PIPELINE_IMPROVEMENT_AND_REFACTORING_PLAN.md` with Phase 6 (GEM unification) execution log

---

**End of report.** All claims are bounded to the Lean declarations and their actual types/hypotheses; physical interpretation remains outside the scope of kernel-checked Lean proofs.