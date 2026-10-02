# Comprehensive Repository-Wide Survey: Brute-Force Tactics & O(1) CAS Optimization Candidates

**Author**: `teamwork_preview_explorer (explorer_survey_r5_1)`  
**Parent**: `orchestrator_5` (`c310530f-678b-4c1c-948e-b8e7ff7beb38`)  
**Date**: 2026-09-22  
**Scope**: 23,137 Lean 4 source files across `lean/` (`DAG/`, `InfoGeometry/`, `Omega/`, etc.)  

---

## 1. Executive Summary

This survey provides a comprehensive census, dependency analysis, mathematical taxonomy, and prioritization matrix of all remaining computational bottlenecks and brute-force tactics (`native_decide`, `decide`, and heavy `simp` storms) across the `info-geometry-lean` repository.

### Key Metrics
- **Total Lean 4 Files in `lean/`**: 23,137
- **Files containing `native_decide`**: **587 files** (down from 588 following the surgical refactor of `lean/DAG/DiracLaplacian.lean`)
- **Total `native_decide` Occurrences**: **2,551** (line-level occurrences) / **3,059** (total token instances)
- **Files containing `decide`**: **1,064 files** (3,815 occurrences)
- **Files with `simpa using` chains**: **3,389 files** (6,805 occurrences)
- **Files with `simp only [...]` lists**: **2,596 files** (9,429 occurrences)
- **Top Single-File Hang Measured**: `lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean` took **6m 28s** to compile under `lake env lean` due to 24 VM-evaluated split-octonion multiplication proofs over $\mathbb{Q}$.
- **Top Occurrences File**: `lean/Omega/Folding/ZeckendorfSignature.lean` contains **84** `native_decide` calls.
- **Top Downstream Backbone File**: `lean/Omega/Core/Fib.lean` contains **45** `native_decide` calls and is directly imported by **69** functional modules.

---

## 2. Top-Level Module & Mathematical Domain Grouping

All 587 files containing `native_decide` reside strictly within three top-level library trees:

| Top-Level Library | File Count | `native_decide` Count | `decide` Count | `simpa using` Count | `simp only` Count | % of All ND Files |
|---|---|---|---|---|---|---|
| **`Omega`** | 436 | 2,390 | 405 | 161 | 743 | 74.3% |
| **`InfoGeometry`** | 147 | 657 | 211 | 39 | 155 | 25.0% |
| **`DAG`** | 4 | 12 | 1 | 8 | 5 | 0.7% |
| **Total** | **587** | **3,059** | **617** | **208** | **903** | **100.0%** |

*(Note: In `DAG`, only 2 files contain executable `native_decide` in code: `DAG.Dominators` [3] and `DAG.GaussianElimination` [3]. The remaining 6 occurrences in `DAG.HarmonicKMS` [5] and `DAG.HodgeTheorems` [1] are in documentation strings/comments.)*

---

### 2.1 Domain Taxonomy: `lean/InfoGeometry/` (147 files, 657 occurrences)

The `InfoGeometry` library targets differential geometry, operator algebras, exceptional Lie groups ($G_2, F_4, E_8$), split octonions, and quantum bridges.

| Sub-Domain | File Count | `native_decide` Count | Mathematical Problem Type |
|---|---|---|---|
| `Canonical` | 50 | 308 | Split-octonion bracket tables, Campbell-Meyer-Drazin inverses, Moore-Penrose borders, Klein quadrics |
| `Algebra` | 45 | 149 | Zorn matrix algebra, $G_2$ Weyl group normalization, unipotent root subgroups, Cuntz supergraded SUSY |
| `OperatorAlgebra` | 9 | 67 | $G_2$ two-automorphism theorems, Cole-Fury ideals, KMS states |
| `External` | 8 | 21 | External algebra bridges and embeddings |
| `Orthogonal` | 4 | 19 | Orthogonal group invariants and quadratic forms |
| `Arithmetic` | 4 | 18 | Riemann zeta equivalences, modular forms |
| `RootSystem` | 2 | 15 | Root lattice inner products and Weyl reflections |
| `Lie` | 5 | 12 | Lie algebra structure constants, split-octonion Cartan weights |
| `Topology` | 2 | 8 | Topological invariants, Euler characteristics |
| `Exceptional` | 5 | 8 | $G_2$ Artin presentations, Jordan algebra relations |
| `Geometry`, `Monster`, `Clifford`, `Projective`, `GromovWittenErlangen`, etc. | 13 | 22 | Clifford spinors, projective geometries, Krein spaces |

---

### 2.2 Domain Taxonomy: `lean/Omega/` (436 files, 2,390 occurrences)

The `Omega` library formalizes dynamical systems, transfer operators, dynamical zeta functions, Zeckendorf numeration, and reversible computation budgets.

| Sub-Domain | File Count | `native_decide` Count | Mathematical Problem Type |
|---|---|---|---|
| `Folding` | 67 | 736 | Zeckendorf signatures, moment sums, bin folding, collision kernels, boundary layers |
| `Zeta` | 83 | 346 | Dynamical zeta functions, cyclic determinants, necklace corrections |
| `Conclusion` | 76 | 325 | Reversible register bit budgets, minimum latch state counts, prime registers |
| `GU` (Group Unification) | 68 | 311 | Pisano periods of primes, Zeckendorf count closures, sector budgets |
| `POM` (Poset Modules) | 54 | 304 | Fibonacci cube edge parities, poset toggle orders |
| `CircleDimension` | 11 | 74 | Circle dimension bounds, Möbius bipartite colorings |
| `EA` (Entropy Algebra) | 15 | 59 | Wedderburn decompositions, reset depth spectrums |
| `GroupUnification` | 17 | 50 | Finite group word problems |
| `Core` | 3 | 47 | Foundational Fibonacci properties, fence determinants, divisibility |
| `Graph` | 2 | 25 | Transfer matrix traces and powers |
| `Combinatorics` | 3 | 24 | Fibonacci cube graphs |
| `SPG`, `HyperKernel`, `SyncKernelWeighted`, `StableArithmetic`, etc. | 37 | 69 | Weighted synchronization kernels, arithmetic bounds |

---

## 3. Active Build Status & Dependency Graph Analysis

### 3.1 Lakefile Target Structure & Inclusion
In `lakefile.lean`:
1. `DAG`: Declared with `globs := #[.andSubmodules `DAG]`. Curated entrypoint: `lean/DAG.lean`.
2. `InfoGeometry`: Declared with `globs := #[.andSubmodules `InfoGeometry]`.
   - Curated root: `lean/InfoGeometry.lean` (110 imports).
   - Curated canonical root: `lean/InfoGeometry/Canonical/All.lean` (2,202 imports).
   - Exhaustive root: `lean/InfoGeometry/AllExhaustive.lean` (12,619 imports).
3. `Omega`: Declared with `globs := #[.andSubmodules `Omega]`.
   - Exhaustive root: `lean/Omega.lean` (9,801 imports).

### 3.2 Functional Import Distribution (Excluding Umbrella Aggregators)
Among the 587 bottlenecked files:
- **Zero functional importers (Leaves / Standalone)**: **39 files (6.6%)** (36 in `InfoGeometry`, 2 in `Omega`, 1 in `DAG`).
- **1 to 4 functional importers**: **464 files (79.0%)**.
- **5 to 9 functional importers**: **44 files (7.5%)**.
- **10+ functional importers (Core Backbones)**: **40 files (6.8%)**.

### 3.3 Curated Entrypoint Membership
- **`lean/DAG.lean`**: Imports exactly **1** executable `native_decide` file:
  - `DAG.Dominators` (3 occurrences in lines 229, 237, 246).
  *(Refactoring this single file eliminates 100% of executable `native_decide` from the `DAG.lean` entrypoint!)*
- **`lean/InfoGeometry/Canonical/All.lean`**: Directly imports **9** `native_decide` files:
  1. `InfoGeometry.Canonical.G2Basis8NativeLineAlignment` (9 calls)
  2. `InfoGeometry.Canonical.LogosPartiturePoset` (7 calls)
  3. `InfoGeometry.Canonical.CyclotomicExplicitMatrixRealizations` (4 calls)
  4. `InfoGeometry.Canonical.KitaevQuantumDoubleGSDBridge` (2 calls)
  5. `InfoGeometry.Canonical.A2QutritCartanDecomposition` (1 call)
  6. `InfoGeometry.Canonical.CyclotomicNestedMatrixRealization` (1 call)
  7. `InfoGeometry.Canonical.O55LightConeSpectrumBridge` (1 call)
  8. `InfoGeometry.Canonical.AffineWeylD5WallpaperQuotient` (1 call)
  9. `InfoGeometry.Arithmetic.RiemannZetaEquivalences` (1 call, 24 downstream importers!)

---

## 4. Top 35 Bottleneck Files Ranked by `native_decide` Count

| Rank | Full Module Path | File Path | ND | Dec | SimpA | Func Importers | Entrypoint Status |
|---|---|---|---|---|---|---|---|
| 1 | `Omega.Folding.ZeckendorfSignature` | `lean/Omega/Folding/ZeckendorfSignature.lean` | 84 | 1 | 0 | 15 | In `Omega` |
| 2 | `Omega.Folding.CollisionZeta` | `lean/Omega/Folding/CollisionZeta.lean` | 79 | 1 | 0 | 8 | In `Omega` |
| 3 | `Omega.Folding.CollisionZetaOperator` | `lean/Omega/Folding/CollisionZetaOperator.lean` | 65 | 0 | 0 | 8 | In `Omega` |
| 4 | `Omega.Zeta.DynZeta` | `lean/Omega/Zeta/DynZeta.lean` | 61 | 4 | 1 | 17 | In `Omega` |
| 5 | `Omega.Zeta.CyclicDet` | `lean/Omega/Zeta/CyclicDet.lean` | 56 | 11 | 0 | 10 | In `Omega` |
| 6 | `Omega.POM.FibCubeEdgeParity` | `lean/Omega/POM/FibCubeEdgeParity.lean` | 56 | 0 | 0 | 2 | In `Omega` |
| 7 | `Omega.Folding.BoundaryLayer` | `lean/Omega/Folding/BoundaryLayer.lean` | 48 | 1 | 5 | 13 | In `Omega` |
| 8 | `Omega.Folding.MomentSum` | `lean/Omega/Folding/MomentSum.lean` | 48 | 0 | 0 | 19 | In `Omega` |
| 9 | `Omega.Core.Fib` | `lean/Omega/Core/Fib.lean` | 45 | 11 | 0 | 69 | In `Omega` (Core Backbone) |
| 10 | `Omega.Folding.Window6` | `lean/Omega/Folding/Window6.lean` | 43 | 6 | 0 | 13 | In `Omega` |
| 11 | `Omega.POM.ToggleOrder` | `lean/Omega/POM/ToggleOrder.lean` | 35 | 9 | 2 | 7 | In `Omega` |
| 12 | `Omega.Zeta.NecklaceCorrection` | `lean/Omega/Zeta/NecklaceCorrection.lean` | 34 | 1 | 2 | 5 | In `Omega` |
| 13 | `Omega.Conclusion.MinLatchesLogStates` | `lean/Omega/Conclusion/MinLatchesLogStates.lean` | 33 | 0 | 0 | 2 | In `Omega` |
| 14 | `Omega.Conclusion.PrimeRegister` | `lean/Omega/Conclusion/PrimeRegister.lean` | 31 | 2 | 6 | 11 | In `Omega` |
| 15 | `Omega.GU.FibPrimePisano` | `lean/Omega/GU/FibPrimePisano.lean` | 30 | 0 | 0 | 5 | In `Omega` |
| 16 | `Omega.GU.MinSectorBudget` | `lean/Omega/GU/MinSectorBudget.lean` | 29 | 0 | 0 | 4 | In `Omega` |
| 17 | `Omega.Folding.BinFold` | `lean/Omega/Folding/BinFold.lean` | 29 | 2 | 0 | 46 | In `Omega` (Core Backbone) |
| 18 | `Omega.Folding.CarryDefect` | `lean/Omega/Folding/CarryDefect.lean` | 29 | 0 | 0 | 2 | In `Omega` |
| 19 | `Omega.Folding.MomentTriple` | `lean/Omega/Folding/MomentTriple.lean` | 29 | 1 | 1 | 9 | In `Omega` |
| 20 | `Omega.Conclusion.ReversibleAuxBitsBudget` | `lean/Omega/Conclusion/ReversibleAuxBitsBudget.lean` | 28 | 0 | 0 | 2 | In `Omega` |
| 21 | `Omega.GU.ZeckendorfCountClosure` | `lean/Omega/GU/ZeckendorfCountClosure.lean` | 27 | 0 | 1 | 9 | In `Omega` |
| 22 | `Omega.Folding.CollisionKernel` | `lean/Omega/Folding/CollisionKernel.lean` | 27 | 0 | 0 | 17 | In `Omega` |
| 23 | `InfoGeometry.Canonical.ThreeColorNativeBracketTable` | `lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean` | 24 | 0 | 0 | 2 | In `InfoGeometry` (6m28s hang!) |
| 24 | `InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteNormalization` | `lean/InfoGeometry/Algebra/Zorn/G2NativeWeylFiniteNormalization.lean` | 24 | 0 | 0 | 2 | In `InfoGeometry` |
| 25 | `InfoGeometry.Canonical.CampbellMeyerWeakDrazin` | `lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` | 22 | 0 | 0 | 0 | In `InfoGeometry` |
| 26 | `Omega.Graph.TransferMatrix` | `lean/Omega/Graph/TransferMatrix.lean` | 22 | 1 | 2 | 16 | In `Omega` |
| 27 | `Omega.EA.Sync10ResetDepthSpectrum` | `lean/Omega/EA/Sync10ResetDepthSpectrum.lean` | 21 | 3 | 0 | 2 | In `Omega` |
| 28 | `InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations` | `lean/InfoGeometry/Canonical/SplitOctonionThreeColorChiralRelations.lean` | 20 | 0 | 0 | 9 | In `InfoGeometry` |
| 29 | `Omega.Folding.MismatchLanguage` | `lean/Omega/Folding/MismatchLanguage.lean` | 20 | 0 | 0 | 4 | In `Omega` |
| 30 | `Omega.CircleDimension.MobiusBipartiteColoring` | `lean/Omega/CircleDimension/MobiusBipartiteColoring.lean` | 20 | 0 | 0 | 2 | In `Omega` |
| 31 | `InfoGeometry.Canonical.TwelveFoldGaloisCharacterSets` | `lean/InfoGeometry/Canonical/TwelveFoldGaloisCharacterSets.lean` | 19 | 3 | 0 | 1 | In `InfoGeometry` |
| 32 | `Omega.Conclusion.Window6Collision` | `lean/Omega/Conclusion/Window6Collision.lean` | 19 | 0 | 2 | 20 | In `Omega` |
| 33 | `Omega.CircleDimension.CircleDim` | `lean/Omega/CircleDimension/CircleDim.lean` | 19 | 15 | 4 | 54 | In `Omega` (Core Backbone) |
| 34 | `Omega.Zeta.TorsionExactOrderLedgerSeeds` | `lean/Omega/Zeta/TorsionExactOrderLedgerSeeds.lean` | 18 | 0 | 0 | 4 | In `Omega` |
| 35 | `Omega.GU.FoldbinGaugeAbelian` | `lean/Omega/GU/FoldbinGaugeAbelian.lean` | 17 | 6 | 0 | 1 | In `Omega` |

---

## 5. Architectural & Mathematical Classification of Bottlenecks

### Pattern 1: Split-Octonion & Zorn Matrix Algebra
- **Examples**: `InfoGeometry.Canonical.ThreeColorNativeBracketTable`, `InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteNormalization`, `InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations`.
- **Root Cause**: Commutator $[x, y]$ and anticommutator $\{x, y\}$ computations over 8-dimensional rational vector spaces $\mathbb{Q}^8$. The Lean elaborator invokes the native compiler/VM to evaluate non-associative matrix products, taking 6+ minutes per file.
- **O(1) CAS Strategy**:
  1. Generate SymPy / SageMath Python verification script computing the 8-dimensional coordinate table.
  2. Emit definitive certificates and replace `native_decide` with definitional equality `rfl` on concrete coordinate components, or explicit matrix multiplication lemmas.

### Pattern 2: Graph Dominance & Finite Array Algorithms in DAG
- **Examples**: `DAG.Dominators`, `DAG.GaussianElimination`.
- **Root Cause**: `buildIdom` and `dominates` evaluated on static `Array Nat` literals (e.g. `#[none, some 0, some 1]`).
- **O(1) CAS Strategy**:
  1. For `DAG.Dominators`: `buildIdom` evaluates purely computationally on concrete array constants. Use `rfl` or `decide` with Decidable instance.
  2. For `DAG.GaussianElimination`: Elementary matrix product $E_2 \cdot E_2^{-1} = 1$ is an algebraic identity that can be proven via linear algebra identity without VM evaluation.

### Pattern 3: Fibonacci Sums & Zeckendorf Signatures in Omega
- **Examples**: `Omega.Folding.ZeckendorfSignature`, `Omega.Core.Fib`, `Omega.Folding.BinFold`.
- **Root Cause**: Evaluating trivial constant identities like `45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4` or `Nat.fib 14 = 377` using `native_decide`.
- **O(1) CAS Strategy**:
  - As verified experimentally during this survey: Lean kernel `by decide` proves these in < 0.1s without compiling C++ VM code!
  - Replace `by native_decide` with `by decide` / `rfl`.

### Pattern 4: Transfer Operators & Cyclic Determinants
- **Examples**: `Omega.Zeta.CyclicDet`, `Omega.Zeta.DynZeta`, `Omega.Folding.CollisionZeta`.
- **Root Cause**: Permutation power checks ($P^k = 1$) and determinant expansions over small cyclic matrices.
- **O(1) CAS Strategy**:
  - CAS certificates computing cycle decomposition and characteristic polynomials.

---

## 6. Prioritized Recommendations for Surgical O(1) CAS Refactoring

We recommend organizing the next iterations into three distinct, surgical, sandboxed sprints:

### Sprint 1: Entrypoint Hygiene & Severe Hang Elimination (Immediate Priority)
1. **`lean/DAG/Dominators.lean`**
   - **Target**: 3 `native_decide` calls (lines 229, 237, 246).
   - **Rationale**: Direct dependency of `lean/DAG.lean`. Eliminating this makes `lean/DAG.lean` completely free of executable `native_decide`!
   - **Risk**: Very low (3 local smoke test theorems).
2. **`lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean`**
   - **Target**: 24 `native_decide` calls.
   - **Rationale**: The worst single compilation hang discovered in the repo (**6m 28s**!). Refactoring this will save massive CI/build time.
   - **CAS Tool**: SymPy / SageMath split-octonion multiplication script (`scripts/cas_split_octonion_bracket.py`).
3. **`lean/InfoGeometry/Canonical/G2Basis8NativeLineAlignment.lean`**
   - **Target**: 9 `native_decide` calls.
   - **Rationale**: Directly imported in `lean/InfoGeometry/Canonical/All.lean`.
   - **CAS Tool**: $G_2$ isotropic point zero-relation certificates.
4. **`lean/DAG/GaussianElimination.lean`**
   - **Target**: 2 `native_decide` calls (lines 1231, 1237).
   - **Rationale**: Completes `DAG` library refactoring.

### Sprint 2: Core Backbone Dependency Targets (Maximum Ripple-Through Speedup)
5. **`lean/Omega/Core/Fib.lean`**
   - **Target**: 45 `native_decide` calls.
   - **Rationale**: Backbone of the entire `Omega` hierarchy (imported by **69** downstream modules!).
   - **Approach**: Replace trivial Fibonacci evaluations with `decide`/`rfl`; certify prime tests.
6. **`lean/Omega/Folding/BinFold.lean`**
   - **Target**: 29 `native_decide` calls.
   - **Rationale**: Imported by **46** downstream modules.
7. **`lean/InfoGeometry/OperatorAlgebra/G2TwoAutomorphismTheorem.lean`**
   - **Target**: 5 `native_decide` calls.
   - **Rationale**: Imported by **30** downstream modules.
8. **`lean/InfoGeometry/Algebra/Zorn/G2NativeLineFiber.lean`**
   - **Target**: 11 `native_decide` calls.
   - **Rationale**: Imported by **12** downstream modules.

### Sprint 3: High-Density Tactic Volume Targets (Bulk Elimination)
9. **`lean/Omega/Folding/ZeckendorfSignature.lean`**
   - **Target**: 84 `native_decide` calls (#1 in repo).
   - **Approach**: Fibonacci sums and NAP properties converted to `decide` / `rfl`.
10. **`lean/Omega/Folding/CollisionZeta.lean`** (79 calls) & `CollisionZetaOperator.lean` (65 calls).
11. **`lean/Omega/Zeta/CyclicDet.lean`** (56 calls) & `DynZeta.lean` (61 calls).
12. **`lean/InfoGeometry/Canonical/SplitOctonionThreeColorChiralRelations.lean`** (20 calls).

---

## 7. Artifact Index
- Survey Analysis Dataset: `/home/goutev/info-geometry-lean/.agents/explorer_survey_r5_1/survey_analysis.json`
- Comprehensive Report: `/home/goutev/info-geometry-lean/.agents/explorer_survey_r5_1/survey_report.md`
- Handoff Document: `/home/goutev/info-geometry-lean/.agents/explorer_survey_r5_1/handoff.md`
- Progress Log: `/home/goutev/info-geometry-lean/.agents/explorer_survey_r5_1/progress.md`
- Dispatch Log: `/home/goutev/info-geometry-lean/.agents/explorer_survey_r5_1/DISPATCH.md`
- Briefing: `/home/goutev/info-geometry-lean/.agents/explorer_survey_r5_1/BRIEFING.md`
