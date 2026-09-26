# Comprehensive Downstream Consumer & Proposition Fidelity Audit
**Target File**: `lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean`  
**Agent**: `explorer_bracket_2` (teamwork_preview_explorer)  
**Date**: 2026-09-22  

---

## Executive Summary

`InfoGeometry.Canonical.ThreeColorNativeBracketTable` defines the native commutator and anticommutator operations on `StandardRationalSplitOctonion` (the 8-dimensional rational Zorn vector matrix representation of split-octonions) and computes the complete three-colour chiral bracket table.

- **Total Declarations**: 27 (2 definitions, 1 simp-proved theorem, and 24 `native_decide` theorems).
- **Bottlenecks Targeted for CAS / O(1) Refactoring**: Exactly 24 theorems proved via `native_decide` (or `cases ... <;> native_decide`).
- **Direct Downstream Dependents**:
  1. `lean/InfoGeometry/Canonical/RiemannSurprisalFluxAudit.lean` (Direct proof consumer via `unfold nativeCommutator` and `simpa using nativeSigmaPlusSigmaMinus_...`)
  2. `lean/InfoGeometry/Canonical/SplitOctonionSixSectorBridge.lean` (Direct import, carrier of chiral sector bridge)
  3. `lean/InfoGeometry/AllExhaustive.lean` (Global umbrella module importing at line 6134)
- **Transitive Downstream Dependents**:
  1. `lean/InfoGeometry/Canonical/All.lean` (Canonical library umbrella target `InfoGeometryCanonical`)
  2. `lean/InfoGeometry/Canonical/SplitOctonionChiralFrame.lean`
  3. `lean/InfoGeometry/Canonical/SplitOctonionSixSectorFin3.lean`
  4. `lean/InfoGeometry/Quantum/GeometricTensorSplitOctonionChiralFrame.lean`
- **Proposition Fidelity Status (Test 2.5)**: ZERO regression tolerance. All 27 declaration identifiers, argument bindings, LHS/RHS types, and 19 `@[simp]` attributes must remain strictly invariant.

---

## 1. Downstream Consumers Analysis

### 1.1 Direct Consumers

#### A. `lean/InfoGeometry/Canonical/RiemannSurprisalFluxAudit.lean`
- **Import**: Line 5: `import InfoGeometry.Canonical.ThreeColorNativeBracketTable`
- **Usage Location**: Lines 218–243, theorem `nativeCircularChiralLadderRelations`:
  ```lean
  theorem nativeCircularChiralLadderRelations
      (c : SplitOctonionColour) :
      nativeCommutator fundamentalSymmetry (modularSigmaPlus c) =
          (2 : ℚ) • modularSigmaPlus c ∧
      nativeCommutator fundamentalSymmetry (modularSigmaMinus c) =
          (-2 : ℚ) • modularSigmaMinus c ∧
      nativeCommutator (modularSigmaPlus c) (modularSigmaMinus c) =
          fundamentalSymmetry ∧
      nativeAnticommutator (modularSigmaPlus c) (modularSigmaMinus c) =
          rationalBasis .one ∧
      splitOctonionMulQ (modularSigmaPlus c) (modularSigmaPlus c) = 0 ∧
      splitOctonionMulQ (modularSigmaMinus c) (modularSigmaMinus c) = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold nativeCommutator
      rw [fundamentalSymmetry_mul_modularSigmaPlus,
        modularSigmaPlus_mul_fundamentalSymmetry]
      module
    · unfold nativeCommutator
      rw [fundamentalSymmetry_mul_modularSigmaMinus,
        modularSigmaMinus_mul_fundamentalSymmetry]
      module
    · simpa using nativeSigmaPlusSigmaMinus_commutator c c
    · simpa using nativeSigmaPlusSigmaMinus_anticommutator c c
    · exact modularSigmaPlus_sq_zero c
    · exact modularSigmaMinus_sq_zero c
  ```
- **Critical Coupling Mechanisms**:
  1. `unfold nativeCommutator` (lines 231, 235): Requires that `nativeCommutator` remains definitionally equal to `splitOctonionMulQ x y - splitOctonionMulQ y x`. If `nativeCommutator` is redefined or made irreducible/opaque, `unfold` fails.
  2. `simpa using nativeSigmaPlusSigmaMinus_commutator c c` (line 239): The theorem `nativeSigmaPlusSigmaMinus_commutator` proves:
     `nativeCommutator (modularSigmaPlus c) (modularSigmaMinus d) = if c = d then fundamentalSymmetry else 0`
     When specialized to `c c`, `if c = c ...` simplifies to `fundamentalSymmetry`. Any change to this theorem's name, parameter structure, or RHS representation will immediately break `simpa`.
  3. `simpa using nativeSigmaPlusSigmaMinus_anticommutator c c` (line 240): The theorem `nativeSigmaPlusSigmaMinus_anticommutator` proves:
     `nativeAnticommutator (modularSigmaPlus c) (modularSigmaMinus d) = if c = d then rationalBasis .one else 0`
     When specialized to `c c`, `if c = c ...` simplifies to `rationalBasis .one`.

#### B. `lean/InfoGeometry/Canonical/SplitOctonionSixSectorBridge.lean`
- **Import**: Line 3: `import InfoGeometry.Canonical.ThreeColorNativeBracketTable`
- **Analysis**:
  `SplitOctonionSixSectorBridge.lean` builds upon the split-octonion chiral Zorn representation (`modularSigmaPlus`, `modularSigmaMinus`, `modularNPlus`, `modularNMinus`), defining the 6-sector basis and null paravector states. It operates in `namespace InfoGeometry.Canonical` where `ThreeColorNativeBracketTable.lean` also lives. It ensures the environment remains harmonious without simp-set divergence or typeclass collisions.

#### C. `lean/InfoGeometry/AllExhaustive.lean`
- **Import**: Line 6134: `import InfoGeometry.Canonical.ThreeColorNativeBracketTable`
- **Analysis**:
  The global repository index module. Any compile-time breakage, parse error, or signature drift immediately breaks `lake build InfoGeometry` and repository-level validation.

---

### 1.2 Transitive Consumers

```
ThreeColorNativeBracketTable
  ├── RiemannSurprisalFluxAudit
  │     └── All.lean (InfoGeometryCanonical target)
  │     └── AllExhaustive.lean
  └── SplitOctonionSixSectorBridge
        └── SplitOctonionChiralFrame
              ├── SplitOctonionSixSectorFin3
              └── GeometricTensorSplitOctonionChiralFrame
```

---

## 2. Exhaustive Declaration Catalog (All 27 Declarations)

The file contains 2 definitions and 25 theorems (total 27 declarations). 24 of these theorems are bottlenecked by `native_decide` and are the primary targets of the CAS O(1) compression refactoring.

### Table of Declarations

| # | Declaration Name | Kind | Attributes | Full Type Signature | Current Proof | Downstream Usage |
|---|------------------|------|------------|---------------------|---------------|------------------|
| 1 | `nativeCommutator` | `def` | - | `(x y : StandardRationalSplitOctonion) : StandardRationalSplitOctonion := splitOctonionMulQ x y - splitOctonionMulQ y x` | Definition | Unfolded in `RiemannSurprisalFluxAudit.lean:231,235`; head for 15 theorems |
| 2 | `nativeAnticommutator` | `def` | - | `(x y : StandardRationalSplitOctonion) : StandardRationalSplitOctonion := splitOctonionMulQ x y + splitOctonionMulQ y x` | Definition | Used in `RiemannSurprisalFluxAudit.lean:226`; head for 10 theorems |
| 3 | `nativeCommutator_self` | `theorem` | `@[simp]` | `(x : StandardRationalSplitOctonion) : nativeCommutator x x = 0` | `simp [nativeCommutator]` | Canonical self-commutator reduction |
| 4 | `nativeAnticommutator_sigmaPlus_sigmaPlus` | `theorem` | `@[simp]` | `(c d : SplitOctonionColour) : nativeAnticommutator (modularSigmaPlus c) (modularSigmaPlus d) = 0` | `cases c <;> cases d <;> native_decide` | Simp normal form for chiral raising anticommutators |
| 5 | `nativeAnticommutator_sigmaMinus_sigmaMinus` | `theorem` | `@[simp]` | `(c d : SplitOctonionColour) : nativeAnticommutator (modularSigmaMinus c) (modularSigmaMinus d) = 0` | `cases c <;> cases d <;> native_decide` | Simp normal form for chiral lowering anticommutators |
| 6 | `nativeSigmaPlus_red_green_commutator` | `theorem` | - | `: nativeCommutator (modularSigmaPlus .red) (modularSigmaPlus .green) = (2 : ℚ) • modularSigmaMinus .blue` | `native_decide` | Explicit colour triality bracket |
| 7 | `nativeSigmaPlus_red_blue_commutator` | `theorem` | - | `: nativeCommutator (modularSigmaPlus .red) (modularSigmaPlus .blue) = (-2 : ℚ) • modularSigmaMinus .green` | `native_decide` | Explicit colour triality bracket |
| 8 | `nativeSigmaPlus_green_blue_commutator` | `theorem` | - | `: nativeCommutator (modularSigmaPlus .green) (modularSigmaPlus .blue) = (2 : ℚ) • modularSigmaMinus .red` | `native_decide` | Explicit colour triality bracket |
| 9 | `nativeSigmaMinus_red_green_commutator` | `theorem` | - | `: nativeCommutator (modularSigmaMinus .red) (modularSigmaMinus .green) = (-2 : ℚ) • modularSigmaPlus .blue` | `native_decide` | Explicit colour triality bracket |
| 10 | `nativeSigmaMinus_red_blue_commutator` | `theorem` | - | `: nativeCommutator (modularSigmaMinus .red) (modularSigmaMinus .blue) = (2 : ℚ) • modularSigmaPlus .green` | `native_decide` | Explicit colour triality bracket |
| 11 | `nativeSigmaMinus_green_blue_commutator` | `theorem` | - | `: nativeCommutator (modularSigmaMinus .green) (modularSigmaMinus .blue) = (-2 : ℚ) • modularSigmaPlus .red` | `native_decide` | Explicit colour triality bracket |
| 12 | `nativeSigmaPlusSigmaMinus_commutator` | `theorem` | `@[simp]` | `(c d : SplitOctonionColour) : nativeCommutator (modularSigmaPlus c) (modularSigmaMinus d) = if c = d then fundamentalSymmetry else 0` | `cases c <;> cases d <;> native_decide` | Directly called in `RiemannSurprisalFluxAudit.lean:239` via `simpa using ...` |
| 13 | `nativeSigmaPlusSigmaMinus_anticommutator` | `theorem` | `@[simp]` | `(c d : SplitOctonionColour) : nativeAnticommutator (modularSigmaPlus c) (modularSigmaMinus d) = if c = d then rationalBasis .one else 0` | `cases c <;> cases d <;> native_decide` | Directly called in `RiemannSurprisalFluxAudit.lean:240` via `simpa using ...` |
| 14 | `nativeNPlus_sigmaPlus_commutator` | `theorem` | `@[simp]` | `(c : SplitOctonionColour) : nativeCommutator modularNPlus (modularSigmaPlus c) = modularSigmaPlus c` | `cases c <;> native_decide` | Simp eigenvalue (+1) for NPlus on SigmaPlus |
| 15 | `nativeNPlus_sigmaPlus_anticommutator` | `theorem` | `@[simp]` | `(c : SplitOctonionColour) : nativeAnticommutator modularNPlus (modularSigmaPlus c) = modularSigmaPlus c` | `cases c <;> native_decide` | Simp anticommutator for NPlus and SigmaPlus |
| 16 | `nativeNMinus_sigmaPlus_commutator` | `theorem` | `@[simp]` | `(c : SplitOctonionColour) : nativeCommutator modularNMinus (modularSigmaPlus c) = -modularSigmaPlus c` | `cases c <;> native_decide` | Simp eigenvalue (-1) for NMinus on SigmaPlus |
| 17 | `nativeNMinus_sigmaPlus_anticommutator` | `theorem` | `@[simp]` | `(c : SplitOctonionColour) : nativeAnticommutator modularNMinus (modularSigmaPlus c) = modularSigmaPlus c` | `cases c <;> native_decide` | Simp anticommutator for NMinus and SigmaPlus |
| 18 | `nativeNPlus_sigmaMinus_commutator` | `theorem` | `@[simp]` | `(c : SplitOctonionColour) : nativeCommutator modularNPlus (modularSigmaMinus c) = -modularSigmaMinus c` | `cases c <;> native_decide` | Simp eigenvalue (-1) for NPlus on SigmaMinus |
| 19 | `nativeNPlus_sigmaMinus_anticommutator` | `theorem` | `@[simp]` | `(c : SplitOctonionColour) : nativeAnticommutator modularNPlus (modularSigmaMinus c) = modularSigmaMinus c` | `cases c <;> native_decide` | Simp anticommutator for NPlus and SigmaMinus |
| 20 | `nativeNMinus_sigmaMinus_commutator` | `theorem` | `@[simp]` | `(c : SplitOctonionColour) : nativeCommutator modularNMinus (modularSigmaMinus c) = modularSigmaMinus c` | `cases c <;> native_decide` | Simp eigenvalue (+1) for NMinus on SigmaMinus |
| 21 | `nativeNMinus_sigmaMinus_anticommutator` | `theorem` | `@[simp]` | `(c : SplitOctonionColour) : nativeAnticommutator modularNMinus (modularSigmaMinus c) = modularSigmaMinus c` | `cases c <;> native_decide` | Simp anticommutator for NMinus and SigmaMinus |
| 22 | `nativeNPlus_NMinus_commutator` | `theorem` | `@[simp]` | `: nativeCommutator modularNPlus modularNMinus = 0` | `native_decide` | Simp bracket for idempotent commuting |
| 23 | `nativeNPlus_NMinus_anticommutator` | `theorem` | `@[simp]` | `: nativeAnticommutator modularNPlus modularNMinus = 0` | `native_decide` | Simp bracket for idempotent orthogonality |
| 24 | `nativeNPlus_self_commutator` | `theorem` | `@[simp]` | `: nativeCommutator modularNPlus modularNPlus = 0` | `native_decide` | Simp bracket for idempotent self-commutator |
| 25 | `nativeNPlus_self_anticommutator` | `theorem` | `@[simp]` | `: nativeAnticommutator modularNPlus modularNPlus = (2 : ℚ) • modularNPlus` | `native_decide` | Simp bracket for idempotent self-anticommutator |
| 26 | `nativeNMinus_self_commutator` | `theorem` | `@[simp]` | `: nativeCommutator modularNMinus modularNMinus = 0` | `native_decide` | Simp bracket for idempotent self-commutator |
| 27 | `nativeNMinus_self_anticommutator` | `theorem` | `@[simp]` | `: nativeAnticommutator modularNMinus modularNMinus = (2 : ℚ) • modularNMinus` | `native_decide` | Simp bracket for idempotent self-anticommutator |

---

## 3. Strict Proposition Fidelity Requirements (Test 2.5)

To pass Test 2.5 ("Proposition Fidelity & Anti-Facade Audit") and guarantee zero regressions across downstream consumers, the refactored file MUST satisfy the following five invariants:

### Invariant 1: Zero Renaming & Zero Omission
- Every one of the 27 declaration identifiers must exist verbatim in the refactored file.
- Exactly 27 declarations must be exposed in `namespace InfoGeometry.Canonical`.
- No helper lemmas or internal CAS certificates may replace the public names.

### Invariant 2: Character-Level Proposition Rigor
- Argument lists must have the exact same binder types and order:
  - `(c d : SplitOctonionColour)` for the 4 binary colour theorems (`#4, #5, #12, #13`).
  - `(c : SplitOctonionColour)` for the 8 unary colour theorems (`#14–#21`).
  - `(x : StandardRationalSplitOctonion)` for `nativeCommutator_self` (`#3`).
  - No arguments (closed terms) for the 6 explicit colour commutator theorems (`#6–#11`) and the 6 idempotent bracket theorems (`#22–#27`).
- Equational RHS terms must be syntactically identical:
  - `#6`: `(2 : ℚ) • modularSigmaMinus .blue`
  - `#7`: `(-2 : ℚ) • modularSigmaMinus .green`
  - `#8`: `(2 : ℚ) • modularSigmaMinus .red`
  - `#9`: `(-2 : ℚ) • modularSigmaPlus .blue`
  - `#10`: `(2 : ℚ) • modularSigmaPlus .green`
  - `#11`: `(-2 : ℚ) • modularSigmaPlus .red`
  - `#12`: `if c = d then fundamentalSymmetry else 0`
  - `#13`: `if c = d then rationalBasis .one else 0`
  - `#14`: `modularSigmaPlus c`
  - `#16`: `-modularSigmaPlus c`
  - `#18`: `-modularSigmaMinus c`
  - `#20`: `modularSigmaMinus c`
  - `#25`: `(2 : ℚ) • modularNPlus`
  - `#27`: `(2 : ℚ) • modularNMinus`

### Invariant 3: Exact Attribute Fidelity
- All 19 declarations marked `@[simp]` must retain `@[simp]`.
- The 6 explicit triality theorems (`#6–#11`) must remain unannotated (as in the original file) to avoid looping or degrading simplifier performance.
- The section must remain `noncomputable section`.

### Invariant 4: Definitional Integrity of Definitions
- `def nativeCommutator (x y : StandardRationalSplitOctonion) : StandardRationalSplitOctonion := splitOctonionMulQ x y - splitOctonionMulQ y x`
- `def nativeAnticommutator (x y : StandardRationalSplitOctonion) : StandardRationalSplitOctonion := splitOctonionMulQ x y + splitOctonionMulQ y x`
- `unfold nativeCommutator` in `RiemannSurprisalFluxAudit.lean` depends definitionally on this exact expression.

### Invariant 5: Anti-Facade Compliance
- Zero `sorry`, `admit`, `axiom`, or stubbing.
- Proofs must rely on verified CAS certificates (e.g., polynomial/integer kernel evaluations or `decide` with precomputed tables) or definitional equality (`rfl`), completely eliminating `native_decide`.

---

## 4. Compilation & Verification Target Requirements

When `ThreeColorNativeBracketTable.lean` is refactored, the following verification pipeline must be executed sequentially with build locks:

### 4.1 Target Sequence

1. **Self Target**:
   ```bash
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.ThreeColorNativeBracketTable
   ```
2. **Direct Downstream Proof Consumer**:
   ```bash
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.RiemannSurprisalFluxAudit
   ```
3. **Direct Downstream Bridge Consumer**:
   ```bash
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.SplitOctonionSixSectorBridge
   ```
4. **Transitive Downstream Chiral Chain**:
   ```bash
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.SplitOctonionChiralFrame InfoGeometry.Canonical.SplitOctonionSixSectorFin3
   ```
5. **Canonical Umbrella Library**:
   ```bash
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometryCanonical
   ```

### 4.2 Single Composite Build Command
For rapid end-to-end verification under lock:
```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.ThreeColorNativeBracketTable \
  InfoGeometry.Canonical.RiemannSurprisalFluxAudit \
  InfoGeometry.Canonical.SplitOctonionSixSectorBridge \
  InfoGeometry.Canonical.SplitOctonionChiralFrame \
  InfoGeometryCanonical
```

---

## 5. Conclusion and Recommendations for Implementer

1. **Preserve Exact Ast Structure**: The downstream proof in `RiemannSurprisalFluxAudit.lean` is brittle to any alteration in the `if c = d then ... else ...` form of theorems #12 and #13.
2. **Elimination of `native_decide`**: Replacing all 24 `native_decide` proofs with O(1) integer kernel certificates or `decide` will completely eliminate the Lean VM native compilation overhead in this file.
3. **Sandbox First**: Any replacement candidate must be validated in an isolated sandbox (`.agents/sandbox_...`) before modifying live code.
