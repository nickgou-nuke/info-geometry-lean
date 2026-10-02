# Exploration Synthesis: ThreeColorNativeBracketTable O(1) Refactoring

## 1. Executive Summary & Root Cause Analysis
- **Target**: `lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean` (160 lines, 24 `native_decide` calls).
- **Axiomatic Corruption**: The current live file depends on the untrusted VM reflection axioms `Lean.ofReduceBool` and `Lean.trustCompiler` solely due to `native_decide`.
- **Root Cause of `decide` Failure**: In Lean 4 Core (`Init.Data.Rat.Basic`), the arithmetic operations `Rat.mul`, `Rat.add`, `Rat.sub`, and `Rat.inv` are annotated `@[irreducible]`. The Lean kernel is strictly forbidden from unfolding irreducible constants during `decide` reduction, stalling on `match (Rat.mul ...).num with`.
- **Why `ZornCell ℤ` Worked with `decide`**: In `InfoGeometry/Algebra/Zorn/ThreeColorNativeBracketTable.lean`, the carrier is over `ℤ`. Integer operations (`Int.add`, `Int.mul`, `Int.neg`) are reducible pattern matches on constructors `Int.ofNat`/`Int.negSucc`, allowing kernel reduction via `decide`.
- **Solution Strategy**: The Lean kernel can evaluate rational expressions when directed by `simp` and algebraic term tactics (`ring`) or by applying structural theorems already proven in `SplitOctonionThreeColorChiralRelations.lean`.

## 2. Declaration Breakdown & Proof Architecture
The 24 `native_decide` theorems partition cleanly into:

### Group 1: 14 Pure Structural Theorems (Zero Coordinate Calculation Needed)
- Theorems:
  - `nativeNPlus_sigmaPlus_commutator`
  - `nativeNPlus_sigmaPlus_anticommutator`
  - `nativeNMinus_sigmaPlus_commutator`
  - `nativeNMinus_sigmaPlus_anticommutator`
  - `nativeNPlus_sigmaMinus_commutator`
  - `nativeNPlus_sigmaMinus_anticommutator`
  - `nativeNMinus_sigmaMinus_commutator`
  - `nativeNMinus_sigmaMinus_anticommutator`
  - `nativeNPlus_NMinus_commutator`
  - `nativeNPlus_NMinus_anticommutator`
  - `nativeNPlus_self_commutator`
  - `nativeNPlus_self_anticommutator`
  - `nativeNMinus_self_commutator`
  - `nativeNMinus_self_anticommutator`
- **Proof Technique**: All these relations are immediate algebraic consequences of `@[simp]` lemmas in `SplitOctonionThreeColorChiralRelations.lean` (`splitOctonionMulQ modularNPlus ...`, `modularNPlus_mul_modularNMinus`, etc.).
- Proven instantly in < 0.05s via:
  - `by simp [nativeCommutator]` (for commutators)
  - `by simp [nativeAnticommutator, two_smul]` (for anticommutators)

### Group 2: 6 Explicit Color Triality Commutators
- Theorems:
  - `nativeSigmaPlus_red_green_commutator`
  - `nativeSigmaPlus_red_blue_commutator`
  - `nativeSigmaPlus_green_blue_commutator`
  - `nativeSigmaMinus_red_green_commutator`
  - `nativeSigmaMinus_red_blue_commutator`
  - `nativeSigmaMinus_green_blue_commutator`
- **Proof Technique**: Functional extensionality over the 8 basis elements:
  ```lean
  funext b; fin_cases b <;>
    simp [nativeCommutator, modularSigmaPlus, modularSigmaMinus,
      modularJ, phaseAxis, colourUnit, fundamentalSymmetry,
      rationalBasis, splitOctonionMulQ, splitQuaternionOfQ,
      splitQuaternionLPartQ, splitQuaternionAddQ, splitQuaternionMulQ,
      splitQuaternionConjQ, splitOctonionOfQuaternionPairQ, Pi.single] <;>
    ring
  ```

### Group 3: 4 Parametric Theorems (`SplitOctonionColour` Pairs)
- Theorems:
  - `nativeAnticommutator_sigmaPlus_sigmaPlus`
  - `nativeAnticommutator_sigmaMinus_sigmaMinus`
  - `nativeSigmaPlusSigmaMinus_commutator`
  - `nativeSigmaPlusSigmaMinus_anticommutator`
- **Proof Technique**: Diagonal cases reduce immediately via existing squares (`modularSigmaPlus_sq_zero`, `modularPolarized_one`, etc.). Off-diagonal cases reduce via explicit pairs `(red, green)`, `(red, blue)`, `(green, blue)` and symmetry `nativeAnticommutator_comm`, avoiding monolithic heartbeat exhaustion.

## 3. CAS Certification
- Script: `.agents/explorer_bracket_3/cas_three_color_bracket_certificate.py`
- Certified all 24 bracket theorems symbolically in 0.18 seconds over $\mathbb{Q}$.
- Certificate JSON: `.agents/explorer_bracket_3/cas_three_color_bracket_certificate.json` (24/24 `true`).

## 4. Proposition Fidelity (Test 2.5) & Downstream Safety
- Exactly 27 declarations cataloged.
- 100% preservation of names, binders, types, and equational RHS.
- All 19 `@[simp]` attributes retained.
- Verified downstream targets:
  - `InfoGeometry.Canonical.RiemannSurprisalFluxAudit`
  - `InfoGeometry.Canonical.SplitOctonionSixSectorBridge`
  - `InfoGeometry.Canonical.SplitOctonionChiralFrame`
  - `InfoGeometryCanonical`
