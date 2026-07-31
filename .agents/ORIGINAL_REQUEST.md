# Original User Request

## Initial Request — 2026-08-01T01:19:34+03:00

Formalize the remaining components of the `AlbertAlgebraGenerationsBridge` in Lean 4, specifically the `F4` derivation algebra acting on the split Albert algebra `J_3(O_s)`, the `CubicJordanDatum` instantiation for the Freudenthal identity, and the associated GAP generator script for `F4`.

Working directory: `/home/goutev/repos/info-geometry-lean`
Integrity mode: benchmark

## Requirements

### R1. F4 Derivation Action, S3 Permutations, CKM and PMNS Matrices
Create `lean/InfoGeometry/Albert/F4Action.lean` defining the 52-dimensional `F4Derivation` structure and its action on `AlbertMatrix`. Must include the `S3` generation permutation generators `genPerm12`, `genPerm23`, `genPerm31`. Furthermore, define the CKM (quark) and PMNS (lepton) mixing matrices as explicit `S3`-generated or `F4`-induced rotation elements bridging the generation Peirce spaces. Must prove `FiniteDimensional.finrank ℝ F4Derivation = 52`, `SimpleLieAlgebra F4Derivation`, and `genPerm_closure`.

### R2. Freudenthal Identity Instantiation
Extend `lean/InfoGeometry/Exceptional/Freudenthal.lean` to instantiate `CubicJordanDatum` for `AlbertMatrix`, and prove `freudenthal_identity_full`: `adjointQuad (adjointQuad X) = normCubic X • X` for the full 27D algebra using concrete coordinates.

### R3. GAP Structure Constants Script
Create `tools/gap/f4_generators.g` to compute the `F4` Lie algebra structure constants verifying the derivation definitions.

### R4. Zero-Sorry Proof Standard
All theorems must be proved using `native_decide` or `ring_nf` (or similar tactics) on concrete coordinates without relying on `sorry`.

## Acceptance Criteria

### Verification
- [ ] `lake build InfoGeometry.Albert.F4Action` completes successfully with 0 warnings and 0 `sorry`s.
- [ ] `lake build InfoGeometry.Exceptional.Freudenthal` completes successfully with 0 warnings and 0 `sorry`s.
- [ ] `gap tools/gap/f4_generators.g` runs successfully. The script must contain internal assertions (`Assert`) that validate the 52D structure constants and exit with a non-zero code if any check fails.
