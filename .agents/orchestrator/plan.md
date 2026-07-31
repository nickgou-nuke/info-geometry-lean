# Project Plan: AlbertAlgebraGenerationsBridge Formalization

## Objectives
1. **R1: F4 Derivation Action, S3 Permutations, CKM/PMNS Matrices**
   - Create `lean/InfoGeometry/Albert/F4Action.lean`
   - Define 52D `F4Derivation` structure and action on `AlbertMatrix`
   - Define `S3` generation permutation generators (`genPerm12`, `genPerm23`, `genPerm31`)
   - Define CKM and PMNS mixing matrices as `S3`-generated or `F4`-induced rotations bridging generation Peirce spaces
   - Prove `finrank ℝ F4Derivation = 52`, `SimpleLieAlgebra F4Derivation`, `genPerm_closure`
2. **R2: Freudenthal Identity Instantiation**
   - Extend `lean/InfoGeometry/Exceptional/Freudenthal.lean`
   - Instantiate `CubicJordanDatum` for `AlbertMatrix`
   - Prove `freudenthal_identity_full`: `adjointQuad (adjointQuad X) = normCubic X • X` for 27D algebra
3. **R3: GAP Structure Constants Script**
   - Create `tools/gap/f4_generators.g`
   - Validate 52D `F4` Lie algebra structure constants with internal assertions (`Assert`)
4. **R4: Zero-Sorry Standard & Quality**
   - No `sorry`s, no warnings, build cleanly under `lake build`

## Phased Approach
- **Phase 0: Codebase Survey & Requirement Mapping**
  - Dispatch 3 Explorers in parallel to inspect existing files in `lean/InfoGeometry/Albert/`, `lean/InfoGeometry/Exceptional/`, `tools/gap/`, etc.
  - Compile `PROJECT.md` containing Architecture, Feature Inventory, Milestones, and Interface Contracts.
- **Phase 1: Milestone Decomposition & Execution**
  - Execute milestones using Explorer -> Worker -> Reviewer -> Challenger -> Auditor iteration loops.
  - Verification with Lake and GAP runs via subagents.
- **Phase 2: Final Integration & E2E Validation**
  - Validate all targets build without warnings or sorrys, GAP script asserts cleanly.
