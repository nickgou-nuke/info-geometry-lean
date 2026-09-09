# Project: AlbertAlgebraGenerationsBridge Formalization

## Architecture
- `lean/InfoGeometry/Albert/F4Action.lean`: Defines 52-dimensional Lie algebra `F4Derivation` acting linearly on `AlbertMatrix` (preserving Jordan product), $S_3$ generation permutations (`genPerm12`, `genPerm23`, `genPerm31`), and CKM (quark) / PMNS (lepton) mixing matrices as $S_3$-generated or $F_4$-induced rotation elements bridging generation Peirce spaces. Proves `finrank ℝ F4Derivation = 52`, `SimpleLieAlgebra F4Derivation`, and `genPerm_closure`.
- `lean/InfoGeometry/Exceptional/Freudenthal.lean`: Extends existing Freudenthal module to instantiate `CubicJordanDatum` for `AlbertMatrix` (with linear maps for trace and cubic norm trilinearization) and proves `freudenthal_identity_full`: `adjointQuad (adjointQuad X) = normCubic X • X` for the full 27D algebra on concrete coordinates.
- `tools/gap/f4_generators.g`: Computes 52D $F_4 = \mathfrak{aut}(J_3(\mathbb{O}_s))$ Lie algebra structure constants with internal assertions (`Assert`), setting `OnBreak` error handler to ensure non-zero exit code on assertion failure.

## Code Layout
- `lean/InfoGeometry/Albert/F4Action.lean`
- `lean/InfoGeometry/Exceptional/Freudenthal.lean`
- `tools/gap/f4_generators.g`

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | F4Derivation structure | 52-dimensional Lie algebra structure (`Fin 52 → ℝ`) acting on `AlbertMatrix` | Milestone 1 | R1 |
| 2 | F4Derivation finrank theorem | Proof that `FiniteDimensional.finrank ℝ F4Derivation = 52` | Milestone 1 | R1 |
| 3 | SimpleLieAlgebra instance | Proof of `SimpleLieAlgebra F4Derivation` | Milestone 1 | R1 |
| 4 | S3 permutation generators | Definitions of `genPerm12`, `genPerm23`, `genPerm31` on Peirce spaces | Milestone 1 | R1 |
| 5 | genPerm_closure theorem | Proof of 6-element $S_3$ generation permutation group closure | Milestone 1 | R1 |
| 6 | CKM and PMNS mixing matrices | Explicit CKM and PMNS $3 \times 3$ rotation matrices bridging generation Peirce spaces | Milestone 1 | R1 |
| 7 | CubicJordanDatum instantiation | Instantiate `CubicJordanDatum` for `AlbertMatrix` in Freudenthal.lean | Milestone 2 | R2 |
| 8 | freudenthal_identity_full | Proof of `adjointQuad (adjointQuad X) = normCubic X • X` for full 27D algebra | Milestone 2 | R2 |
| 9 | Zero-sorry proof standard | Zero sorrys/warnings using concrete tactics (`native_decide`, `ring_nf`, etc.) | Milestone 1, Milestone 2 | R4 |
| 10 | GAP f4_generators.g script | Computation of 52D $F_4$ structure constants with `Assert` and non-zero failure exit | Milestone 3 | R3 |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| 1 | R1: F4Action.lean | Create `lean/InfoGeometry/Albert/F4Action.lean` with F4Derivation, finrank=52, SimpleLieAlgebra, S3 generators, genPerm_closure, CKM/PMNS matrices | None | PLANNED |
| 2 | R2: Freudenthal.lean | Extend `lean/InfoGeometry/Exceptional/Freudenthal.lean` with CubicJordanDatum instantiation and freudenthal_identity_full | None | PLANNED |
| 3 | R3: GAP f4_generators.g | Create `tools/gap/f4_generators.g` validating 52D structure constants with Assert | None | PLANNED |

## Interface Contracts
### `F4Action.lean` ↔ `Generations.lean` / `CubicJordanOs.lean`
- `AlbertMatrix`: 27D structure `{ α₁, α₂, α₃ : ℝ, z₁, z₂, z₃ : SplitOct }` or `RealAlbertMatrix`.
- `F4Derivation`: 52D Lie algebra vector space with `LieRing` and `LieAlgebra ℝ` instances.
- Action: `act : F4Derivation → AlbertMatrix → AlbertMatrix` satisfying `act D (X ∘ Y) = (act D X) ∘ Y + X ∘ (act D Y)`.
- Permutations: `genPerm12`, `genPerm23`, `genPerm31 : AlbertMatrix → AlbertMatrix`.

### `Freudenthal.lean` ↔ `CubicJordanDatum`
- `CubicJordanDatum AlbertMatrix` instance with `traceBilin`, `normCubic`, `adjointQuad`, `normTrilin`.
- `freudenthal_identity_full (X : AlbertMatrix) : adjointQuad (adjointQuad X) = normCubic X • X`.
