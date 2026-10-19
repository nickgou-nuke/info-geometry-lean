# Ground-truth contract: Majorana sheet kernels and KKT projector sectors

## Claim and scope

On `DoubledSpace E`, identify the fixed vectors of the KKT-core positive and
negative grading projectors for `doubledSpaceCl11Action` with the canonical
`plusSheet` and `minusSheet`. Compose these identifications with the existing
creation/annihilation kernel theorems. This is an algebraic operator identity
on `DoubledSpace E` (where `E` is any complete real inner-product space).

## Owner evidence

- `Krein/MajoranaSheetConnectors.lean` proves creation and annihilation kernels
  are `plusSheet` and `minusSheet`.
- `Quantum/RealSplitClifford.lean` defines `doubledSpaceCl11Action`, with
  `eps = spectral_epsilon`.
- `Canonical/KreinMajoranaZeroModeBlock.lean` defines its zero/cozero projectors
  as the KKT-core plus/minus grading projectors.
- `Krein/PolarizedSector.lean` identifies `spectralPlusProj` and
  `spectralMinusProj` with canonical points on the two sheets.

## Acceptance statements

- `zeroModeProjector_fixed_iff_plusSheet`
- `cozeroModeProjector_fixed_iff_minusSheet`
- `creation_kernel_iff_zeroModeProjector_fixed`
- `annihilation_kernel_iff_cozeroModeProjector_fixed`

## Not established

No Hamiltonian spectrum, nonzero protected boundary eigenstate, index-to-kernel
theorem, spatial localization, or topological protection is established. The
KKT-core names are projector-sector labels in this result.
