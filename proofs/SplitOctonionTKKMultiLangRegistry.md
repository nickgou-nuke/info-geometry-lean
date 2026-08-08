# Split Octonion / Chiral / TKK Multi-language Registry

This registry ties the Lean carrier theorems to the existing non-Lean witness
files already present in the repo.

It is a boundary document, not a theorem statement:

- Lean carries the certified routing lemmas and finite carrier proxies.
- GAP / Sage / SymPy / M2 / Isabelle carry the polynomial and coordinate
  witnesses.
- The current repo does not claim a full `E8(8)` or `Z_3 × Z_3` theorem in Lean.
- The closest Lean spine is the carrier routing into `g_0`, `g_±1`, and `g_2`.

## Lean core

- `ZornCore.lean`
- `ZornOPParavector.lean`
- `ZornAssociatorSplitOctonion.lean`
- `ZornChiralBridge.lean`
- `ChiralCausalCone.lean`
- `ChiralConeAlgebraFinality.lean`
- `ChiralCausalConeTKKBridge.lean`
- `ZornTrialityTKKBridge.lean`
- `ZornParavectorNullspace.lean`
- `ZornScalingFlow.lean`
- `ZornScalingFlowOrdered.lean`
- `SplitOctonionBraidSU3.lean`
- `FureyZornFermionBridge.lean`
- `PauliZornTrifactor.lean`
- `OctonionMatrixEncodings.lean`
- `TKKJordanPairData.lean`
- `TKKCompileData.lean`
- `TKKQQBridge.lean`
- `TKKCartanDecomposition.lean`
- `ThermodynamicTKKBridge.lean`
- `MobiusCantorTKKClosure.lean`
- `CanonicalSplitOctonionTKK.lean`
- `GrandUnifiedTKK.lean`
- `Pin55CartanDecomposition.lean`
- `Pin55ChiralZornTKKBridge.lean`
- `PinO55GlideReflection.lean`
- `ArtinMonodromyPin55.lean`
- `ArtinCentralizerMonodromy.lean`
- `Clifford55AnomalyOSP.lean`
- `ProjectiveAffineConformalClosure55.lean`
- `SplitCliffordAlgebras.lean`

## External algebra witnesses already in the repo

- `ZornAssociatorSplitOctonion.py`
- `zorn_isospin_breaking.g`
- `cartan_triality_gap.gap`
- `cartan_triality_computation.py`
- `split_octonion_zorn_kks.sympy.py`
- `split_octonion_zorn_kks.sage`
- `split_octonion_zorn_kks.sage.py`
- `split_octonion_zorn_kks.g`
- `split_octonion_zorn_kks.m2`
- `split_octonion_zorn_kks_isabelle/SplitOctonionZornKKS.thy`
- `serre_spectral_split_octonion_sympy.py`
- `serre_spectral_split_octonion.sage`
- `serre_spectral_split_octonion.sage.py`
- `serre_spectral_split_octonion.g`
- `serre_spectral_split_octonion.m2`
- `pin55_matrices.sage`
- `pin55_cartan.sage`
- `pin55_root_system_analysis.sage`
- `pin55_dewitt_dmodule.m2`
- `clifford_tkk_closure.py`
- `galgebra_16_spinor_split.py`
- `galgebra_pin55_orientifold.py`
- `tkk_5_graded.sage`
- `tkk_module.m2`
- `zorn_su3_stabilizer.gap`

## Coverage map

- Zorn lanes and associator witness:
  - Lean: `ZornOPParavector`, `ZornAssociatorSplitOctonion`
  - SymPy: `ZornAssociatorSplitOctonion.py`, `split_octonion_zorn_kks_sympy.py`
  - GAP: `zorn_isospin_breaking.g`, `cartan_triality_gap.gap`
  - Isabelle: `split_octonion_zorn_kks_isabelle/SplitOctonionZornKKS.thy`
  - Sage: `split_octonion_zorn_kks.sage`, `split_octonion_zorn_kks.sage.py`
  - Singular/Macaulay2-style witnesses: `split_octonion_zorn_kks.g`, `split_octonion_zorn_kks.m2`

- Chiral projector and nilpotent spine:
  - Lean: `ChiralCausalCone`, `ChiralConeAlgebraFinality`, `ChiralCausalConeTKKBridge`
  - This is the canonical carrier-side naming layer for `S+`, `S-`, `N+`, `N-`.

- Triality and five-grade closure:
  - Lean: `CartanTriality`, `TKKJordanPairData`, `TKKCompileData`,
    `TKKQQBridge`, `TKKCartanDecomposition`, `GrandUnifiedTKK`,
    `ThermodynamicTKKBridge`, `MobiusCantorTKKClosure`,
    `CanonicalSplitOctonionTKK`, `ZornTrialityTKKBridge`
  - Python witnesses: `cartan_triality_computation.py`, `gravity_tkk_tensor.py`

- Pin(5,5) / O(5,5) carrier-side geometry:
  - Lean: `Clifford55AnomalyOSP`, `SplitCliffordAlgebras`, `Pin55CartanDecomposition`,
    `ProjectiveAffineConformalClosure55`, `Pin55ChiralZornTKKBridge`
  - Sage / M2 / Python witnesses: `pin55_matrices.sage`, `pin55_cartan.sage`,
    `pin55_root_system_analysis.sage`, `pin55_dewitt_dmodule.m2`,
    `clifford_tkk_closure.py`

The registry is intentionally descriptive. The theorem content stays in Lean;
the external files are witnesses, computations, and consistency checks.
