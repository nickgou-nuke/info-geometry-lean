# Release Notes

## v0.1.0-bridge-chain (2026-06-05)

Bridge chain closed: self-dual cones → Weyl/V4 → Klein bottle orientifold → boundary states.

- `clockAxis_as_intertwiner` closes the Heisenberg↔Schrödinger duality
- Affine cocycle extension `A·W ≠ W·A` with explicit defect `(±2θ₂∓2π, 0)`
- 5 bridge files, 16 SymPy witnesses, 0 structural gaps
- Tag: `v0.1.0-bridge-chain`

### Post-release verification

- `tools/sympy/andreev_affine_defect_bridge.py` — downstream Andreev cocycle propagation check
  - Verifies the same affine cocycle defect as an explicit phase-conjugation correction in the Andreev/BdG channel
  - `OVERALL: True` (all checks passed)
