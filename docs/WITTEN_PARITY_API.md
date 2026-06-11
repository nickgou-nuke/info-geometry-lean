# WittenParityIndex API Overview

> Status: `live API overview`
> Audited: 2026-06-10
> Owner module: `lean/InfoGeometry/Arithmetic/WittenParityIndex.lean`
> Boundary: finite polynomial parity only. This is not a proof certificate for
> RH, analytic Ramanujan convergence, KMS theory, CFT, or a physical Witten
> index theorem.

`WittenParityIndex.lean` is the arithmetic entry point for the finite
`+1, -1, +1, -1` parity sequence attached to the first four symbolic
Ramanujan-defect shapes.

The module has two jobs:

- prove four explicit polynomial parity identities by `ring`;
- connect those identities to the already verified finite Bernoulli defect
  readouts owned by `RamanujanDefectTower`.

## Imports

```lean
import Mathlib
import InfoGeometry.Arithmetic.RamanujanDefectTower
```

## Namespace

```lean
namespace InfoGeometry.Arithmetic.WittenParityIndex
```

## Symbolic Polynomial Layer

The module defines four symbolic defect shapes:

```lean
def D1 (x y : ℝ) : ℝ
def D2 (x y : ℝ) : ℝ
def D3 (x y : ℝ) : ℝ
def D4 (x y : ℝ) : ℝ
```

They use symbolic coefficients `c0`, `c1`, and `c2` to capture the finite
symmetric coefficient patterns:

- `D1`: degree `2`, even under swap;
- `D2`: degree `3`, odd under swap;
- `D3`: degree `4`, even under swap;
- `D4`: degree `5`, odd under swap.

## Kernel-Checked Parity Theorems

The closed theorem surface is:

```lean
theorem D1_even_parity :
    D1 c0 c1 α β = D1 c0 c1 β α

theorem D2_odd_parity :
    D2 c0 c1 β α = - D2 c0 c1 α β

theorem D3_even_parity :
    D3 c0 c1 c2 α β = D3 c0 c1 c2 β α

theorem D4_odd_parity :
    D4 c0 c1 c2 β α = - D4 c0 c1 c2 α β
```

All four are finite algebraic identities proved by `ring`.

## Four-Layer Parity Factor

```lean
def witten_parity_factor (n : ℕ) : ℝ :=
  if n % 2 = 1 then 1 else -1
```

The displayed finite sequence is closed by:

```lean
theorem witten_parity_index_evaluation :
  witten_parity_factor 1 = 1 ∧
  witten_parity_factor 2 = -1 ∧
  witten_parity_factor 3 = 1 ∧
  witten_parity_factor 4 = -1
```

## Bernoulli Defect Connection

The bridge to the finite Ramanujan defect tower is:

```lean
theorem ramanujan_defect_layers_follow_witten_sequence :
    DefectParityTarget 1 (ramanujanBernoulliSide aperyBernoulliReadout 1) ∧
    DefectParityTarget 2 (ramanujanBernoulliSide zetaFiveBernoulliReadout 2) ∧
    DefectParityTarget 3 (ramanujanBernoulliSide zetaSevenBernoulliReadout 3) ∧
    DefectParityTarget 4 (ramanujanBernoulliSide zetaNineBernoulliReadout 4)
```

This theorem imports the already proved finite parity targets:

- `zeta3_defect_parity`;
- `zeta5_defect_parity`;
- `zeta7_defect_parity`;
- `zeta9_defect_parity`.

## Geometric Reading

The safe geometric reading is a dictionary, not a theorem:

| Formal layer | Geometric label | Lean owner |
|---|---|---|
| `D1`, `D3` even parity | invariant finite defect shape | `WittenParityIndex.lean` |
| `D2`, `D4` odd parity | anti-invariant finite defect shape | `WittenParityIndex.lean` |
| `P_plus` | exact label | `HodgeTrifactorBridge.lean` |
| `P_minus` | coexact label | `HodgeTrifactorBridge.lean` |
| `P_zero` | harmonic label | `HodgeTrifactorBridge.lean` |

The Lean theorem currently proves only the finite algebraic parity and the
finite Bernoulli-defect connection. It does not prove that zeta zeros are
harmonic zero-modes or that a physical Witten index has been constructed.

## Companion SymPy Script

`tools/sympy/witten_parity_index.py` independently expands and simplifies the
same four polynomial parity checks:

```bash
python3 tools/sympy/witten_parity_index.py
```

## Verification

```bash
lake env lean lean/InfoGeometry/Arithmetic/WittenParityIndex.lean
lake build InfoGeometry.Arithmetic.WittenParityIndex
python3 tools/sympy/witten_parity_index.py
rg -n "sorry|admit|axiom|sorryProof|_True|_valid|_certificate|_law|law_holds|recovery_law" \
  lean/InfoGeometry/Arithmetic/WittenParityIndex.lean
```

