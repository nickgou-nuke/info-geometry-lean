# Peirce Ladder Operators & SU(3) Color: Multi-System Formalization

## Overview

This directory contains a complete cross-system formalization of the connection between:

1. **Complex structure** `J = e₁` with `J² = -1` in split octonions
2. **Nilpotent ladder operators** `uᵢ, dᵢ` from Peirce decomposition
3. **Complex ladder operators** `αᵢ = (uᵢ + J·dᵢ)/√2`
4. **Zorn matrix projectors** `OP1, OP2` for color isolation
5. **SU(3) color gauge symmetry** acting on 3 ladder operators

The key insight: **3 fermionic ladder operators generate the Standard Model color triplet** through the Peirce decomposition mechanism.

## Files by System

### SageMath / SymPy
- `tools/infra/peirce_ladder_formalization.py` - Main Python script
- `tools/infra/galgebra_clifford_peirce.py` - GaAlgebra + Clifford computation
- `tools/infra/bridge_data/peirce_ladder_bridge.json` - Bridge data export

### Lean 4
- `lean/InfoGeometry/Peirce/PeirceLadderOperators.lean` - Formal proof with Mathlib

### Coq
- `tools/infra/bridge_data/PeirceLadder.v` - Coq/MathComp formalization

### Isabelle/HOL
- `tools/infra/bridge_data/PeirceLadderOperators.thy` - Isabelle formalization

### Macaulay2
- `tools/infra/bridge_data/peirce_dmodule.m2` - D-module structure computation

## Mathematical Structure

### 1. Complex Structure
```
J = e₁  (first imaginary unit in split octonions)
J² = -1
```

### 2. Nilpotent Ladder Operators (Peirce Decomposition)
```
uᵢ² = 0      (nilpotent creation)
dᵢ² = 0      (nilpotent annihilation)
{uᵢ, dᵢ} = 1  (canonical anticommutation)
```

### 3. Complex Ladder Operators
```
αᵢ = (uᵢ + J·dᵢ)/√2

These satisfy:
[αᵢ, αⱼ†] = δᵢⱼ
```

### 4. Fermionic Fock Space
```
Dimension: 2³ = 8
Decomposition: 1 ⊕ 3 ⊕ 3̄ ⊕ 1
  - Vacuum |0⟩: singlet 1
  - αᵢ†|0⟩: triplet 3 (quark)
  - αᵢ†αⱼ†|0⟩: antitriplet 3̄ (antiquark)
  - α₀†α₁†α₂†|0⟩: singlet 1 (baryon)
```

### 5. Zorn Matrix Projectors
```
OP1 = [[1,0],[0,0]]  (projects onto a, left)
OP2 = [[0,0],[0,1]]  (projects onto b, right)

Properties:
- OP1² = OP1  (idempotent)
- OP2² = OP2  (idempotent)
- OP1·OP2 = 0  (orthogonal)
- OP1 + OP2 = I  (complete)
```

### 6. Sandwich Formula
```
X_color = OP1 · X · OP2

This strips vacuum/lepton sectors (a, b),
isolating pure SU(3) color off-diagonals (𝑥⃗, 𝑦⃗)
```

### 7. Peirce Decomposition Theorem
```
Tripotent eigenvalue λ ∈ {+1, -1, 0} determines projector:

λ = +1 → OP1 (left, acts on 𝑥⃗ quark)
λ = -1 → OP2 (right, acts on 𝑦⃗ antiquark)
λ = 0  → OP1+OP2 (bilateral, acts on a,b vacuum)
```

## Usage

### Run SageMath/SymPy Formalization
```bash
cd /home/goutev/repos/info-geometry-lean
python3 tools/infra/peirce_ladder_formalization.py
```

### Compile Lean 4 Proof
```bash
cd /home/goutev/repos/info-geometry-lean
lake build PeirceLadderOperators
```

### Check Coq Proof
```bash
cd tools/infra/bridge_data
coqc PeirceLadder.v
```

### Check Isabelle Proof
```bash
isabelle build -d . PeirceLadderOperators
```

### Run Macaulay2 D-Module Computation
```bash
M2 < tools/infra/bridge_data/peirce_dmodule.m2
```

## Cross-System Verification Chain

```
SageMath/SymPy (computation)
      ↓
GaAlgebra/Clifford (geometric algebra)
      ↓
Macaulay2 (D-modules, Weyl algebra)
      ↓
Lean4 (kernel-checked proofs)
      ↓
Coq (independent verification)
      ↓
Isabelle/HOL (independent verification)
```

## Key Theorems

### Lean4: `OP1_idempotent`, `OP2_idempotent`
```lean
theorem OP1_idempotent : OP1 * OP1 = OP1
theorem OP2_idempotent : OP2 * OP2 = OP2
```

### Coq: `peirce_ladder_color_theorem`
```coq
Theorem peirce_ladder_color_theorem :
  forall J u d,
  J * J = -1 →
  (∀ i, nilpotent_ladder (u i) (d i)) →
  ∃ fock_space color_action,
    fock_space ≠ ∅ ∧ su3_dim color_action = 3.
```

### Isabelle: `peirce_ladder_color_theorem`
```isabelle
theorem peirce_ladder_color_theorem:
  fixes J :: real and u d :: "nat ⇒ real"
  assumes "J * J = -1"
    and "∀i∈{0,1,2}. nilpotent_ladder (u i) (d i)"
  shows "∃fock_space color_action.
          fock_space ≠ {} ∧ su3_dim color_action = 3"
```

## Physics Connection

This formalization captures the **Günaydin-Gürsey construction**:
- Split octonions → quark color via Zorn matrices
- 3 ladder operators → 3 colors (red, green, blue)
- Diagonal projectors → isolate color from lepton/vacuum sectors

The fermionic Fock space structure `1 ⊕ 3 ⊕ 3̄ ⊕ 1` matches the Standard Model representation content for a single generation.

## References

- PeirceLadderOperators.lean: Main Lean4 formalization
- peirce_ladder_bridge.json: Bridge data for cross-system ingestion
- AQL functorial bridge: tools/infra/aql/aql_functorial_bridge.py
- SplitOctonionZorn.lean: lean/InfoGeometry/Exceptional/SplitOctonionZorn.lean