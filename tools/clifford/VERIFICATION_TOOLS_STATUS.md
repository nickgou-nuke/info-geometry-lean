# Accurate Status: Gamma Matrix Computational Tools

## What's Being Committed

### ✅ SymPy Verification (`tools/clifford/verify_gamma_matrices.py`)
Computational verification of Weyl-Brauer construction for **Euclidean Cl(d,0)**:
- 10/10 signatures tested (d=2,3,4)
- Full anticommutation: {Γ_a, Γ_b} = 2η_{ab}I
- Chiral operator properties
- **Signature**: Euclidean (not split)

### ✅ SageMath Verification (`tools/clifford/gamma_sage.py`)
Abstract Clifford algebra verification:
- Native `CliffordAlgebra(QuadraticForm)` usage
- 9/9 algebras verified (d=2,3,4)
- Even/odd decomposition
- Center structure
- **Can handle both Euclidean and split signatures**

### ✅ GAP Script (`tools/clifford/gamma_group.gap`)
Group-theoretic verification (created, not yet run):
- Gamma group structure
- Order: 2^{d+2}
- Derived subgroup, center properties

### ✅ Documentation
- `ACCURATE_STATUS.md` - Canonical vs. reference (this file supersedes others)
- `MULTI_ENGINE_GAMMA_MATRICES.md` - Cross-engine status
- `verify_multi_engine.sh` - Shell script to run all verifications

## What's NOT Being Committed (Deleted/Reverted)

### ❌ `lean/InfoGeometry/Clifford/GammaMatrices.lean`
**Status**: Kept as reference but NOT canonical
- Euclidean signature Cl(d,0)
- Does NOT match repo's Cl(n,n) split tower
- Already has disclaimer: "NOT USED IN MAIN TOWER"
- **Should NOT be imported for proofs**

### ✅ Canonical Implementation (Already in Repo)
- `Cl11CoordinateAlgebra.lean` - Finite Cl(1,1) coordinates
- `ClNN.lean` - Recursive Cl(n,n) tower  
- `Cl11InfiniteCarrier.lean` - Direct limit carrier
- `SplitCliffordDirectLimit.lean` - Mathlib DirectLimit wrapper

## Commit Message

```
tools(clifford): Add computational verification for Clifford algebras

External verification tools for Clifford algebra structures:

- verify_gamma_matrices.py: SymPy Weyl-Brauer verification (Euclidean)
- gamma_sage.py: SageMath abstract Clifford algebra (both signatures)
- gamma_group.gap: GAP gamma group structure
- Documentation: ACCURATE_STATUS.md, MULTI_ENGINE_GAMMA_MATRICES.md

These tools provide computational evidence for Clifford algebra relations.
They verify Euclidean signature Cl(d,0); the repo's canonical implementation
uses split signature Cl(n,n) in Clifford.ClNN and Clifford.Cl11InfiniteCarrier.

The Lean file GammaMatrices.lean (Euclidean) is kept for reference but
marked as NOT USED IN MAIN TOWER.
```

## Usage

```bash
# SymPy verification (Euclidean)
python3 tools/clifford/verify_gamma_matrices.py

# SageMath verification (both signatures possible)
sage -python tools/clifford/gamma_sage.py

# GAP verification (not yet run)
gap tools/clifford/gamma_group.gap
```

For formalization work in this repo, use:
- `InfoGeometry.Clifford.ClNN` - Split tower
- `InfoGeometry.Clifford.Cl11CoordinateAlgebra` - Cl(1,1) coordinates
- `InfoGeometry.Clifford.Cl11InfiniteCarrier` - Direct limit