# Gamma Matrices Status - Cl(1,1) Split Signature

## Overview

The `GammaMatrices.lean` file provides **theorem-honest computational representations** of the canonical split Clifford algebra Cl(1,1). It is NOT a competing definition but a verified isomorphism to the coordinate algebra.

## Canonical Sources (THESE ARE THE AUTHORITY)

1. **`Cl11CoordinateAlgebra.lean`** - Finite coordinate algebra with:
   - Generators: `e1Basis` (squares to +1), `e2Basis` (squares to -1)
   - Anticommutation: `e2 * e1 = -e12`
   - Bivector: `e1 * e2 = e12`, `e12² = 1`

2. **`Cl11InfiniteCarrier.lean`** - Direct limit Cl(1,1)^∞

3. **`ClNN.lean`** - Recursive Cl(n,n) tower with null generators

4. **`Canonical/SplitCliffordDirectLimit.lean`** - Mathlib wrapper

## GammaMatrices.lean Role

Provides explicit 2×2 matrix representations for:
- Numerical verification (export to SymPy/SageMath)
- Connection to physics literature (which uses gamma matrix notation)
- Computational debugging

### Key Theorems

```lean
-- The isomorphism
coordinateMatrixEquiv : Cl11 ≃+* Matrix (Fin 2) (Fin 2) ℝ

-- Basis correspondence
correspondence_e1 : coordinateMatrixEquiv e1Basis = γ₁  (squares to +I)
correspondence_e2 : coordinateMatrixEquiv e2Basis = γ₂  (squares to -I)
correspondence_e12 : coordinateMatrixEquiv e12Basis = γ₁₂

-- Structure preservation
correspondence_sq_e1 : coordinateMatrixEquiv (e1 * e1) = I
correspondence_sq_e2 : coordinateMatrixEquiv (e2 * e2) = -I
correspondence_anticomm : coordinateMatrixEquiv (e2 * e1) = -γ₁₂
```

## Signature: Cl(1,1) NOT Cl(3,0)

**CRITICAL**: These are SPLIT signature matrices:
- γ₁² = +I (one positive direction)
- γ₂² = -I (one negative direction)  
- {γ₁, γ₂} = 0 (anticommute)

This is **NOT** the Euclidean Pauli matrices (which generate Cl(3,0) with all three squaring to +I, or Cl(0,3) with all squaring to -I).

The split signature Cl(1,1) is appropriate for:
- Krein spaces (indefinite metric)
- 1+1 dimensional Minkowski space
- Hyperbolic geometry

## Matrix Representation

```
γ₁ = [0  1]     (squares to +I)
     [1  0]

γ₂ = [0 -1]     (squares to -I)  
     [1  0]

γ₁₂ = [1  0]    (bivector, squares to +I)
      [0 -1]
```

The isomorphism:
```
fromCoordinate(q) = [q.s + q.e12,  q.e1 - q.e2]
                    [q.e1 + q.e2,  q.s - q.e12]
```

## Usage

```lean
-- For algebraic work, use the canonical algebra:
open InfoGeometry.Clifford.Cl11CoordinateAlgebra
#eval e1Basis * e2Basis  -- = e12Basis

-- For matrix computations:
open InfoGeometry.Clifford.GammaMatrices
#eval gammaPlus * gammaMinus  -- = gamma12

-- To translate between them:
#eval coordinateMatrixEquiv (e1Basis * e2Basis)  -- = gamma12
```

## Computational Tools

The SymPy/SageMath verification scripts in `tools/clifford/` use the Weyl-Brauer construction for Cl(n,n). They verify:
- Anticommutation relations {Γₐ, Γ_b} = 2ηₐₑI
- Correct signature (split, not Euclidean)
- Recursive Kronecker product structure

## TODO

1. Extend `splitGammaEmbedding` to full Cl(n,n) tower
2. Prove embedding preserves multiplication for all n
3. Connect to `ClNN` tower via `Canonical.SplitCliffordDirectLimit`
4. Add numerical export functions (JSON/Python codegen)