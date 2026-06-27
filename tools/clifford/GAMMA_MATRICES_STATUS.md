# Higher-Dimensional Gamma Matrices: Repo-Native Clifford Algebra Status

## Mandate

Formalize higher-dimensional gamma matrices and Clifford algebra structures using **only** kernel-checked, repo-native theorems. No speculative physics interpretations, no unproven claims.

## Current Repo Status (Kernel-Checked)

### 1. Split Clifford Tower `Cl(n,n)`

**Owner Files:**
- `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean` (309 lines)
- `lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean` (235 lines)
- `lean/InfoGeometry/Clifford/CliffordBott.lean` (186 lines)

**Core Definitions:**
```lean
-- Split Cl(1,1) head atom
abbrev SplitCl11Alg := CliffordAlgebra Q11

-- Recursive Cl(n,n) tower
abbrev SplitClNNAlg (n : ℕ) := Alg n

-- Direct limit (infinite split Clifford algebra)
abbrev ClInfty := SplitCliffordInfinity
```

**Kernel-Checked Theorems:**
1. **Bott periodicity**: `splitCliffordMap` embeddings form a directed system
2. **Direct limit**: `ClInfty` is the Mathlib `DirectLimit.Ring` of the tower
3. **Parabolic power law**: `(1 + rε)^n = 1 + nrε` in the direct limit
4. **Square-zero generators**: `gammaHeadNullMinus 0` lifts to square-zero element
5. **8-step Bott clock**: Subsequence preserves square-zero property

### 2. DAG Matrix Representations

**Owner Files:**
- `lean/DAG/MatrixRepresentation.lean`
- `lean/DAG/ChiralDiracAnticommutation.lean`
- `lean/DAG/GradedBottPeriodicity.lean`

**Core Definitions:**
```lean
-- Chiral gamma matrix (grading operator)
def chiralGamma {n0 n1 n2 : ℕ} : Matrix (Cell n0 n1 n2) (Cell n0 n1 n2) ℚ

-- Dirac operator
def diracOp (B1 B2 : ...) : Matrix ...

-- Graded anticommutation
theorem dirac_anticommutes_gamma :
  chiralGamma * diracOp + diracOp * chiralGamma = 0
```

### 3. Krein-Clifford Foundations

**Owner Files:**
- `lean/SelfReference/Krein.lean`
- `lean/InfoGeometry/Krein/*` (multiple files)

**Core Structures:**
- Krein space with `⟨J, ε, i⟩` supergraded Lie package
- Split signature `(n,n)` quadratic forms
- Tomita-Takesaki modular theory bridge

### 4. What Exists in Mathlib (via Repo Imports)

The repo imports these Mathlib modules:
- `Mathlib.Algebra.Colimit.DirectLimit`
- `Mathlib.Algebra.Colimit.Module`
- `Mathlib.LinearAlgebra.CliffordAlgebra.Basic` (imported by `DAG/FindFinrank.lean`)
- `Mathlib.LinearAlgebra.CliffordAlgebra.Grading`

**Known Mathlib Clifford API:**
```lean
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

-- Universal Clifford algebra construction
def CliffordAlgebra (Q : QuadraticForm R M) : Type

-- Universal map from vector space to Clifford algebra
def CliffordAlgebra.ι (Q : QuadraticForm R M) : M →ₗ[R] CliffordAlgebra Q

-- Fundamental relation: ι(v)² = Q(v) • 1
theorem CliffordAlgebra.ι_sq (v : M) : (ι v)^2 = algebraMap R (CliffordAlgebra Q) (Q v)

-- Grading by Z/2Z (even/odd decomposition)
def CliffordAlgebra.evenOdd (Q : QuadraticForm R M) : ZMod 2 → Type
```

## Gaps vs Wikipedia Claims

### Wikipedia Claims NOT Yet Formalized

1. **Gamma group presentation** - abstract group with generators `Γ_a`
2. **Charge conjugation matrices** `C_(±)` in arbitrary dimensions
3. **Symmetry tables** for `C Γ_{a₁...aₙ}` transposition
4. **Recursive construction** via Pauli matrix tensor products
5. **Explicit dimension formulas** for charge conjugation properties

### What CAN Be Formalized Now

Using existing repo surfaces:

1. **Split-signature gamma matrices** as `Cl(n,n)` generators
2. **Chiral grading operator** `chiralGamma` (already defined)
3. **Anticommutation relations** via `CliffordAlgebra.ι_sq`
4. **Bott periodicity** through `splitCliffordMap` embeddings
5. **Direct-limit structure** via `ClInfty`

## Multi-Engine Verification Plan

### Phase 1: SymPy/Python (Exploration)

Create verification scripts for:
- Explicit `Cl(n,n)` generator matrices for small `n`
- Anticommutation relations `{Γ_a, Γ_b} = 2η_{ab}`
- Chiral operator `Γ_chir = Γ_0...Γ_{d-1}`
- Charge conjugation candidates `C_(±)`

**File:** `tools/clifford/verify_gamma_matrices.py`

### Phase 2: SageMath (Algebraic Structure)

Verify:
- Quadratic form classification for split signatures
- Dimension counts: `dim Cl(p,q) = 2^{p+q}`
- Even/odd subalgebra dimensions
- Center structure in various signatures

**File:** `tools/clifford/gamma_sage.sage`

### Phase 3: GAP (Finite Group Theory)

Verify:
- Gamma group order: `|G_{p,q}| = 2^{p+q+2}`
- Derived subgroup: `[G,G] = {1, -1}`
- Involution counts
- Center structure

**File:** `tools/clifford/gamma_group.g`

### Phase 4: Lean 4 (Kernel-Checked Core)

Formalize:
1. Anticommutation relations from `CliffordAlgebra.ι_sq`
2. Chiral operator properties (existing: `chiralGamma`)
3. Grading structure via `CliffordAlgebra.evenOdd`
4. Bott periodicity via `splitCliffordMap`

**DO NOT FORMALIZE YET:**
- Full gamma group presentation
- Charge conjugation classification tables
- Transposition symmetry properties
- Odd-dimensional special cases

**Files to Extend:**
- `lean/InfoGeometry/Clifford/GammaMatrices.lean` (new)
- `lean/InfoGeometry/Clifford/CliffordBott.lean` (extend)

### Phase 5: Isabelle/HOL (Structural Sketch)

Create skeleton theory mirroring Lean definitions:
- Algebra typeclass for Clifford algebras
- Generator anticommutation axioms
- Grading structure

**File:** `tools/isabelle/gamma/GammaMatrices.thy`

### Phase 6: Coq (Alternative Formalization)

Parallel formalization using Coq's linear algebra:
- Matrix representations
- Anticommutation proofs
- Comparison with Lean results

**File:** `tools/coq/GammaMatrices.v`

## Immediate Next Steps

1. **Audit existing Lean files** to extract all kernel-checked gamma/Clifford theorems
2. **Create SymPy verification** for small-dimensional cases (`n=1,2,3,4`)
3. **Document negative scope**: what's NOT yet formalized (charge conjugation tables, etc.)
4. **Extend `CliffordBott.lean`** with explicit anticommutation lemmas
5. **Build multi-engine harness** following the `mobius-multi-engine-formalization` pattern

## Honesty Boundary

**Formalized (Kernel-Checked):**
- Split Clifford tower `Cl(n,n)` direct limit
- Chiral grading operator on DAG matrix representations
- Bott periodicity embeddings
- Parabolic power law in direct limit
- Supergraded Lie package `⟨J, ε, i⟩`

**NOT Yet Formalized:**
- Full gamma group presentation
- Charge conjugation classification in all dimensions
- Transposition/conjugation symmetry tables
- Odd-dimension special cases
- Explicit matrix constructions beyond `n=4` DAG grading

**Mathlib Imports That Work:**
- `Mathlib.LinearAlgebra.CliffordAlgebra.Basic` ✓
- `Mathlib.LinearAlgebra.CliffordAlgebra.Grading` ✓
- `Mathlib.Algebra.Colimit.DirectLimit` ✓
- `Mathlib.Algebra.Colimit.Module` ✓

## Verification Commands

```bash
# Check existing Lean files compile
lake env lean lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean
lake env lean lean/InfoGeometry/Clifford/CliffordBott.lean

# Build mathlib dependencies
lake update mathlib
lake build

# SymPy verification (Phase 1 - COMPLETE ✓)
python3 tools/clifford/verify_gamma_matrices.py
# Output: CLIFFORD_SYMPY_OK

# After Sage script is created (Phase 2)
/home/goutev/miniforge3/envs/sage/bin/python3 tools/clifford/gamma_sage.sage

# After GAP script is created (Phase 3)
/home/goutev/miniforge3/envs/sage/bin/gap -q -c 'Read("tools/clifford/gamma_group.g");'
```

## Phase 1 Status: SymPy Verification ✓ COMPLETE

**File:** [`tools/clifford/verify_gamma_matrices.py`](file:///home/goutev/repos/info-geometry-lean/tools/clifford/verify_gamma_matrices.py)

**Verified:**
- ✓ Cl(1,1) anticommutation relations: `{Γ_a, Γ_b} = 2η_{ab} I`
- ✓ Cl(1,1) square relations: `Γ_0² = +I`, `Γ_1² = -I`
- ✓ Cl(1,1) chiral operator: `Γ_chir = Γ_0 Γ_1`, `Γ_chir² = +I`, `{Γ_chir, Γ_a} = 0`
- ✓ Cl(1,1) charge conjugation: `C_+` exists (Γ_0)
- ✓ Dimension formula: `dim Cl(n,n) = 2^{2n}` for n=1,2,3,4

**Deferred to Lean:**
- Cl(2,2) explicit matrices (use repo's ClNN tower instead)
- Charge conjugation classification in higher dimensions
- Transposition symmetry tables

**Output:**
```
CLIFFORD_SYMPY_OK
All verifications passed
```

## References

- **[SplitCliffordTensorBridge.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean)** - Canonical `Cl(n,n)` tower, 309 lines
- **[SplitCliffordDirectLimit.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean)** - Direct limit construction, 235 lines
- **[CliffordBott.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Clifford/CliffordBott.lean)** - Bott periodicity bridge, 186 lines
- **[MatrixRepresentation.lean](file:///home/goutev/repos/info-geometry-lean/lean/DAG/MatrixRepresentation.lean)** - DAG matrix representations with `chiralGamma`
- **[ChiralDiracAnticommutation.lean](file:///home/goutev/repos/info-geometry-lean/lean/DAG/ChiralDiracAnticommutation.lean)** - Anticommutation theorem
- **Mathlib**: `LinearAlgebra/CliffordAlgebra/Basic.lean`, `Grading.lean`