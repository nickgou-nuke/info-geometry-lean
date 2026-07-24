# QUARANTINED: GogberashviliSplitOctonionBasis.lean

## Date: 2026-07-19

## Reason for quarantine

This file was moved from `lean/InfoGeometry/Clifford/` because its theorems are
**mathematically inconsistent** with the `ZornCell ℝ` algebra defined in
`InfoGeometry.Algebra.Zorn.ConcreteComposition`.

## Sage verification evidence

Using the EXACT `mulZ` formula from `ConcreteComposition.lean`:

- `J0 = (1, -1, 1, 0, 0, 0, 0, 0)`, `I = (1, -1, 0, 0, 0, 0, 0, 0)`, `j0 = (0, 0, 1, 0, 0, -1, 0, 0)`
- File claims: `J0 * I = j0`
- Sage computes: `J0 * I = (1, 1, -1, 0, 0, 0, 0, 0)` (trace = 2, NOT in imaginary subspace)
- But `j0` has trace = 0 (IS in imaginary subspace)
- Therefore `J0 * I ≠ j0` is **guaranteed** by the algebra structure

The `ZornCell ℝ` algebra does NOT preserve the imaginary subspace under multiplication
(Imaginary × Imaginary can produce scalar components). The Gogberashvili relations
`Jₙ * I = jₙ` (both imaginary) cannot hold in this algebra.

## Root cause (basis-conversion analysis)

The split-octonions admit two valid 8D real bases with a linear isomorphism between them:

1. **Abstract Clifford/Cayley-Dickson basis**: `{1, I, J, K, L, LI, LJ, LK}`
2. **Zorn vector-matrix basis**: `{P₊, P₋, X₁, X₂, X₃, Y₁, Y₂, Y₃}`

The correct conversion isomorphism maps the identity to the Zorn identity and the
7 imaginary units to **trace-zero** Zorn matrices:

```
1   ↦ P₊ + P₋ = diag(1, 1)              (trace 2, identity)
K   ↦ P₊ - P₋ = diag(1, -1)            (trace 0)
I   ↦ X₁ - Y₁ = [[0, e₁], [-e₁, 0]]    (trace 0)
J   ↦ X₁ + Y₁ = [[0, e₁], [e₁, 0]]     (trace 0)
```

Under this isomorphism the multiplication tables match perfectly:
- `I² = (X₁ - Y₁)² = -P₊ - P₋ = -1`
- `J² = (X₁ + Y₁)² = P₊ + P₋ = 1`
- `K² = (P₊ - P₋)² = P₊ + P₋ = 1`

**The Gogberashvili file committed a coordinate error**: it mapped the imaginary basis
generator `J₀` directly to the identity matrix `1` (trace 2), rather than to the
trace-free diagonal unit `P₊ - P₋`. This identifies a non-trivial imaginary generator
with the algebraic identity, collapsing the basis:

- By definition, `1 · I = I` (identity acts trivially)
- The paper required `J₀ · I = j₀` with `I` and `j₀` distinct
- If `J₀ ↦ 1`, then `1 · I = j₀` implies `I = j₀`, which collapses the basis

## Resolution options

1. **Use a different algebra**: The Gogberashvili split-octonion basis requires a true
   split-octonion algebra where all 7 imaginary units have square ±1. The current
   `ZornCell ℝ` has nilpotent basis elements (`u1² = 0`), so it is NOT a split octonion.

2. **Find correct coordinates**: If a valid Gogberashvili basis exists in `ZornCell ℝ`,
   the squares work but cross-products don't with current coordinates. Requires
   systematic search for consistent coordinates (may not exist).

3. **Quarantine** (current action): Keep the work but remove from theorem-safe build
   until mathematically verified.

## Status

QUARANTINED - not part of `lake build InfoGeometry`.
