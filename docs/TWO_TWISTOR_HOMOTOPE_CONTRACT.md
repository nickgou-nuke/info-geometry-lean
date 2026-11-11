# Two-twistor invariants and ordered homotopes

## Intake and provenance

Source: the user's Bulgarian two-twistor / associative `T`-homotope intake in
the 2026-11-11 conversation. The original prose remains the source proposal,
not a collection of accepted axioms. This contract records the mathematical
claims selected from it and their corrections.

The intake proposes `x *_T y = x*T*y`, a symmetric/skew decomposition,
`H = Z† Σ Z`, `P = conjugate(Π)*transpose(Π)`,
`m² = 2*|det Π|²`, a degenerate lower-spinor alternating form, internal
unitary frame changes, and the recurrence `(M,S) -> (3M+S,M+3S)`.
It also proposes a thirteen-node conceptual poset, quantum spin spectra,
Pauli–Lubanski identities, a massless representation limit, and a color
interpretation. Those additional interpretations require separate carriers
and proofs; numbering the proposed nodes does not prove those implications.

## Source-grounded owners

Base: `c143c264bc18bbf41d692be4e270b5b7f7405702` on `main`.
Lean: `v4.34.1`; Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

| Existing owner | Reused mathematical content |
|---|---|
| `Twistor/PenroseIncidence.lean` | `Spinor2`, `Twistor4 = Spinor2 × Spinor2`, `ComplexSpacetime` |
| `Twistor/PerjesConventions.lean` | Conjugate-first `wittPair`, `paperHelicity`, `paperScale` |
| `Twistor/InfinityTwistor.lean` | Native alternating form, dual-valued infinity map, radical and Plücker `p23` |
| `Twistor/TwoTwistorPlucker.lean` | Six actual minors of the existing twistor pair |
| `Twistor/TwistorKinematicTensor.lean` | Slot components and conjugate-first momentum dyad |
| `Twistor/TwistorConstituentKinematics.lean` | `pairMassSq`, momentum determinant, nonnegativity |
| `Twistor/TwistorInternalSymmetry.lean` | Left mixing of row-indexed constituent packets |
| `Twistor/ConstituentMomentumTransport.lean` | Whole-matrix unitary momentum invariance |
| `OperatorAlgebra/PeirceSpine/KantorCornerAnomaly.lean` | A restricted upper-Peirce homotope bracket; not the general associative product |

The search covered repository filenames and content under `lean/InfoGeometry`,
the imported owner statements and their consumers, and the pinned Mathlib
matrix/trace/unitary APIs. No categorical or analytic completion is needed
for the finite matrix statements here. Existing colimit owners are not
substitutes for the missing physical implications.

## Corrected theorem contracts

1. **Ordered product.** Work in an arbitrary associative noncommutative
   ring/algebra. Associativity of `x*T*y` is inherited without assuming that
   `T` is central or invertible. The half-sum/half-difference decomposition
   requires an appropriate scalar inverse of two. Its skew part can vanish;
   nonvanishing must be a hypothesis or an explicit example.
2. **Gram and mass.** Use the existing Witt form on the existing twistor
   carrier. The induced alternating two-tensor contraction is the determinant
   of the Gram matrix. The paper-normalized mass squared is twice the existing
   `pairMassSq`; the existing definition is not changed.
3. **Independent variation.** Construct twistor vectors with arbitrary complex
   infinity pairing `r` and cross pairing `t`, both with zero self-pairing.
   Consequently the two squared magnitudes independently realize every pair
   of nonnegative real values. This explicit realization is the delivered
   statement; an `AlgebraicIndependent` theorem for a specified polynomial
   coordinate ring is a distinct possible extension.
4. **Infinity form.** `I_flat = diag(0, epsilon)` is neither an idempotent
   projector nor a square-zero matrix: its square is minus the lower-block
   projector. Raising with the off-diagonal Witt matrix gives a square-zero
   endomorphism. These are different typed constructions.
5. **Unitary action.** The prompt uses right column action, whereas the
   existing packet uses left row mixing. The adapter is `mix Uᵀ`.
   For square matrices `U†U=1` implies `UU†=1`; the latter must be used before
   transposing to obtain `conjugate(U)*transpose(U)=1`. Invariance under
   constituent mixing is not a matrix-centralizer theorem about `P`.
6. **Spin normalization.** With standard Pauli matrices and
   `Htf = H - trace(H)/2 * 1`, choose `S_i = trace(Htf*sigma_i)/4`.
   Then `S = (Re(tau), -Im(tau), s1-s2)/2` and
   `|S|² = ((s1-s2)² + |tau|²)/4 = trace(Htf²)/8`.
   The intake's negative trace-square sign and mixed factors are rejected.
7. **Cayley change.** The actual matrix `paperScale * [[1,1],[-1,1]]`
   is unitary with determinant one. It preserves the pair's bivector, mass,
   momentum and spin length. Internal Pauli coefficients rotate; the pitch vector is not
   fixed componentwise. No spin normalization is inferred from terminology.
8. **Finite recurrence.** Prove the recurrence and its Hadamard modes for
   every natural-number iteration. Identifying the resulting integers with
   dimensions of specific Clifford tensor subspaces requires a separate
   counting equivalence and is not claimed here.

## Explicit open and rejected claims

- Divergence of `|S|/m` as `m -> 0` requires an additional asymptotic
  hypothesis; a nonzero limiting spin is sufficient. Bounded spin alone does
  not imply divergence. No representation-theoretic massless limit or
  Weinberg–Witten theorem follows from the finite quotient formula.
- The Pauli–Lubanski operator, quantum CCR representation, spin spectrum,
  `SU(3)` color interpretation, and an unbounded `Gr(k,4)` tower are not
  constructed. In particular `k` cannot grow beyond four for subspaces of a
  fixed four-dimensional space.
- The real-coordinate massless example in the intake has nonzero second
  self-pairing. A purely imaginary upper component supplies a genuine pair
  of null twistors with zero mass and nonzero cross pairing.
- A conceptual ordering is recorded as a dependency map only where Lean
  imports and theorem applications provide the corresponding dependencies.

## Actual dependency order

The formal dependency order has two branches. The generic associative-ring
homotope and the natural-number recurrence are independent algebraic owners.
The twistor branch reuses the existing carrier, Witt form, infinity pairing,
moment operators and constituent dynamics. Its new dependencies are:

| Level | Owner | Inputs and resulting statement |
|---|---|---|
| 1 | `TwoTwistorGramMass` | Existing pairings and moment operators → Gram contraction, ordered round-trip trace, exact idempotence defect and all positive operator powers, independent parameter realization |
| 1 | `TwoTwistorSpinCayley` | Existing scale and Pauli matrices → corrected coordinate norm and concrete Cayley identities |
| 2 | `TwoTwistorInfinityBlocks` | Gram/mass carrier and existing column equivalence → rank-two dual form, lower-block square, raised nilpotence and infinity contraction |
| 3 | `TwoTwistorUnitary` | Both level-1 owners, infinity blocks and existing momentum transport → covariance, isomassive Cayley change and invariant squared pitch length |

This order is the import/theorem dependency structure. It does not pretend
that a numbered philosophical taxonomy proves the excluded physical claims.

## Verification plan

Compile the exact affected source closure against the unchanged pins, inspect
all introduced declaration axiom dependencies, run the strict proof screener
and staged proof gate, and obtain independent source review. Report the
scoped result separately from the root-package integration gate. The latter
must be attempted and its actual failure, if any, retained.
