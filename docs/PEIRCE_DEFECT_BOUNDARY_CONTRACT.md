# Peirce defect, finite-group action, and positivity contract

## Intake and source authority

This follow-up formalizes the mathematical content of the supplied
`Pasted text(20261112-095847).txt`. The preserved intake under
`docs/intake/peirce-defect-20261112.txt` is an unverified proposal. Its
assertions, including assertions advertised as corrections, are not proof
authority. The implementation starts from main commit
`a392af178af1fe2bcba2ba39eb405700c6ee103c`; PR #325 is a separate change.

The carrier for the algebraic statements is an arbitrary associative unital
ring. Real linear and Hilbert-space structure is introduced explicitly only
for projection and positivity results. No commutativity of the operator ring
or finite dimension of the operator space is assumed.

## Existing owners

- `Core/PeirceDefect.lean` already proves the denominator-free odd-corner
  criterion using native Peirce grading and actual submodules.
- `PeirceSpine/Basic.lean` and `Tetraktys.lean` own the directed cones,
  their ordered products, and their multiplication table.
- `PeirceSpine/CyclotomicBridge.lean` already proves the corrected
  `omega^2 - omegaBar = 1 - V`, reflection squares, braiding, and the
  coefficient `-2` in the reflection-plane difference.
- `PeirceSpine/DefectTower.lean` already proves orthogonal splitting of
  every finite defect iterate.
- `PeirceSpine/Unipotent.lean` already owns conjugation by the nilpotent
  shears, with their ordered signs.
- `PeirceSpine/Homogenized.lean`, `KleinAction.lean`, and
  `TetraktysKleinActionBridge.lean` own the unnormalized channels and
  their identification with an actual Klein action on `V = 1`.
- `OperatorAlgebra/BoundedHomotopyCoercivity.lean` owns the real Hilbert
  Hodge operator, its energy identity, kernel, and a sufficient homotopy
  condition for coercivity.

## New theorem targets and dependencies

1. Two-sided annihilation implies a native `Polynomial.eval₂` splitting
   law, including the exact constant-term correction. Specialize this to
   the two ordered Peirce cycles.
2. The third cyclotomic relation is equivalent to `V = 1`. Equal reflection
   squares are equivalent only to `V^2 = V`. From `V = 1`, construct an
   actual `DihedralGroup 3 →* Bˣ`, with explicit generator values. No
   faithfulness claim is part of this construction.
3. Two commuting involutive real linear maps give a normalized projection
   onto their common fixed submodule. Apply this to the existing Peirce
   conjugations and identify its range with the native common centralizer.
   Prove the exact discrepancy between the off-shell homogenized channel
   and its Fourier channel before imposing `V = 1`.
4. Adjoint pairing gives a positive Hodge operator and a precise common
   kernel. Construct rank-one Peirce operators on an arbitrary real Hilbert
   space with an unused orthogonal direction to prove that nonvanishing
   does not imply a whole-space coercive lower bound.
5. Explicit noncommutative matrix witnesses correct the claimed zero
   products and distinguish zero overlap from a nonzero overlap that
   annihilates a response.

These are theorem dependencies, not a claim that the proposal's conceptual
labels define a categorical poset or a physical dynamical system.

## Corrections required by the intake

| Proposed claim | Exact correction |
|---|---|
| `E12 E31 + E31 E12 = 0` | The sum is `E32`, which is nonzero. A separate four-dimensional example has two nonzero opposite corners with both products zero. |
| `(1-N) P (1+N) = P-N` for an upper corner | This order gives `P+N`; the opposite conjugation order gives `P-N`. |
| The displayed averaging expression gives `8 V^3` and kills the other channels | Its coefficient normalization is wrong. It gives `5 V^3` on `V`; the existing Fourier channel has the correct scale. |
| `V^2 = V` is unital cyclotomic closure | It only equalizes reflection squares. The third cyclotomic relation requires `V = 1`. |
| An algebraic `V` makes defect iterates vanish | Algebraicity alone does not do this; `V = 2*1` is a nonzero fixed point of `x ↦ x^2-x`. |
| Nonzero positive `V` supplies a positive lower bound | A nonzero positive operator may have a nontrivial kernel. An injectivity or coercivity theorem requires additional hypotheses. |
| `[P,A] ≠ 0` implies the upper corner is nonzero for arbitrary `A` | The commutator can be supported entirely in the lower corner. Use the actual upper-corner nonvanishing premise, or an appropriate self-adjointness assumption. |
| A global idempotent supplies a global gauge section | An idempotent can describe a projective module without supplying a global frame or gauge fixing. No bundle-triviality result follows here. |

## Scope limits

There is no Yang--Mills mass-gap theorem, Gribov--Singer theorem, global
bundle construction, Azumaya classification, faithful color action, or
Golay/Leech lattice construction in this change. A restriction on permuting
three named generators does not exclude every action of `S4` on a larger
ambient algebra. The Hilbert-space counterexample excludes a positive lower
bound on the whole space; it does not by itself exclude a spectral gap on
the orthogonal complement of a kernel.

## Validation plan

Keep Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` unchanged. Use a focused
package with the repository's shared-lock build protocol, independent
source review, source screening, and explicit transitive axiom reports.
The local shared compiler lock was occupied at intake; an independent
GitHub runner supplies validation without interrupting that task. A focused
success will certify only the selected import closure and audited names.

Validation results and the exact source commit are recorded in the PR.
