# Fibonacci Quantum Group Formalization Map

This document digests the useful ideas from
`/media/goutev/SP DS72/auto/proofs` into the current repo without importing
broken proof files.

The main lesson from the archive is not that more Lean files should be copied.
It is that the repo needs a precise bridge from finite Fibonacci matrix facts to
the still-open quantum-group root-of-unity quotient story.

## Existing Checked Owners

| Concept | Checked owner |
|---|---|
| Golden ratio and Fibonacci fusion dimension | `lean/InfoGeometry/Fibonacci/FibAnyonThm1.lean` |
| Explicit real F-matrix, involutivity, determinant | `lean/InfoGeometry/Fibonacci/FibAnyonThm2.lean` |
| Explicit complex R-matrix and fifth-root convention | `lean/InfoGeometry/Fibonacci/FibAnyonThm3.lean` |
| Closed matrix Yang-Baxter relation | `lean/InfoGeometry/Canonical/YangBaxterProof.lean` |
| Theorem-only categorical F/R/B surface | `lean/InfoGeometry/Categorical/FibonacciBraiding.lean` |
| Mathlib braided coherence plus Zorn/colimit/tri-facet/self-dual cone readout | `lean/InfoGeometry/Categorical/FibonacciBraidedTowerCone.lean` |
| General Grothendieck group infrastructure | `lean/InfoGeometry/Algebra/Grothendieck.lean` |
| Tensor tower colimit/protected-state infrastructure | `lean/InfoGeometry/Canonical/TensorTowerColimit.lean` |

## Archive Ideas Preserved

The fuller archive encodes this informal chain:

```text
U_q(sl(2))
  -> universal R-matrix/quasitriangularity
  -> quantum Yang-Baxter
  -> braided representation category
  -> q root-of-unity truncation
  -> semisimple Fibonacci quotient
  -> explicit F/R matrices
  -> hexagon/Yang-Baxter coherence
```

The current repo has checked material for the final finite/categorical readout,
but not yet for the root-of-unity quotient construction. Future work should
therefore attach new proofs to the owner infrastructure above, not introduce new
wrapper structures or standalone proof sketches.

## Rejected Direct Imports

| Archive file | Reason |
|---|---|
| `FormalTheoryQuantum.lean` | Good roadmap, but not valid Lean in this repo: pseudo tensor notation, unresolved `HopfAlgebra` API, `sorry`, and recursive theorem-name collisions. |
| `FibAnyonThm4.lean` | Does not compile; the repo already has a stronger canonical Yang-Baxter owner. |
| `fib_category.lean` | Does not compile; F-matrix proofs fail under the current toolchain. |
| `fibanyon_thm2_fmatrix.lean` | Does not compile; weaker duplicate of `FibAnyonThm2`. |
| `fibanyon_thm3_rmatrix.lean` | Does not compile; missing namespace for `pi` and has unfinished unitary goals. |
| `fibanyon_thm4_yangbaxter.lean` | Compiles, but only proves `True`; useful only as a pointer to mathlib braided coherence. |
| `fibanyon_thm5_braidgroup.lean` | Compiles, but contains only a toy alias and a `True` theorem. |

## Root Convention Debt

There are two useful root conventions in play:

```text
q2 = exp(2 * pi * i / 5), so q2^5 = 1
q1 = exp(pi * i / 5),     so q1^5 = -1 and q1^2 = q2
```

The finite R-matrix file uses the fifth-root convention. The canonical
Yang-Baxter owner uses the half-angle convention. Before proving deeper
representation-theoretic facts, add explicit bridge lemmas between these
conventions and make every theorem state which convention it uses.

## Native Formalization Queue

1. Root bridge:
   prove checked lemmas relating `exp(pi * i / 5)` and `exp(2 * pi * i / 5)`.
2. Grothendieck/Fibonacci fusion:
   express `tau * tau = one + tau` in the existing Grothendieck infrastructure.
3. Quantum dimension:
   define the exact q-number/quantum-dimension expression needed for the root
   of unity truncation.
4. Negligible quotient:
   state the Ch5 theorem as an explicit interface, with no hidden carrier
   structure and no external certificate fields.
5. Fibonacci MTC quotient:
   state the Ch6 theorem that the quotient has precisely the two simple objects
   `one` and `tau`, plus the fusion rule.
6. Braided category instance:
   only instantiate a concrete Fibonacci `BraidedCategory` after associator,
   unitors, pentagon, and hexagon data are actually kernel-checked.
7. Tower and cone connection:
   route inductive-limit geometry through `TensorTowerColimit`,
   `TriFacetGeometry`, and `SelfDualCone`, as already done by
   `FibonacciBraidedTowerCone`.

## Guardrails

Do not add new carrier `structure` declarations merely to package a proof
sketch. Use explicit theorem parameters or existing owner types.

Do not turn the archive's `True` theorems into owner claims. They are navigation
notes only.

Do not reimplement categorical coherence at the matrix level. Use mathlib
`BraidedCategory` coherence and treat finite matrices as instances/readouts.

Do not claim the full Fibonacci modular tensor category until the
root-of-unity truncation and semisimple quotient have checked Lean statements.
