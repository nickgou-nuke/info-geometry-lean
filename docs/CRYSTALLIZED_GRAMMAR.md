# Convex-hull maximizers

## Mathematical extraction

The supplied text contains a valid conditional claim: a **unique attained
maximum** of a linear objective on a convex hull belongs to the generating set.
The implementation proves the stronger convex-objective version and then its
linear specialization, using native `ConvexOn`, `LinearMap`, `convexHull`, and
`Set.extremePoints`. It introduces neither an identity-valued “polytope” wrapper
nor a replacement linear-functional structure.

The uniqueness hypothesis is not strict convexity. Strict convexity need not
give a unique maximum; an affine objective is not strictly convex on a domain
containing a nontrivial segment. Neither a unique maximum nor its existence is
assumed to follow automatically from a physical cooling process.

## Existing owners and sources

Recursive content searches, including hidden/ignored and archived Lean files,
returned 198 matching lines in `/tmp/crystallization-reuse.txt`. Inspected
repository owners include `Epistemology/SemanticReflector`,
`Canonical/ZeroTemperatureCrystallization`, and the existing interference
formalization. Their declarations concern adjunctions, matrix conjugation, or
complex amplitudes, not this convex-hull maximum theorem.

[Mathlib's extreme-point API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Extreme.html)
already provides `extremePoints_convexHull_subset`; it is reused rather than
reproved. Installed Mathlib sources determine the proof signatures.
`ConvexOn.convex_le` and `convexHull_min` propagate a bound from the generators
to their hull. `Finset.exists_max_image` supplies a maximizing generator for a
nonempty finite generating set.

A follow-up search in `/tmp/convex-saturation-reuse.txt` and direct inspection of
Mathlib's `Analysis/Convex/Function.lean` identified native endpoint-saturation
inequalities: `ConvexOn.le_left_of_right_le` and `le_right_of_left_le`.
The implementation now reuses these instead of repeating polynomial arithmetic.
It also reuses `LinearMap.convexOn` rather than reproving linear convexity.

## Theorem dependencies

- Convexity plus a unique attained maximum implies an extreme point: a strict
  two-point mixture reaching the maximum forces its endpoints to maximize.
- Extreme-point membership in a convex hull implies generator membership.
- The native linear-map specialization closes the supplied incomplete proof.
- Convex sublevel sets propagate generator bounds to the convex hull.
- Finite nonempty generators attain their largest objective value; the bound
  theorem makes it a maximum over their hull.

The finite-maximum branch needs neither uniqueness nor the extreme-point
argument. The unique-maximizer branch needs neither finiteness nor topology.
`CrystallizedGrammarDependency.lean` records these separate branches as a finite
partial order. It is not introspection of Lean's environment or a semantic
equivalence between probability distributions and propositions.

Endpoint saturation also gives `maximizer_set_isExtreme`, without assuming
uniqueness or existence of a maximizer. An extreme **set** need not be convex
and can be empty. For linear objectives, `linear_maximum_on_openSegment_iff`
proves the two-sided statement: a strict mixture attains the bound exactly when
both endpoints attain it. The converse is not asserted for arbitrary convex
objectives. An additional regression example shows why a zero mixture weight
cannot force the ignored endpoint to maximize. These saturation branches are
included in the dependency poset.

## Boundaries and regression tests

An arbitrary generating set is not necessarily finite, discrete, bounded, or
the set of vertices. Its convex hull is not automatically a polytope.
`finite_generator_maximum` guarantees a maximizing generator, not that every
maximizer is a vertex, or that the selected generator is extreme.

The constant zero linear objective has the midpoint of `[0,1]` as a maximizer,
although it is not in the generating set `{0,1}`. The tests formalize this
counterexample and the failure of maximum attainment for the identity function
on `(0,1)`. Positive tests cover the identity objective and finite constant
objectives, including ties.

No Krein–Milman or Bauer theorem is claimed: their topological hypotheses and
conclusions differ from the elementary convex-hull result here. No theorem
establishes a zero-temperature limit, Boolean-valued weights, an E8 lattice,
or a transformation of observations into logical truth. Minimizing a convex
objective is also a different problem from maximizing it.

## Verification environment

Serial checks use the shared build lock, installed Lean 4.28.x, cached Mathlib,
and isolated outputs. Pinned Lean 4.28.1 is unavailable locally; no toolchain or
dependency metadata is changed. This is not a full-repository build.

All three Lean modules compile, and all seven regression examples pass.
Axiom audits of all twelve theorems report only subsets of `propext`,
`Classical.choice`, and `Quot.sound`. No `sorryAx`, custom axioms, or
`native_decide` are used. Targeted staged-diff whitespace checks pass.
