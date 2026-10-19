# QMS contract: Seiberg–Witten trace-free theorem scope

## Ground truth

In `Topological/SeibergWittenNoncommutativeGaugeBridge.lean`, `swQuadMap`
returns a value of `Mat2 R`; the owner defines ordinary transpose and matrix
trace, then proves only
`Mat2.trace (swQuadMap Psi half) = 0` under `2 * half = 1`.

The synthesis theorem consumes that trace equality. The inspected owner and its
audit do not define a differential two-form carrier, a Hodge-star operation on
that carrier, or a map identifying the quadratic matrix with a self-dual form.

## Correction

Describe the result as trace-freeness of the quadratic matrix map. Preserve the
theorem name and type. Do not call it self-duality.

## Open mathematical requirement

A self-duality theorem requires an explicit spinor-to-two-form map and a Hodge
star on its target, followed by a proof that the image is fixed by that Hodge
star. No such claim is made by this wording correction.
