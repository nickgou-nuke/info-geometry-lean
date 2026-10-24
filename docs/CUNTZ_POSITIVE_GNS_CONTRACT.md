# Positive algebraic GNS state on the corrected Cuntz quotient

Carrier: `ComplexStarCuntzAlg Bool`, with conjugate-linear complex star,
regarded as a real star algebra for the existing GNS quotient API.
For normalized nonnegative weights q, use the real part of the already
constructed `quotientProductFunctional q hq`. Its positivity on all
star-squares is `quotientProductFunctional_nonneg`; its star compatibility is
`quotientProductFunctional_star`. Real symmetry follows by taking real parts
of the latter identity on `star x * y`.

The existing `RealAlgebraicState.state_null_product_zero` implies closure of
the null set under left multiplication: apply it to `star a * (a * x)` and
the null vector x. Thus the `GNSAction.RepresentationState.null_left_ideal`
field is proved, not imposed as a new condition on the quotient state.
The complex star-square value has zero imaginary part by positivity, so its
vanishing is equivalent to vanishing of the real quadratic value.

Reuse `AlgebraicGNSState`, `GNSBridge`, and `GNSAction`; no new quotient or
alternative scalar-fixing involution. This supplies an algebraic real GNS
action on the corrected complex carrier. Complex-linear Hilbert completion,
boundedness, faithfulness, and von Neumann closure are separate obligations.

Status: parent kernel/axiom audit passed; independent semantic review passed;
independent QA passed (session 93111, exit zero, 9420 jobs,
`/tmp/cuntz-positive-gns-qa.log`). Parent session 39711 exited zero with 9420 jobs;
log `/tmp/cuntz-positive-gns-audit.log`. All four axiom reports contain exactly
`propext`, `Classical.choice`, and `Quot.sound`. The new concrete state and
audit modules produce no warnings. The modified generic state owner retains
its pre-existing deprecated `Mathlib.Data.Real.Star` import warning.
Strict screening of the new modules found zero traps.

The complex radical bridge now reuses `Archetype_II_GNS_Radical.gnsRadical` in
`Cosmology/NonCommutativeHorizonCausalPoset.lean`, already a scalar-polymorphic
native submodule, with membership `∀ y, φ (star y * x) = 0` and proved
left-multiplication stability. `CuntzComplexStarGNSRadical` identifies this
complex radical with the real quadratic null set, using null-product vanishing
on y and `I • y`. It uses Mathlib's `LinearMap.liftQ₂` to descend the actual
complex pairing and proves nonnegativity and diagonal-zero iff quotient-zero.
Parent audit session 63979 exited zero with 9422 jobs, eight standard-three
axiom reports, and no new-module warnings (`/tmp/cuntz-complex-radical-audit.log`).
Independent semantic review and QA passed (session 65520, exit zero, 9422 jobs,
`/tmp/cuntz-complex-radical-qa.log`).
The representative-preserving equivalence with the earlier real GNS carrier
and intertwining of its action with a native complex-linear quotient operator
are now in `CuntzComplexStarGNSQuotient`. Parent audit session 27591 exited
zero with 9423 jobs and four standard-three axiom reports
(`/tmp/cuntz-complex-gns-quotient-audit.log`). Semantic review passed;
independent quotient QA passed (session 47429, exit zero, 9423 jobs,
`/tmp/cuntz-complex-gns-quotient-qa.log`). All four QA axiom reports contain
exactly the standard three axioms, with zero own-source warnings and zero
strict-screen traps. The carrier equivalence is an `Equiv`; only the quotient
action is packaged as complex-linear. Hilbert completion remains an obligation. The
similarly named `Cosmology/CausalPosetArchetypes.lean` repeats the radical
declaration names; reconcile imports before composing these surfaces.
