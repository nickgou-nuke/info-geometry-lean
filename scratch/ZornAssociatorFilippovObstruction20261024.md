# Native Zorn associator: Filippov obstruction contract

Status: historical v1 contract; v3 passed independent AA and candidate QA. Live promotion QA passed.
During initial authoring, no builds, tests, or CAS execution were performed.

Imports: `InfoGeometry.Algebra.ZornPeirceMixedAssociator` and
`Mathlib.Basic.Real.Basic`. Uses the existing `ZornVectorMatrix`, `U`, `V`,
`associator`, and explicit native additive/scalar operations; no new carrier,
closure predicate, or assumed conclusion.

Convention: A(x,y,z) = (xy)z - x(yz). The five inputs are
(x,y,u,v,w) = (U₀,U₁,U₂,V₀,V₁). The fundamental identity's left side is zero;
the right side is -4 U₂. Thus left minus right is 4 U₂ over any CommRing.
Nonvanishing and universal-identity refutation specialize to ℝ; no claim of
nonvanishing in characteristic two. The three right-side contributions are
-2 U₂, -U₂, -U₂ under the owner's multiplication convention.

The two coordinate proofs reduce the native multiplication definitions using
Fin 3 sums. They do not evaluate an external model or introduce an axiom.
The defect equality reuses those separate side evaluations; its real
nonvanishing follows by projecting the upper coordinate 2.

Suggested audit heads (namespace `InfoGeometry.Algebra.ZornVectorMatrix`):
- `associator_filippov_UUUVV_lhs`
- `associator_filippov_UUUVV_rhs`
- `associatorFilippovDefect_UUUVV`
- `associatorFilippovDefect_real_ne_zero`
- `associator_not_filippov_real`

This refutes Filippov for the associator, not the ordinary Leibniz theorem for
the corrected standard derivation D(a,b) = ad([a,b]) - 3 A(a,b,·), nor the
fundamental identity for a Lie algebra's nested triple product.

Final native owner QA: `/tmp/qa-a-zorn-filippov-live-h_642ris/result.json`,
session 87342, exit zero, shared lock released. Owner plus Algebra.All built
9709 jobs; all six declarations clean; zero scoped warnings/errors, stable
captured source and pin hashes. Existing upstream/package warnings remain.
Independent source AA accepted the byte-identical v3 promotion. This is scoped
acceptance, not a full repository release receipt.
