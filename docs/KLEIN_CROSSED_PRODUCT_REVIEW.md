# Independent source review: Klein, skew-polynomial and CAR development

## Review roles and scope

The parent integrated candidate sources and owns serialized kernel verification.
Worker authors did not run Lean, Lake, tests, or cache commands. Independent
reviewers read different authors' sources against the pinned Mathlib APIs.
These findings are semantic/source reviews, not compiler acceptance.

| Source | Author | Independent reviewer | Source-level result |
| --- | --- | --- | --- |
| `Algebra/SkewPolynomialFactorization.lean` | lean_environment | thermodynamics_audit | Pass; kernel validation pending in the separate verification record. |
| `Algebra/CARTwoSidedIdeal.lean` | thermodynamics_audit | lean_environment | Pass; ledger wording narrowed to the actual real-algebra sheet adapter. |
| `Algebra/QuadraticCrossedProduct.lean` | spinor_audit | lean_environment | Pass; actual native matrix subring, conditional centrality and quadratic identity. |
| `OperatorAlgebra/Z2ProjectorWeights.lean` | parent | thermodynamics_audit | Pass; existing definitions reused, rational rather than real scope clarified. |

## Native skew-polynomial review

The action used by the native `SkewPolynomial.φ` is exactly the action defining
multiplication. The product law twists the coefficient of the right factor:
`(r*X^n)*(s*X^m)` has coefficient `r * φ^n(s)`, in that order. Accordingly the
candidate's linear coefficient is `φ(v)-u` and its constant term is `-u*v`.
The stated right-inverse condition is sufficient; no opposite-order inverse
or invertibility of the twist is assumed. `abel` is used only after valid
multiplicative rewrites. Extracting the degree-one coefficient proves the
exact defect criterion even for rings with zero divisors and noninjective
twists. No root-set, unique-factorization, or geometric classification is
reported as a consequence.

## Native two-sided quotient review

The proof uses `TwoSidedIdeal`, not a left ideal. Both absorption directions
are required and are applied in the correct order. The unit anticommutator
puts 1 in the ideal, giving the actual top ideal. The native quotient is
`I.ringCon.Quotient`; the top-ideal congruence is definitionally the top ring
congruence. A unital `RingHom` preserves the unit anticommutator, so killing
one generator gives `0=1` in its entire codomain without surjectivity.

The assumptions have nontrivial examples: the existing
`SplitClifford.carPair_matrix` supplies the two off-diagonal matrix units in
`M₂(ℂ)`. The new `Cl11Atom.toCARPair` explicitly fills the existing interface
with the existing real-algebra half-sums and their proved identities. No new
Clifford representation or stored conclusion is introduced.

## Twisted quadratic matrix review

Coordinate injectivity uses entries `(0,0)` and `(1,0)` and injectivity of `σ`.
It does not divide by `T`; even `T=0` is admitted. The ordered product formula
is correct under precisely involutivity and `σ T=T`. Native `Subring` closure
inherits actual matrix operations. The coefficient map is a `RingHom`, not an
unjustified `Algebra L` instance, since arbitrary coefficients are not central.
The lower-left entry detects the fixed-ring condition without cancellation.

Trace and determinant are fixed coefficients and their embeddings are central
in the constructed subring. The centrality theorem classifies only embedded
coefficient elements; it does not assert that the entire center equals the
fixed ring. The quadratic identity is an ordered polynomial formula using
native trace/determinant. It does not define a reduced characteristic polynomial
in a separately constructed central simple algebra or a bundled polynomial
over a fixed subring. The independently reviewed `glide_isUnit` addition maps the unit parameter
through the coefficient homomorphism, rewrites the result as the square of
the glide, and uses native `isUnit_pow_iff`. This works in a general monoid;
no commutativity of the quadratic ring or explicit inverse formula is assumed.

The later closed complex-conjugation example was independently reviewed too.
It instantiates this exact image at `R=ℂ`, `σ=conj`, `T=1`; commutation of the
glide and the embedded `I` would force `conj I=I`, contradicted by imaginary
parts. Reopening the namespace removes the generic ambient variables from
this closed statement. The separate imported matrix-unit witness matches the
generic ambient carrier. Uniform `L→R` renaming only aligns the coefficient
variable with that existing API. Three unused definitional coercion lemmas
were removed; substantive short computational proofs were retained.

The final lexical semantic-vacuity scan flags two short `simp` proofs for
review: `matrix_trace` computes the trace of the actual matrix, and the
unchanged `AlgHom.map_projectorWeight` is a structural homomorphism
calculation. Neither has a vacuous conclusion. An earlier scan also flagged
`traceCoefficient_fixed`; after its necessary native proof repair, that
finding is absent. The remaining warning-level findings require semantic
review, not artificially longer proof scripts.

## Existing projector owner review

Both half-sums have the same defect `¼ • (Γ*Γ-1)`. Over a rational algebra,
cancelling this nonzero scalar proves idempotence iff `Γ*Γ=1`, including the
trivial algebra. `module` is used only for rational linear combinations after
distribution; operator products are not commuted. The narrower import is
supported by `FiniteSpinAlgebra` importing `Mathlib.Tactic`; compilation must
still validate the complete changed owner, including its old declarations.

## Repairs after the first native compiler pass

The first native pass found simplifier elaboration failures in the skew,
quadratic, and projector modules. The authors proposed isolated repairs for
the new modules, and a different
reviewer compared both repairs with the exact failed-check source snapshots.
The parent integrated only the reviewed proof-body changes.

In the skew coefficient proof, an explicit `C_mul_X_eq_monomial` rewrite now
precedes the restricted coefficient simplifier. This prevents an additive
homomorphism rewrite from splitting the constant before the product is
converted to a monomial.

In the quadratic module, concrete instances `hσ a`, `hσ b`, `hσ c`, and
`hσ d` replace the ineffective general involutivity simplifier argument where
needed. A `map_zero` rewrite removes a remaining `σ 0`, and compiler-reported
unused simplifier arguments are removed. The proof of trace invariance finishes
with additive commutativity. Remaining `ring` calls operate only on entries
in the declared commutative coefficient ring after matrix extensionality.

No declaration, theorem statement, carrier, hypothesis, factor order, or
theorem contract was weakened by these repairs. This independent source
review does not replace their required subsequent native compiler check.

The two projector equivalence proofs additionally give `sub_eq_zero` to
`norm_num`, closing the exact residual equivalence `Γ*Γ-1=0 ↔ Γ*Γ=1` reported
by the compiler. Their defect calculations and statements remain unchanged.

## Boundaries retained

The global skew Laurent Klein algebra and its split fibers are distinct
carriers. No global CAR pair is inferred from a split matrix fiber. No topology,
orientation class, Brauer class, Azumaya locus, categorical colimit, or
uniqueness theorem for a philosophical synthesis follows from this patch.
See the claim ledger and source references in
`KLEIN_CROSSED_PRODUCT_CONTRACT.md` for the intake corrections.

## Scoped CI review, 2026-11-17

The first upstream run compiled nine of ten closure modules. The quadratic,
CAR, and projector owners each compiled with zero warnings. The skew
coefficient proof still left an `if True` expression because its restricted
simplifier did not reduce that branch, and `if_pos` was deprecated at the
pinned Lean version. A different reviewer checked the minimal final repair:
retain the explicit `C_mul_X_eq_monomial` rewrite and use
`simpa [coeff_monomial] using hcoeff`. The pinned default simplifier supplies
the reflexive-condition, `ite_true`, and `coeff_zero` reductions. Removing
the restricted simplifier changes no statement, assumption, or ordered
product. Current native acceptance is recorded by the exact-head workflow,
separately from this source review.

An independent reviewer inspected the new
`.github/workflows/klein-crossed-product.yml` against the maintained checker
and shared-lock implementation. The reviewed workflow SHA-256 is
`20992d957874409297718d5c1330d2bcc1beab32ec3f43960153aa2d3d5dc3f2`.

The workflow fetches the exact PR head, checks the unchanged toolchain and
Mathlib pins, verifies the official compiler archive on fresh installation,
and records source provenance. It restores only pinned dependencies, derives
cache roots from the current source closure, and hydrates under the original
shared lock with its descriptor inherited by subprocesses. Nonexistent
lexical import paths are recorded and excluded only from cache arguments;
the native compiler still checks the unchanged source imports.

Every run uses fresh repository output, the unchanged maintained checker,
and its mandatory native declaration audit. A subsequent report guard checks
the exact source head and target list and requires all four owners to compile
with zero warnings. No root gate or hook is changed. The parent also parsed
the YAML and checked all embedded shell and Python syntax successfully.
These source and syntax reviews do not claim that a GitHub Actions run has
completed; current execution results belong in the verification record.
