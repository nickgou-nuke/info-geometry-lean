# Stream VI: partition, alternant, and graded-algebra contract

## Intake and source authority

The input is `Pasted text(3).txt`, SHA-256
`aae9d533783dc1c803c10355f188399fbad6caacede6e3a1d844d64987e78884`.
The source is retained with the task attachment. This contract records the
mathematical corrections rather than treating the input's proposed implication
arrows as established theorems.

The implementation starts from upstream commit
`3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`. The earlier chiral-resolvent PR is
independent. Toolchain and dependency pins are unchanged.

## Existing owners and actual carriers

| Input component | Source owner | Actual mathematical content |
|---|---|---|
| Binary exchange cut | `Algebra/LinearInvolutionProjectors.lean` | Complementary native endomorphism idempotents from an involution and a scalar half; both ordered orthogonality laws. |
| Four block components | `Canonical/CattoGurseyBlockGrading.lean` | Native `Matrix (Fin m ⊕ Fin n)`; actual Peirce corner compression and homogeneous block ranges. |
| Odd supertrace | `Canonical/GLSupermatrixGradedLie.lean` | Graded cyclicity and vanishing supertrace of homogeneous brackets over a commutative coefficient ring. |
| Berezin operation | `Canonical/BerezinFermionicIntegrationBridge.lean`, `Canonical/ExteriorContractionOperatorBridge.lean` | Native exterior-algebra contraction, signed generator product rule, square-zero contraction. |
| Quantum binomial | `Algebra/Quantum/QBinomial.lean` | Ordered binomial expansion in an associative algebra over a field, with a central scalar phase. |
| Tripotent projectors | `Physics/Algebra/TripotentPeirceProjectors.lean` | Three ordered orthogonal idempotents for `T*T*T=T` in an arbitrary real algebra. |
| Finite partition sums | `Algebra/OperatorCyclotomicParafermions.lean` | Ordered telescoping and two-sided inverse identities in any ring. |
| Four-sector Fourier inversion | `Canonical/PeirceV4GrandCanonicalFourierBridge.lean` | Actual finite-state sector sums with an explicitly supplied grading into the Klein group. |
| Vandermonde exclusion | `Canonical/VandermondeExclusionBridge.lean`, native `Mathlib.LinearAlgebra.Vandermonde` | Determinant product; zero iff collision requires an integral domain. |
| Schur factorization | `NCG/BerezinianGaussianFactorization.lean`, native `Mathlib.LinearAlgebra.Matrix.SchurComplement` | Ordered block factorization with an actual inverse; ordinary determinant and conditional Schur-ratio readouts. |
| Signed Zorn triples | `Canonical/CattoGurseySplitBasis.lean` | Nonassociative multiplication, two distinct triple-product endpoints, and an obstruction to faithful associative realization. |
| Distinct exterior modes | `Projective/ExteriorBladeIncidence.lean` | Nonzero native exterior product of every linearly independent finite frame. |

These owners were inspected at their definitions, hypotheses, relevant proofs,
and consumers. Existing theorems are reused; an imported theorem is not reported
as a newly constructed result.

## New theorem contracts

### 1. Cubic cancellation for ordered braided families

Carrier: `[Field k] [Ring A] [Algebra k A]`. The scalar phase satisfies
`1 + q + q^2 = 0`; centrality is supplied by `algebraMap k A`.

The binary result assumes `a*b = algebraMap k A q * (b*a)` and proves
`(a+b)^3 = a^3+b^3` by specializing the existing quantum-binomial expansion.
For `a : Fin n → A`, ordered pairwise relations for **only** `i < j` imply
`(∑ i, a i)^3 = ∑ i, (a i)^3`. Individual cube-zero hypotheses then imply
cube-zero of the sum. This applies to native `Module.End` as well as matrices.

The inverse connection uses the existing finite geometric-sum identities to
identify the native `Ring.inverse (1-x)` when a power of `x` vanishes. Thus a
finite cube-zero braided sum has the explicit inverse `1+D+D^2`.

### 2. Polynomial determinant divisibility

Carrier: arbitrary commutative coefficient ring, `v : Fin n → R`, and polynomial
columns `p : Fin n → R[X]`. Reduce each column modulo the monic node polynomial
`∏ i, (X-C(v i))`. The remainder preserves each node evaluation and has degree
less than `n`.

The new matrix theorem constructs, rather than assumes, the factorization
`evaluationMatrix = Matrix.vandermonde v * remainderCoefficientMatrix v p`.
Taking determinants proves divisibility without distinct-node assumptions.
Specializing to independent `MvPolynomial.X` variables and monomial columns
constructs one multivariate polynomial quotient for every determinant alternant
with natural exponents.
Its evaluation formula remains valid when nodes collide.

This supplies polynomial regularity for determinant alternants. Identifying a
quotient with a representation character requires the representation-theoretic
owner and is not inferred from the determinant identity.

### 3. Moment curve and the ordered Zorn baryon

Carrier: the existing `ZornVec3 R` and `ZornVectorMatrix R`, with `[CommRing R]`.
The existing cross product is identified with native `crossProduct`; the dot
product already has native finite-sum coordinates. The scalar triple product
is identified with a native determinant.

For `u(t)=(1,t,t^2)`, the row matrix is exactly `Matrix.vandermonde t`. Its
determinant is `(t 1-t 0)*(t 2-t 0)*(t 2-t 1)`. Reusing
`GunaydinGursey.baryon_parenthesizations` preserves both actual endpoints:

* the left-associated triple is `-Δ • uStarZero`;
* the right-associated triple is `-Δ • uZero`.

Under an integral-domain hypothesis, each triple is zero exactly on the
collision locus. Equality of the two parenthesizations has the same exact
criterion. The reassociation defect is therefore retained, rather than erased
by replacing the nonassociative carrier with matrices.

### 4. Ordered Schur factorization and trace boundary

The rectangular block identity is formulated over any associative coefficient
ring, with explicit two-sided inverse laws for the bottom-right block. The
ordinary determinant specialization additionally assumes commutative
coefficients. Off-diagonal blocks retain their order throughout.

The ordinary trace of an odd anticommutator is twice the trace of its first
block; it can be nonzero. The existing supertrace cancels the two block traces.
A concrete rational example records why the ordinary Schur determinant ratio
is not a multiplicative Berezinian on unrestricted ordinary matrices.

## Corrections and excluded implications

| Input assertion | Correct boundary |
|---|---|
| `1+q+q^2=0` and braiding imply generator cubes vanish | Individual cube-zero laws are separate hypotheses; no such implication is used. |
| Cube-zero sum automatically has nonzero square | False, including for the zero sum. Exact nilpotency requires a separate witness. |
| Every tripotent is a cube-root-of-unity grading | `T^3=T` has spectral labels `0,±1`; `G^3=1` is a different polynomial equation. |
| Binary exclusion forbids three distinct fermionic modes | False. A linearly independent three-frame has nonzero native exterior product. |
| Berezin differentiation is an ordinary quotient derivation | The native operation is odd contraction with a signed product rule. |
| Every truncated geometric sum is one cyclotomic polynomial | True for prime truncation orders; generally it factors into several cyclotomic factors. |
| `1-x` is `Φ₁(x)` | The standard convention is `Φ₁(x)=x-1`, so the sign is reversed. |
| Reciprocal cancellation holds at `x=1` | In a field it requires `x≠1`; in an arbitrary ring it requires `IsUnit (1-x)`. The division-free finite identity holds everywhere. |
| Odd anticommutators always have nonzero ordinary trace | Nonvanishing is possible, not universal. |
| The ordinary determinant/exponential trace identity fails | The ordinary identity remains valid; replacing ordinary trace with supertrace changes the expression being evaluated. |
| Invertible `D` makes the Schur complement invertible | Full block-matrix invertibility is an additional necessary hypothesis. |
| Schur factorization forces a unique multiplicative Berezinian | This does not follow for ordinary commuting coefficients; a concrete counterexample is included. |
| The `6|21` block matrix is the octonion multiplication | Existing `no_injective_associative_realization` excludes a faithful multiplication-preserving identification. |
| A root-of-unity partition zero proves color confinement | This is an algebraic zero; the physical claim needs additional dynamics and representation data. |
| All eight stages form a forced linear causal order | Only actual declaration dependencies are ordered. Independent branches remain incomparable. |

## Dependency order

The mathematical connections to be checked are:

1. Quantum-binomial expansion → cubic cancellation → finite braided nilpotence
   → native finite inverse.
2. Monic division → evaluation-matrix factorization → polynomial determinant
   divisibility → multivariate alternant quotient and its evaluation.
3. Native cross-product compatibility → determinant → moment-curve Vandermonde
   → ordered Zorn triples → exact collision and reassociation criteria.
4. Two-sided inverse laws → ordered block factorization → ordinary determinant
   specialization. Graded trace and its ordinary-trace contrast use the existing
   native block carrier.

The companion `Canonical/StreamVIDeclarationAudit.lean` reads constants from
checked declaration types and values, follows their project dependencies,
checks their transitive axiom dependencies, and computes a topological order.
It uses expression constants rather than the additional inductive/constructor
bookkeeping edges. No actual type/value edge is filtered out.

Ordinary Lean elaboration then creates literal names and edge lists, kernel
proofs of strict forward edges and endpoint bounds, and a native
`PartialOrder (Fin N)`. Its order relation is exactly `Relation.ReflTransGen`
of the extracted edges. The numeric ranks prove antisymmetry; they do not
replace reachability with a total order. The constructor and generated graph
certificates receive the same axiom audit.

The kernel certifies the literal graph's partial order. The inspection command
connects that graph to the loaded declarations, and source hashes connect those
declarations to the selected source snapshot. These are separate checks.
An emitted linear extension does not turn unrelated adjacent nodes into
implications. Physical causality and psychological interpretation are outside
this declaration dependency construction.

## Validation record

The selected closure was independently rebuilt in a fresh directory, without
incremental project-artifact reuse: **53 source modules passed** with Lean
`4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`) against mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The checker verified the pinned
dependency sources; mathlib's pinned compiled artifacts were reused.

The independent declaration audit reports **81 seeds, 294 reachable project
declarations, 192 theorem declarations, and 916 dependency edges**. These counts
include existing owners and private/generated declarations; they are not a
count of new public theorems. All eight graph-certificate declarations passed,
and each has an empty axiom list. The audited declaration closure's transitive
axiom union is
exactly `propext`, `Classical.choice`, and `Quot.sound`.

All 53 source, snapshot, and Git-index hashes matched the successful build
manifest, as did the verification-tool hashes. The independent run recorded
fingerprints for all 53 newly built project `.olean` files. The full compiler log
contains no proof-hole warnings and no warnings from task-owned modules.
Its 13 lint warnings are in unchanged graded-matrix, Fourier-sector, and
tripotent owners.

The scoped staged-proof, strict OpenGauss, semantic-content, semantic-vacuity,
strict closure-debt, and whitespace gates passed. There are no OpenGauss traps,
semantic errors, or hard closure-debt findings. Two short-proof advisories were
reviewed as direct native-lemma reuse and definitional compatibility on the
same carrier. Other nonblocking debt heuristics were classified by independent
QA; they do not supply mathematical assumptions.

A single controlled negative probe replaced one generated certificate proof
with an ill-typed natural-number term in a separate scratch copy. Lean exited
with code 1 and emitted no final audit PASS summary. The checked forbidden-axiom
guard rejected the failed-proof fallback. The agreed end-to-end rejection
criteria were met. An additional harness assertion requiring a particular
immediate logged-error message failed; the raw harness FAIL is preserved, and
that immediate diagnostic path is not claimed to have been exercised. No
source or test changes were made to force that assertion to pass, and the
positive source, index, snapshot, and project-object hashes stayed unchanged.

Independent agent mathematical and architecture review: **PASS**.
Independent QA disposition: **ACCEPTED_WITH_LIMITED_SCOPE**.

Reproduce the selected check with a clean checkout of the pinned mathlib
revision and its compiled dependency artifacts:

```sh
python3 tools/quality/check_operator_geometry.py \
  --mathlib /path/to/pinned-mathlib \
  --work-dir /path/to/fresh-verification-directory \
  --target InfoGeometry.Canonical.StreamVIDeclarationAudit
```

This command rebuilds the complete selected project-source closure. It is
separate from a whole-repository Lake build.

The separately maintained root-package attempt
`python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.StreamVIDeclarationAudit`
acquired the shared lock and exited with code 1 before checking the target:
`external_refs/homotopy-hypothesis-lean4` is missing. Its cache-hydration attempt
encountered the same blocker. The maintained read-only path preflight also
reports absent, untracked HomotopyHypothesis and Atlas path dependencies and an
uninitialized GIFT gitlink pinned at
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92`. The tracked `InfoGeometryCore`
package is available. Thus whole-repository Lake acceptance remains blocked;
no full-root build success is claimed and no dependency pins were changed.
