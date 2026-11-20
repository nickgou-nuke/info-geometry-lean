# Chiral reciprocity: source and theorem contract

## Intake and intent

Source: `Pasted text(20261116-170755).txt`, 254 lines, SHA-256
`049da78bfe67a287774ce409a3a41f793992a72c987b8502667a43f1960afc69`.
The supplied text mixes operator identities, physical interpretation, and
first-person analytical narrative. The narrative is retained in the intake;
it is not evidence for a theorem or a psychological claim about the user.

Base: upstream `main`, commit
`08c34e03f610b452e03422037949196dc7d92d6d`. This is a separate continuation
from the reconstruction/Landauer draft PR. The pinned Lean `v4.34.1` and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain unchanged.

Risk class: R4, bounded Hilbert operators, normed-algebra exponentials, and
finite matrix traces. Intended classification: theorem-backed for the exact
operator statements below, with the analytic-index and physical claims
recorded separately as open or incorrect. No new assumption carrier, index
definition, generalized-inverse definition, or finite-dimensional surrogate
for the Hilbert-space statements is introduced.

## Claim inventory and owner grounding

| Intake claim | Current owner or corrected contract | Classification |
|---|---|---|
| A nonzero nilpotent has an ordinary reciprocal | Existing `Canonical.MoorePenroseDrazinObstruction` and `MoorePenroseDrazinCriterion` distinguish inner, Moore-Penrose, Drazin, and genuine inverses. | Rejected as stated; existing obstruction reused in the report. |
| Nonzero partner eigenvalues pair | `OperatorAlgebra.PartnerEigenspaces` already constructs the equivalence; `PartnerGeneralizedEigenspaces` extends it to generalized eigenspaces and Jordan chains. | Existing theorem. |
| Positive-energy reciprocity is normalized by the inverse square root | `Analysis.HilbertGramDuality` supplies the continuous equivalence and inner-product scaling. Construct the actual native linear isometric equivalence for arbitrary positive real eigenvalue. | New theorem/construction. |
| The normalized correspondence extends to a bounded inverse globally | `Singular.MoorePenrose` already constructs a bounded inverse on the kernel complement under closed range. Connect that actual inverse to Gram eigenspaces and derive its quantitative norm obstruction. | Conditional, with a new proved compatibility and obstruction. |
| A zero Witten index forces absent zero modes or broken supersymmetry | `Canonical.FiniteSuperchargePairing.paired_zeroSupercharge_index` already allows arbitrarily many paired zero modes. | Rejected implication. |
| The exponential partner supertrace equals a dimension defect | `SpinorialCore.FiniteSupertrace` supplies a polynomial result; `Analysis.PairedHeatTrace` supplies conditional spectral sums. Prove an actual normed-algebra exponential theorem using the existing general cyclic-trace owner. | New analytic theorem, with explicit trace hypotheses. |
| A nonzero commutator forces a nonzero exponential weighted trace | Square-zero partners commute with their anticommutator, forcing cyclic cancellation against its exponential. Supply an actual noncommuting matrix example. | Countermodel to the proposed implication. |
| A nonzero weighted trace proves a horizon flux | An unrelated weight already gives a nonzero commutator trace in finite matrices. A boundary-flux identification requires a separate analytic model. | Rejected inference. |
| A spinorial square of minus identity contradicts a projective involution | Native `Projectivization.SL_mulAction_ker` and projective scalar-kernel APIs distinguish the two actions. A support-corner square is not a full ambient identity. | Existing native structure; no topology is inferred from the matrix square. |
| APS makes a Fredholm index noninteger, or supplies a universal negative-eta jump | An integer Fredholm index, an eta invariant, and a regularized non-Fredholm quantity are different objects. The APS formula includes the bulk term, kernel correction, and spectral boundary condition. | Rejected as stated; analytic construction remains open. |
| The Hilbert space canonically splits into zero, positive, and infinity sectors | No operator, spectral measure, or definition of the proposed infinity summand is supplied. Infinity is not an additional eigenvalue. | Open/undefined; no such decomposition is introduced. |

The owner search covered repository filenames and content, direct imports,
consumers, and pinned Mathlib declarations. It is bounded source inspection,
not a claim that all historical files compile or that an external graph is
current. Existing names containing Witten, APS, or modular terminology were
checked for their actual assumptions and carriers.

## Selected native owners and contracts

### HilbertGramReciprocity

Carrier: complete real or complex Hilbert spaces `E,F` and an arbitrary bounded
linear map `A : E ->L[k] F`. Eigenspaces are native `Module.End.eigenspace`
submodules of the actual Gram operators `A.adjoint.comp A` and
`A.comp A.adjoint`.

- An actual `HasEigenvalue` witness proves the Gram eigenvalue real and
  nonnegative. A nonzero actual eigenvalue has positive real part.
- For a real `r > 0`, construct `LinearIsometryEquiv` between the two Gram
  eigenspaces at `(r : k)`, with forward map `r^(-1/2) A` and inverse
  `r^(-1/2) A.adjoint`.
- Reuse `HilbertGramDuality.gramEigenspaceEquiv` and its inner-product law;
  do not rebuild the partner equivalence or assume norm preservation.
- Prove the forward, inverse, and adjoint-exchange readouts.

No finite-dimensionality, compactness, spectral completeness, or closed-range
hypothesis is needed on one positive eigenspace. A nonzero scalar by itself
does not establish the existence of an eigenvector or positivity.

### HilbertGramMoorePenrose

Reuse `Singular.MoorePenrose.IsMoorePenroseInverseCLM A B` and the actual
`moorePenroseInverse A hClosedRange` construction. All products are typed
compositions of bounded maps between the original Hilbert spaces.

- From `ABA=A` and self-adjointness of `BA`, derive `BAA.adjoint=A.adjoint`.
- If `AA.adjoint y = mu*y` with `mu != 0`, derive
  `B y = mu^(-1) * A.adjoint y`.
- At real `r > 0`, prove compatibility with the normalized inverse and the
  norm formula `norm(B y) = norm(y)/sqrt(r)`.
- An actual nonzero eigenvector yields `1 <= r * norm(B)^2`.
- If every positive epsilon bounds an actual positive eigenvalue of
  `AA.adjoint` from above, prove `range A` is not closed. Under a contrary
  closed-range hypothesis, the existing bounded Moore-Penrose construction
  and epsilon `1/(norm(B)^2+1)` contradict the norm bound.

This is a point-spectrum accumulation theorem. It constructs neither a
spectral resolution nor an unbounded pseudoinverse. The obstruction concerns
small positive eigenvalues, not an asserted extra spectral point at infinity.

### GradedExponentialTrace

Carrier: a complete normed associative algebra over a real/complex scalar
field, a continuous linear cyclic functional, and arbitrary algebra elements.
The exponential is native `NormedSpace.exp`, with its convergent series.

- Under `Gamma*D + D*Gamma = 0`, prove
  `tau (Gamma * exp (t * D^2)) = tau Gamma` for every scalar parameter.
  Reuse the existing `NoncommutativeGradedTrace` cancellation theorem;
  continuity justifies applying the functional to the exponential series.
- For arbitrary finite rectangular real/complex matrices `A,B`, specialize
  to the genuine doubled block operator and prove
  `trace(exp(t*AB)) - trace(exp(t*BA)) = card(m) - card(n)`.
  The constant term supplies the dimension correction. Empty index types
  remain allowed. No diagonalization or commutation of `A,B` is assumed.
- For a square-zero factor `E` and arbitrary partner `F`, derive commutation
  with `H=EF+FE`, then prove `trace((EF-FE)*exp(t*H))=0` by existing cyclic
  cancellation. This commutation lemma does not require completeness; the
  preceding analytic series theorem retains that hypothesis.
- Give an explicit noncommuting finite matrix witness, including the
  contrast with a different weight whose commutator trace is nonzero.

For arbitrary partners these are exponential identities. A heat-semigroup
interpretation needs an appropriate adjoint/positive Hamiltonian. The Banach
statement assumes a continuous cyclic functional on that algebra; it is not
an assertion that the ordinary Hilbert trace exists on all bounded operators.
No trace-class ideal, unbounded domain, elliptic heat kernel, APS boundary
problem, KMS state, or Fredholm index formula is supplied by these identities.

The historical polynomial owner's upstream `Algebra.lean` imports the whole
Mathlib umbrella. The new analytic proof instead consumes the more general
existing cyclic-trace owner and native matrix block APIs. Historical owners
and their public declarations remain unchanged; no duplicate polynomial API
is introduced and no dependency pin or verification gate is modified.

## Causal dependencies and acceptance

The native Gram equivalence and inner-product identity feed normalization.
Penrose identities feed the inverse's eigenspace action; normalization and
the operator norm then feed the small-eigenvalue obstruction. In a separate
branch, cyclicity and oddness feed power cancellation; continuity and the
convergent exponential series feed the exponential theorem. The actual block
construction supplies the finite rectangular specialization. These proofs
do not create edges from projective inversion or incidence-poset inversion
to an analytic boundary index.

Generation: root and the isolated Hilbert candidate author. Independent
mathematical/source audit: `paper_audit`. Independent final acceptance:
`repo_survey`, which neither writes the owners nor acts as the source auditor.
Builds and tests remain serialized through the repository's shared lock.

Acceptance requires a fresh maintained source-closure compile, native
declaration axiom audit, strict placeholder and semantic gates, strict
screener/refutation, static Gate 4, and the installed staged-source hook.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted foundational
axioms. No `sorry`, `admit`, custom axiom, `native_decide`, or suppression is
introduced. Actual source hashes, commands, warnings, and acceptance results
belong in the companion formalization report.

Root dependency availability is checked separately. The existing Atlas,
HomotopyHypothesis, and GIFT blockers do not become a successful root-build
certificate through selected-module verification or draft publication.
