# Epistemic gap implementation — 2026-11-26

## Intake and source authority

The intake is the user attachment `Pasted text(20261126-162037).txt`, supplied
with the request to implement its audited gaps in the current codebase.
Its persistent source identifier is
`libfile_fde3_f-be3943728a9881919cab6c3ae1cad824_70911a391df48191b124693f71d02e6e`.
The attachment is an audit and implementation agenda, not a theorem certificate.
This document records extracted contracts rather than claiming to reproduce
the attachment verbatim.

Implementation started from `fe24e350b08fdea04f74c0748ef9fd9417c47529` with
Lean `4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
No toolchain or dependency revision change is part of this work.

The following pending owner sources were inspected at exact revisions:

| Existing proposed owner | Source revision | Reused role |
| --- | --- | --- |
| `AttentionQueryGeometry` from [PR #456](https://github.com/nickgou-nuke/info-geometry-lean/pull/456) | `4ad85fc6e5f2ffb8d178efffecd43922e76b6460` | Actual query log-partition, first Fréchet derivative, Fisher null criterion |
| `FiniteRealFockQuadraticAdjoint` from [PR #463](https://github.com/nickgou-nuke/info-geometry-lean/pull/463) | `892baa629fcb56284a92d06c64d0da803b29125c` | Positive-Hilbert transpose-adjoint law for the quadratic Fock operator |
| `GradedCliffordOperatorRepresentation`, `AtiyahBottShapiroSymbol` from [PR #465](https://github.com/nickgou-nuke/info-geometry-lean/pull/465) | `5ee7def6bdeb7a5ddfff95018456427dbe9ddcdf` | Actual graded Clifford representation, eigenspace symbol and inverse |

The individual source files are reused with their ownership relationships;
this is not an assertion that those complete pull requests have been merged.

## Atomic contracts

The table describes the integrated source implementation and its explicit
hypotheses. Acceptance of an exact revision additionally requires native Lean
compilation and all-declaration axiom verification; the verification record below
separates those checks from source review.

| ID | Carrier and hypotheses | Required conclusion | Source implementation |
| --- | --- | --- | --- |
| LOG-1 | Finite-dimensional real Hilbert space; positive operator `T` | The restriction to `ker T` orthogonal complement is positive and invertible | Actual support restriction, positivity and inverse |
| LOG-2 | The same actual support restriction | Real symmetric operator logarithm and native power-series exponential inverse | Native real spectral theorem and power-series exponential |
| LOG-3 | Zero extension of the negative support logarithm | `P exp(-K) P = T`, and exponential acts as identity on the discarded kernel | Compressed identity and explicit kernel correction |
| GEN-1 | Existing `H_unb`, `U_unb`, and `D_max` | Strong continuity of the actual real ℓ² group | Summable square domination on the original Hilbert carrier |
| GEN-2 | Same group and maximal weighted ℓ² domain | Derivative at zero equals `K_max`, with differentiability iff domain membership | Both domain implications and a concrete strong-generator instance |
| SK-1 | Positive rectangular finite kernel and positive equal-mass marginals | Existence and uniqueness of the diagonally scaled matrix | Constructed feasible product coupling and unique scaling |
| SK-2 | Actual alternating row/column normalization recurrence | Whole sequence tends to that matrix | Full matrix-sequence convergence for the actual native Nat.rec recurrence |
| SK-3 | All nonnegative matrices with the given marginals | Generalized and ordinary relative-entropy Pythagorean identities and unique constrained minimizer | Pythagorean proof admits all nonnegative feasible competitors, including zeros |
| SK-4 | Nonnegative kernel with an explicitly feasible coupling positive on exactly its support | Supported iteration convergence and scaling | Closed active-log-potential range handles arbitrary feasible support, including disconnected masks |
| SK-5 | Square nonnegative kernel and unit marginals | Positive-permutation coverage iff same-support doubly stochastic feasibility iff positive balanced scaling | Native Birkhoff decomposition and explicit positive permutation average |
| FOCK-1 | Full native real exterior/Fock algebra | `Q(M)` equals the exterior derivation on every degree | Native exterior generator induction on every degree |
| FOCK-2 | Same complete operator carrier | `[Q(M),Q(N)] = Q(MN-NM)`, transpose adjoint, and noncommutation example | Actual Lie representation, positive-metric adjoint and symmetric noncommuting example |
| FOCK-3 | Existing exterior-basis coordinates with their proved norm identity | Actual isometry to finite Euclidean coordinates, with star-algebra conjugation preserving the action, adjoints and commutators | Existing norm-preserving coordinates bundled as a linear isometry and star-algebra conjugation |
| FISHER-1 | Finite nonempty family of continuous real key covectors | Full Fréchet derivative of the actual first Fréchet derivative is continuous bilinear covariance | Full Fréchet Hessian as a continuous bilinear covariance |
| FISHER-2 | Quotient by the intersection of key-difference kernels; nonzero inverse temperature | Positive definite native inner-product core and induced norm, with base-point descent | Actual quotient carrier, positive inner-product core and induced norm |
| FISHER-3 | Same quotient | Potential descends after subtracting the reference-key affine term, retaining its Hessian | Affine-corrected potential and base-point descent |
| KKS-1 | Native Lie algebra over a commutative ring; actual radical of the KKS bilinear map | Alternating nondegenerate form on the module quotient | Actual radical module quotient and induced alternating form |
| DIRAC-1 | Native Lie algebra, trivial scalar coefficients, native alternating two-cochain | Graph equals its neutral orthogonal complement, and is bracket-closed iff native CE differential vanishes | Native cochain differential, actual graph and native Lie subalgebra |
| DIRAC-2 | Same cochain | Linear B-transform preserves pairing; bracket defect is contraction of native CE differential | Actual linear B-transform; native Lie equivalence when the CE differential vanishes |
| ABS-1 | Actual graded representation of real `Cl(0,1)` | Native Clifford-module equivalence with `V × V`, generator `(-y,x)`, grading `(x,-y)` | Full represented-module equivalence, including the entire Clifford action |
| ABS-2 | Finite-dimensional normed module; negative-unit sphere | Continuous symbol and inverse families | Actual eigenspace carriers and finite-dimensional operator continuity |
| ABS-3 | Extra odd square-minus-one generator anticommuting with the old generators | Hemisphere symbol, square/inverse/boundary identities, and continuity | Native extended Clifford representation, with a concrete noncommuting real four-dimensional example |
| ABS-4 | Two actual represented graded Clifford modules | Product-carrier representation and eigenspace direct sums, compatible with symbol and inverse | Actual product representation and eigenspace equivalences |
| ABS-5 | Actual represented graded `Cl(0,1)` module and the existing restriction functor | The actual restricted object's superdimensions equal the diagonal arithmetic restriction invariant, compatibly with the arithmetic cokernel | Objectwise arithmetic comparison; module-class Grothendieck identification remains separate |
| TOMITA-1 | Densely defined closed real partial operator on its original Hilbert space | Actual adjoint-square composition domain, form identities, positivity, self-adjointness and closedness | Native partial-map adjoint and closed-graph projection derive density, self-adjointness and closedness |
| TOMITA-2 | Closable existing Tomita core on the original GNS completion, viewed as a real Hilbert space | Actual real adjoint square with the original composition domain and form | Original GNS realification and original Tomita graph; explicit closability premise |
| FREDHOLM-1 | Existing real ℓ² space and maximal domain; symmetric operator `D = -Γ K_max` | Explicit smoothing `C` with `C(H) ⊆ D_max` and `D C = F`; bounded self-adjoint odd invertible `F`, native Fredholm index zero, compact `F²-I` | Actual maximal-domain smoothing identity and operator-norm finite-coordinate compactness proof |
| CORE-1 | Legacy `RealContinuousCoreInterface` | Correct documentation of its invariant scalar readout | Truthful scalar-readout contract and proof using the actual fixed-point equality |
| BARRIER-1 | Sinkhorn matrix with all row and column sums one | Existing marginal log barrier is zero | Native elementary negative-sum identity and normalized-marginal theorem |
| GATE-1 | New-ref pre-push validation | The invocation advertised as the full root gate actually selects `--full` | Explicit --full invocation with the existing range checks preserved |

## Actual mathematical dependencies

These are proof dependencies to be checked in Lean, not causal claims about a
physical system or edges inferred from shared terminology.

- Real positivity and the kernel orthogonal complement → positive support
  restriction → real spectral logarithm → exponential intertwining and the
  compressed exponential identity.
- Weighted ℓ² domain → summable domination → strong group continuity and
  derivative → maximal-domain characterization.
- Scalar KL inequality → supported matrix Pythagorean identity → actual
  normalization descent → compact positive support box → balanced cluster
  point → uniqueness → whole-iteration convergence.
- Native exterior derivation recurrence → equality with creation/contraction
  quadratic → matrix commutator identity and existing Hilbert adjoint law.
- Actual query probability derivative → derivative of the first Fréchet derivative →
  mixed covariance → exact nullspace → quotient form and induced norm.
- Native KKS bilinear map → its radical → double quotient lift →
  nondegeneracy. Native CE differential → graph bracket defect → graph
  closure and B-transform compatibility.
- Actual grading eigenspaces and negative Clifford generator → standard
  doubled module equivalence → full action compatibility. Extra generator →
  extended quadratic representation → hemisphere symbol.

## Source navigation and import surface

The selected constructions have one import surface:

```lean
import InfoGeometry.Canonical.EpistemicGapImplementation
```

The leaf owners retain their separate carriers and hypotheses. Importing the
surface does not identify those carriers with one another.

| Construction | Main source owners |
| --- | --- |
| Positive support, logarithm, exponential and kernel correction | [RealSupportLogarithm](../lean/InfoGeometry/Analysis/RealSupportLogarithm.lean) |
| Strong real Hilbert group and exact maximal generator domain | [UnboundedHilbertStrongGenerator](../lean/InfoGeometry/OperatorAlgebra/UnboundedHilbertStrongGenerator.lean) |
| Positive rectangular Sinkhorn limit and KL minimizer | [SinkhornPositiveConvergence](../lean/InfoGeometry/Physics/SinkhornPositiveConvergence.lean), [SinkhornRelativeEntropyProjection](../lean/InfoGeometry/Physics/SinkhornRelativeEntropyProjection.lean) |
| Sparse support convergence and square total-support classification | [SinkhornSupportConvergence](../lean/InfoGeometry/Physics/SinkhornSupportConvergence.lean), [SinkhornTotalSupport](../lean/InfoGeometry/Physics/SinkhornTotalSupport.lean) |
| Logarithmic routing recurrence and concrete counterexamples | [FiniteLogSinkhornConvergence](../lean/InfoGeometry/Routing/FiniteLogSinkhornConvergence.lean), [SinkhornKLExamples](../lean/InfoGeometry/Physics/SinkhornKLExamples.lean) |
| Full Fock derivation and actual isometric coordinate transport | [FiniteRealFockExteriorDerivation](../lean/InfoGeometry/Clifford/FiniteRealFockExteriorDerivation.lean), [FiniteRealFockIsometricTransport](../lean/InfoGeometry/Clifford/FiniteRealFockIsometricTransport.lean) |
| Fréchet Hessian, nullspace quotient and positive Fisher form | [AttentionFisherQuotient](../lean/InfoGeometry/Canonical/AttentionFisherQuotient.lean) |
| Algebraic KKS radical quotient | [SouriauKKSRadicalQuotient](../lean/InfoGeometry/Canonical/SouriauKKSRadicalQuotient.lean) |
| Native Chevalley–Eilenberg graph and B-transform | [CotangentDiracCE](../lean/InfoGeometry/Geometry/CotangentDiracCE.lean) |
| Actual negative-line module classification and direct sums | [NegativeLineModuleClassification](../lean/InfoGeometry/Canonical/NegativeLineModuleClassification.lean), [GradedCliffordModuleSum](../lean/InfoGeometry/Canonical/GradedCliffordModuleSum.lean) |
| Continuous ABS symbol, hemisphere and restriction comparison | [AtiyahBottShapiroHemisphere](../lean/InfoGeometry/Canonical/AtiyahBottShapiroHemisphere.lean), [ABSZeroStepModuleComparison](../lean/InfoGeometry/Canonical/ABSZeroStepModuleComparison.lean) |
| Closed partial-operator adjoint square and original GNS bridge | [RealAdjointSquare](../lean/InfoGeometry/OperatorAlgebra/RealAdjointSquare.lean), [ClosedTomitaAdjointSquare](../lean/InfoGeometry/Canonical/ClosedTomitaAdjointSquare.lean) |
| Actual real ℓ² bounded transform and compact square defect | [RealL2BoundedTransform](../lean/InfoGeometry/OperatorAlgebra/RealL2BoundedTransform.lean) |

The ABS hemisphere owner also constructs a concrete real four-dimensional
instance of its extra-generator hypotheses. On `(ℝ × ℝ) × (ℝ × ℝ)`, it uses
`C(x,y)=(-y,x)` and `J(x,y)=(Ay,Ax)`, where `A(a,b)=(-b,a)`. It proves the
square and grading relations, `C*J + J*C = 0`, and `C*J ≠ J*C`, and identifies
the two represented coordinate generators with these actual operators.

The Fock owner proves both noncommutation of its explicit symmetric real
coefficient matrices and noncommutation of their full lifted operators.
The coordinate transport uses the existing norm-preserving exterior-coordinate
map; it preserves the actual Hilbert adjoint and Lie commutator.

Compatibility checks also cover the existing consumers of the extracted
owners. After extraction, `CliffordExteriorLift` needs only the focused exterior
owner and `FiniteSpinAlgebra`; its remaining declaration is byte-preserved.
The three required Peirce projector/decomposition ancestors of
`TripotentUnboundedResolventFlow` now use focused native Mathlib imports in
place of whole-Mathlib imports. Their complete declaration-bearing suffixes
are byte-preserved. These import repairs address concrete missing native
artifacts and have separate source review. The subsequent native seven-owner
compatibility run passed, including the exact derivative-import repair
described in the verification record.

## Corrections to legacy contracts

`SouriauCoadjointOrbitSymplecticReduction.reducedKKSForm` still accepts
representatives in the original Lie algebra. Its names remain source
compatible, but its documentation no longer says that it constructs a smooth
Marsden–Weinstein quotient.

The `SinkhornFoundation` phase inequalities compare the normalized axis's
zero post-step residual with the other axis's nonnegative pre-step residual.
They do not prove that the other axis improves, that a single global
error sequence is monotone, or that the matrix sequence converges. Compatibility
names mentioning transport or free energy retain their existing types with
corrected descriptions. The new KL convergence owner has a distinct theorem
contract.

`kahlerPotentialRN` is a sum of marginal log barriers. On the bistochastic
locus it vanishes. The Fisher metric belongs to the query Hessian quotient;
the two constructions are not identified by naming them both potentials.

`RealContinuousCoreInterface` packages an action and an invariant real-valued
readout on an abstract type. It supplies no algebra, crossed product, or normal
faithful semifinite trace. The canonical continuous-core trace requires a
scaling law and a positive extended codomain. The legacy fields are not
silently reinterpreted as that trace. The scaling sign depends on the chosen
dual character: [Houdayer's Copenhagen notes](https://cyrilhoudayer.com/wp-content/uploads/2014/09/copenhagen-2013.pdf),
Lecture 5, p. 15, use `θ_t(λ(s)) = exp(its) λ(s)` and `Tr ∘ θ_t = exp(t) Tr`.
Reversing the action parameter reverses both signs. The abstract legacy action
does not specify either character convention.

`CertifiedModularReduction.RegularSpectrumPositive` computes the spectrum of
an ambient compression. It cannot certify strict positivity when that
compression retains a nonzero discarded kernel. The public interface remains
source compatible, with documentation pointing to the actual restricted
support construction. Its Drazin projector is not identified with the metric
support without a separate theorem.

## Boundaries of the implementation

Finite real spectral calculus does not provide an unbounded logarithm or a
Tomita–Takesaki theorem. A native positive modular form, even after quotient
and completion, is not itself an operator `S†S` on the original GNS Hilbert
space. Compact resolvent by itself is not a proved bounded Fredholm transform.

The KKS quotient here is algebraic. Smooth coadjoint orbit charts, invariant
differential forms on an orbit, Lie-group integration, and smooth Courant
algebroids require their own owners. The Fisher inner-product construction does
not by itself establish a global Kähler structure or identify its topology
with an independently chosen ambient quotient topology.

Support-feasible Sinkhorn data are explicit mathematical input in the general
rectangular sparse case. A positive diagonal, or mere existence of a
nonnegative coupling with smaller support, does not replace support-faithful
feasibility. The square unit-marginal owner characterizes this feasibility
by positive-permutation coverage. A general rectangular Hall-type
classification of admissible masks is a separate claim.

The explicit real ℓ² bounded transform proves an operator-level Fredholm result.
It does not supply a represented algebra, compact commutators with that algebra,
a Fredholm-module class or a chiral index pairing.

The standard `Cl(0,1)` module equivalence is stronger than a dimension count,
but full ABS/K-theory comparison also requires additive module classes,
restriction maps, and the topological clutching/classification comparison.
Those must not be inferred solely from an algebraic symbol or dimension
equality.

## Verification record

### Accepted native scopes

The current source implementation has passed native acceptance in three
separate scopes, using Lean `4.34.1` and the unchanged pinned Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

| Native scope | Repository modules | Owned declarations audited | Result |
| --- | ---: | ---: | --- |
| All 33 new owners, `SinkhornFoundation`, and `SpectralTriple` | 149 | 1,610 | Passed |
| Exact `Canonical.EpistemicGapImplementation` import and ownership probe | 146 | 0 owned; all 34 required owners imported | Passed |
| Seven compatibility owners, including `TripotentExponentialFlow` | 72 | 484 | Passed |

The two complete declaration audits cover 42 distinct owners and 2,094
declarations, including all 1,038 declarations owned by the 33 new modules.
The union of native repository modules, including the umbrella, has 209
members. Counts include definitions and generated declarations; they are not
counts of newly proved mathematical theorems.

The complete audited axiom footprint is `propext`, `Classical.choice`, and
`Quot.sound`. The maintained audit includes generated and private owned
declarations; its rejection policy was not weakened. Genuine incremental
reuse checks exact source and dependency fingerprints. The final core run
freshly compiled one module and reused 148 maintained artifacts; the final
compatibility run freshly compiled two modules and reused 70. These reuses
refer to previously compiled exact artifacts, not development-cache substitution.

Warnings remain visible: 153 in the core closure (77 selected-owner and
76 dependency), and 174 in the compatibility closure (7 selected-owner and
167 dependency). Deduplicating the repository module overlap gives 297
warnings. The public umbrella, the repaired ABS hemisphere owner, and both
`TripotentExponentialFlow` and its previously blocked consumer compile
with zero warnings. No warning-free whole-repository claim is made.

Core and umbrella execution took place at
`c3e398c825b2593637531da4e1c6e04c51294ef2`; compatibility execution took
place at `213b736cc715b5f1b46e258f6665eacd3b8df4c6`.
Independent QA binds the earlier core/umbrella result to the later source
by exact file identity while preserving the actual execution commit.
A subsequent documentation-only commit similarly requires an explicit
source-identity record; it does not change where native execution occurred.

The review/recovery archive preserves the complete invocation argument
arrays, source snapshots, semantic reviews, compiler logs, declaration
audits, source/artifact hashes and independent disposition. Its principal
native records are:

| Checkpoint | Report SHA-256 |
| --- | --- |
| `qa-35-targets-20261126T222613Z` | `2ab4765d77f35a553a931c3104dfe4d98599dcd33bdefdb0b3a0a2c4d3c450a6` |
| `qa-umbrella-20261126T222902Z` | `eaa4e63a2f4589c5a222ed7d784d96372bc2393d72643afe44818ce2eb30e6fb` |
| `qa-compatibility-7-targets-20261126T224225Z` | `e08e06747dbd6b50d950a9b640c4f11eec46330eaa56217d38fbbd74fbf588ff` |

Both declaration-audit invocations use
`python3 tools/quality/check_clifford_dirac.py`, the exact pinned
`--mathlib-root` and `--lean`, `--output /tmp/epistemic-acceptance-d292`,
`--incremental`, and explicit repeated `--target` arguments.
Each checkpoint's `invocation.json` records the complete command without
omitted targets. The import-only umbrella is compiled and ownership-probed
separately because it intentionally owns no declarations.

### Historical failures and repairs


The new-ref pre-push hook previously printed that it was running a full root
gate but invoked `post_build_gate.sh` without arguments. That script defaults
to incremental mode. The hook now passes `--full` explicitly. This change does
not make an absent path dependency available or turn a scoped native check
into a successful root build.

The first maintained acceptance run passed for
`Canonical.AttentionQueryGeometry` and `Physics.SinkhornKLProjection`.
It compiled their exact twelve-module repository closure and audited all
43 declarations in the two selected owners. Their combined axiom footprint
is exactly `propext`, `Classical.choice`, and `Quot.sound`. The accepted source
SHA-256 values are respectively
`08b0a0c4c95119ab3dcbe3d9bd7a33bcc9f86a193ed5f2d780ac37e3d80bcf04`
and `ef27792fefc4e07fba1b0f96189036fc3e194cd2012f446a119666d4036364cb`.

The working implementation contains 33 new proof-owning modules and the
import-only `Canonical.EpistemicGapImplementation` surface. The surface is
connected through `InfoGeometry.AllExhaustive`. Source integration is distinct
from acceptance of a final source hash.

The subsequent independent 26-target attempt compiled all 123 repository
modules in its selected import closure: 111 fresh compilations and 12 genuine
incremental reuses. Its strict audit then rejected the generated declaration
`InfoGeometry.Physics.AmariSinkhornAlternatingProjections.sinkhornIterates._unsafe_rec`
after 223 audit records. The attempt is recorded as rejected; successful
compilation does not override that result. The source recurrence now uses
native `Nat.rec` with exactly the same initial matrix and row-then-column
successor. Its zero/successor equations and every other declaration are
unchanged. The auditor and its permitted axiom policy are unchanged.

The first 35-owner attempt stopped at the concrete ABS coordinate-generator
proof. The accepted repair derives those identities from the actual native
Clifford lift; the represented action and the noncommuting example are
unchanged. The first six-owner compatibility run subsequently exposed a
missing one-dimensional derivative subtraction import in the unchanged
`TripotentExponentialFlow` source. Adding the direct native `Deriv.Add`
import preserves every declaration byte; the final seven-owner run both
compiles and completely audits that repaired owner. Both earlier failures
remain rejected historical records, superseded only by their respective
exact-source successful retries.

The staged source review also required repairs to two inherited proofs in
touched owners. The fixed-point proof now applies the supplied equality through
`congrArg`, and the negative-sum proof uses `(neg_add _ _).symm`; their statements
are preserved. To check the actual legacy Type-III owner, `SpectralTriple`'s sole
whole-Mathlib import was narrowed to the native compact-operator module and the
`nth_rw` tactic module. Its remaining source bytes are unchanged. The Fock owner
now explicitly imports the existing noncommutation witness for the exact
`Matrix (Fin 2) (Fin 2) ℝ` carrier, already in its transitive closure. Its stronger
local matrix/operator witness and all other declarations are unchanged. These
repairs do not weaken the source gate or assert new continuous-core or
spectral-triple constructions.

Acceptance uses the repository-maintained exact-source closure and native
axiom auditor `tools/quality/check_clifford_dirac.py` with explicit targets,
followed by the applicable staged proof and push gates. The required compiler
lock is `/tmp/info-geometry-build.lock`; neither the lock nor the dependency
pins are bypassed. The saved reports bind exact source hashes and distinguish local source
closure from the root Lake workspace and its complete configured dependency graph.

### Full repository gate and dependency disposition

The actual full repository command was invoked at 00:47:21 Europe/Sofia
on 2026-11-27, from commit
`213b736cc715b5f1b46e258f6665eacd3b8df4c6`:

```bash
bash scripts/quality/post_build_gate.sh --full
```

The invocation completed at 01:22:50 Europe/Sofia on 2026-11-27 with
**exit code 1**. After acquiring the maintained shared lock, its actual
`lake build InfoGeometry.All` stopped during dependency resolution:

```text
error: HomotopyHypothesis: package directory not found:
.../repository/external_refs/homotopy-hypothesis-lean4
```

The command did not establish a successful root project compilation. The
checkpoint `root-full-gate-20261126T224721Z/result.json` records the completed
failure, unchanged HEAD, dependency/toolchain hashes, and gate-script hashes.
The full log SHA-256 is
`e20639cd69f659ae4b36a91d27fa347184050e1b58e6e289f44af2d71e18111b`.
Lake retrieved the exact pinned Mathlib and LeanCopilot sources; no dependency
revision changed. The earlier pending-lock observation is preserved only as
historical evidence. The invocation has ended and released its build lock.

The same full invocation passed its tracked-scope, quarantine, axiom/debt and
theory checks on their available inputs. Its semantic-vacuity and
semantic-content checks each returned 2 because tracked baseline source was
absent from the sparse checkout. Those incomplete checks were not counted as
passes. Exact baseline recovery subsequently restored 29,298 absent paths and
preserved six existing symlinks. Every one of the 29,304 recovered/resolved
entries was independently checked against both the original commit and the
current Git index, including blob content and file mode. All became readable;
no existing source was overwritten, and no index, sparse configuration,
dependency pin or proof implementation changed.

A separate maintained source-gate rerun completed at 01:35:35 Europe/Sofia on
2026-11-27. All five commands returned 0:

| Source check | Result after exact baseline recovery |
| --- | --- |
| Tracked Lean scope | Passed the maintained authoritative-scope policy |
| Quarantined Lean artifacts | Passed the maintained quarantine policy |
| Axiom and debt | 28,615 selected files; no reported `sorry`, `axiom` or `admit` gaps |
| Semantic vacuity | Complete 56,950/56,950 read coverage; passed the maintained `--fail-prefix lean/` policy |
| Semantic content | Complete 27,528/27,528 selected-file coverage; no current blocking findings; 22 manifest-only quarantine entries retained |

The vacuity pass is scope-specific: its global lexical report contains 862
errors and 73,505 warnings, while the configured `lean/` blocking set contains
34,653 warnings and no errors. It is neither a zero-findings report nor a
kernel proof. The current complete reports are in
`source-gates-after-hydration-20261126T232721Z`; the earlier incomplete reports
remain in the full-gate checkpoint. The rerun's `result.json` SHA-256 is
`1440b1dad13451b891b693ffc3dcff4c728b4107f05404260cc16a9949129965`.

These source checks resolve the input-coverage defect. They do not supersede
the failed root native build. No additional root native invocation was made
after baseline recovery; the missing configured dependency remains unresolved.

The independent current read-only command
`python3 tools/infra/ci_bootstrap.py paths` exited 1 at `213b736c`:
HomotopyHypothesis is missing and untracked, Atlas's restored path remains
untracked, and GIFT's pinned gitlink is uninitialized with missing source.
InfoGeometryCore passes that direct availability/provenance check. The
preflight is not a Lean compiler result or a complete dependency compatibility
check. It establishes the remaining package restoration and source-selection
work independently of the completed failed root gate.

The changed `AllExhaustive`, `Canonical.TypeIIIContinuousCoreReal`,
`Canonical.PinOperatorFamilyBridge`, and
`Clifford.KahlerHestenesJWABSPrimary` lie outside the accepted native scopes.
Five other changed modules were compiled as dependencies, without a separate
complete audit of all their owned declarations. No whole-repository or
external-package acceptance, successful pre-push result, remote branch, or
pull request is claimed. Publication remains subject to the repository gate.

The maintained read-only dependency preflight
`python3 tools/infra/ci_bootstrap.py paths` exited 1 at the base revision.
`HomotopyHypothesis` and `Atlas` refer to missing, untracked path packages;
`GIFT` is an uninitialized gitlink at
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92`.
The tracked `InfoGeometryCore` path passed this availability check.
This is evidence about package availability, not a Lean compiler result.
That preflight did not select a replacement package or change a dependency pin.

A subsequent bounded provenance check recovered Atlas's recorded short revision
`34ffed3` as
[`facebookresearch/atlas-lean@34ffed396f376454c1a9b297f3fd74c5c801fb50`](https://github.com/facebookresearch/atlas-lean/commit/34ffed396f376454c1a9b297f3fd74c5c801fb50).
That exact source declares package `Atlas`, Lean `v4.29.0`, and Mathlib
`8a178386ffc0f5fef0b77738bb5449d50efeea95`. The origin and full revision are
therefore recovered. Its complete 2,722-file source snapshot was subsequently
restored to the configured path after every file blob, mode and Git tree was
verified against root tree `c12fe2315fe475d70a4fcee81d6b731f853373ab`.
Compatibility with the root pins is untested. The path remains ignored and is
not represented by a tracked package or gitlink, so the maintained
reproducibility preflight still reports `untracked_path_dependency`; restored
bytes alone do not satisfy that gate.

The likely HomotopyHypothesis upstream is
[`cadamcat/homotopy-hypothesis-lean4`](https://github.com/cadamcat/homotopy-hypothesis-lean4).
Its observed commit `6766fc567cfbf82a49843c698826c0d6aa47f7b5` declares the
expected package and the root's exact Lean and Mathlib versions. No recorded
root source selects that commit, so it remains a concrete candidate rather
than a silently installed replacement. The GIFT origin redirects to
`Arithmon/K7-Lean`, where the recorded exact gitlink was not retrievable in
the bounded commit/tree queries; a global exact-SHA search also returned no
match. The official exact-commit GitHub page also returned HTTP 404 after
the legitimate repository rename redirect. This does not establish absence
from every inaccessible repository.

An authentic, clean checkout of the pinned LeanArchitect revision
`54d3fb249685db8e5a564e0b3f331cff77991607` is available. Its source declares
Lean `v4.28.0`. Exact-source prior native evidence at the root's `v4.34.1`
records an API mismatch in `Architect/Command.lean`: its `exportEntriesFnEx`
callback returns the old shape where the current compiler expects
`OLeanEntries`. The current Type-III closure attempt stopped at the unavailable
compiled `Architect` import; the prior compatibility failure is separate
evidence, not a fresh successful owner check. Removing that dependency while
preserving the examined declarations was not justified by source inspection.

### Concrete unapplied dependency proposal

The review/recovery archive includes
`candidates/dependencies/leanarchitect-atlas-homotopy-pins-213b736c.patch`
with SHA-256
`aaa1612d05d0c5a9814e10a8a08e8602f975d3242878a827e5ad98dfc1f0f7d3`.
It proposes the following explicit selections consistently across
`lakefile.lean`, `lakefile.src.lean`, `lakefile.toml`, and `lake-manifest.json`:

| Package | Proposed exact source | Status |
| --- | --- | --- |
| LeanArchitect | [hanwenzhu/LeanArchitect@468e8f58fb4ad6e6ad672a08da6d0d0531e95a97](https://github.com/hanwenzhu/LeanArchitect/commit/468e8f58fb4ad6e6ad672a08da6d0d0531e95a97) | Replaces the old export-callback API; official [Lean 4.34.0 CI passed](https://github.com/hanwenzhu/LeanArchitect/actions/runs/35911821154); root 4.34.1 compatibility remains untested |
| Atlas | [facebookresearch/atlas-lean@34ffed396f376454c1a9b297f3fd74c5c801fb50](https://github.com/facebookresearch/atlas-lean/commit/34ffed396f376454c1a9b297f3fd74c5c801fb50) | Converts the path requirement to the exact Git source recovered from tracked provenance; root compatibility remains untested |
| HomotopyHypothesis | [cadamcat/homotopy-hypothesis-lean4@6766fc567cfbf82a49843c698826c0d6aa47f7b5](https://github.com/cadamcat/homotopy-hypothesis-lean4/commit/6766fc567cfbf82a49843c698826c0d6aa47f7b5) | Proposed new revision selection; its declared Lean/Mathlib pins match root, but the original intended root revision remains unknown and native compatibility remains untested |

Homotopy is used by the actual root import graph: `InfoGeometry.All` imports
`AllExhaustive`, which imports
`Twistor.Cl55RealSplitPinNullFundamentalGroup`; that owner imports
`HomotopyHypothesis.Blueprint.Henry.Topology` and uses its
`Henry.Top.homotopyEquivalences` and `Henry.Top.weakEquivalences` in theorem
statements. Approving the proposed Homotopy commit would establish a new
explicit source choice, not recover an unrecorded historical pin.

The proposed JSON and TOML parse successfully, exact field-delta and inverse
byte checks pass, and `git apply --check` passes against the unchanged four
current configuration files. The 21 other manifest entries, package order,
Lean, Mathlib, Batteries, Cli, and GIFT entry/gitlink are preserved. These
source-level checks do not establish a successful build with the proposed
packages. The earlier two-package Architect/Atlas patch is retained separately.

GIFT still requires an accessible repository or archived checkout preserving
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` with commit/tree provenance,
or an explicitly selected correction. No alternative GIFT revision has been
chosen. No package removal is proposed.

No part of either dependency patch has been applied. The repository's
[AGENTS.md](../AGENTS.md), under **Build, dependency, and cache discipline**,
requires explicit user authorization for dependency or toolchain changes.
The concrete proposal is ready for that decision; approval would permit
restoration and native validation, not itself certify the full repository.
