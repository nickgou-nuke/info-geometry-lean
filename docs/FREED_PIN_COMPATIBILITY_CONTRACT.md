# Pin representation, graded Morita, and operator compatibility

## Scope and baseline

This work connects PR #338's ordered Clifford suspension and normalized-vector
Pin construction to explicit representations, grading comparisons, geometric
operators, domains, and operator families. The baseline is
`1369d7181834704a5879e2e5dfcc0e1ad931131a`, based on upstream
`a392af178af1fe2bcba2ba39eb405700c6ee103c`.

The focused construction and exhaustive declaration audit have passed at the
accepted code checkpoint recorded below. Lean `v4.34.1`, the root dependency
revisions, the quality-gate criteria, and the root gate entrypoints are
unchanged. The audit implementation caches an immutable module-name array;
its coverage and rejection criteria are unchanged. The constructions reuse
native Clifford algebras, graded tensor products, matrix module categories,
continuous linear maps, and Fredholm operators. Whole-root integration remains
blocked by the separately observed repository configuration failures below.

## Declaration map

Namespace prefixes are relative to `InfoGeometry`. The listed definitions give
actual maps or carriers; the listed theorems state their comparison equations
and invariants. The selected-owner audit, rather than this abbreviated map,
determines exhaustive declaration coverage.

| Layer | Namespace and key declarations | Exact result and inputs |
| --- | --- | --- |
| Ordered Pin representations | `Clifford.FreedPinRepresentation`: `positiveRepresentation`, `negativeRepresentation`, `positiveRepresentation_pair`, `negativeRepresentation_pair`, `pinRepresentation`, `positivePinRepresentation_comp`, `negativePinRepresentation_comp`, `continuousPinAction` | Pullback of a supplied native Clifford algebra representation through the actual ordered suspension maps; restriction agrees with the constructed normalized-vector Pin homomorphisms. A bounded representation gives each Pin element an actual continuous linear automorphism. |
| Source and ambient grading | `Clifford.FreedPinRepresentation`: `positivePin_preserves_grading`, `negativePin_preserves_grading`; `Clifford.Cl11GradedMorita`: `cl11StandardEquiv_grade`, `freedPositiveLineRepresentation_ι`, `freedPositiveLineRepresentation_ι_even` | Target-vector anticommutation implies commutation with every suspended source Pin action. In the explicit split-line model, the source generator acts by `t • Eplus` and is ambient even. The source Clifford grading and the ambient grading remain distinct. |
| Concrete Klein representation | `Clifford.FreedKleinRepresentation`: `representation`, `representation_ordered_pair`, `pullback_eq_positiveRepresentation`, `positivePinHom_representation`, `glidePin`, `suspended_glide_action`, `dirac_eq_ordered_suspension` | The suspended representation is constructed from the existing Klein Clifford action and its volume matrix. The full pulled-back algebra action agrees with the existing action; an actual normalized Pin element gives the fibre reflection of the existing Klein glide; the geometric Dirac coefficients are the represented ordered suspension products. |
| Geometric operator and smooth domain | `Geometry.KleinPinDirac`: `dirac`, `dirac_equivariant`, `descendedDiracSection`, `differentiableSections`, `diracLinear`, `smoothSections`, `diracSmoothLinear`, `gradedDirac`, `grading_sq`, `grading_dirac_anticommute`, `gradedDirac_cosine_nonzero` | Fréchet differentiation and the actual deck action prove that the source Dirac operator switches orientation sectors. The doubled smooth-section domain carries an explicitly involutive grading and a nonzero odd differential operator. The grading declarations live in `Geometry/KleinPinGradedDirac.lean` under the same namespace. |
| Suspended geometric operator | `Clifford.FreedKleinRepresentation`: `suspendedDirac_eq_volume_dirac`, `suspendedDirac_equivariant`, `descendedSuspendedDiracSection`, `suspendedDiracSmoothLinear`, `suspendedDirac_cosineField_nonzero` | The operator defined from suspended vector coefficients equals the volume action composed with the source Dirac operator. Its second sector switch makes it preserve each smooth sector. It is a distinct differential operator with its own quotient descent and nonzero witness. |
| Graded matrix and operator reduction | `OperatorAlgebra.GradedMatrixMorita`: `matrixEquivalence`, `liftSemilinearOperator`, `reduceSemilinearOperator`, `counit_intertwines_semilinear`, `unit_intertwines_semilinear` | The native matrix Morita functors lift to modules with semilinear additive involutions over an arbitrary coefficient ring automorphism. Their unit and counit are even. Superlinear operators are reconstructed from their actual corner restrictions, retaining the full coefficient action. |
| Graded Clifford tensor | `Clifford.Cl11GradedTensorMorita`: `head_tail_supercommute`, `matrixToTensor_tensorToMatrix`, `tensorToMatrix_matrixToTensor`, `tensorMatrixEquiv`, `tensorParity_compatible`, `cliffordHeadCancellation`, `tensor_matrix_units_noncomm` | A native real graded coefficient algebra gives the actual graded tensor presentation as two-by-two matrices over that entire algebra. The four-unit inverse proves bijectivity. Independently specified factorwise parity agrees with matrix parity, and the constructed module-category equivalence cancels the Clifford head. |
| Actual algebraic tower | `Canonical.SplitCliffordHeadMorita`: `headTailEquiv_involute_tmul`, `splitInfinityMatrixEquiv`, `splitInfinityMatrixEquiv_grade`, `splitInfinityGradedCancellation`, `finiteHeadMatrixEquiv_bond` | The existing algebraic direct limit is identified with matrices over its full algebraic tail. The comparison preserves its canonical grading, and the finite matrix presentations commute with the actual fixed-head bonding maps. |
| Operator domains and Pin families | `KK.LinearDiracTransport`: `domainEquiv`, `operator`, `dense_domain`, `closed_graph`, `kernelSectorEquiv`, `resolvent_shifted`; `KK.PinLinearDiracTransport`: `pin_operator_mul_on_domain`, `positive_pin_domain_eq`, `continuous_pin_inverse_family`, `continuous_pin_conjugate_family`, `continuous_pin_resolvent_family` | A supplied domain `S` and operator `D : S →ₗ[ℝ] H` are transported to their actual images and conjugates. Density, closed graph, and compact resolvent data are transported from explicit inputs; the right-resolvent equation uses source shifted-operator injectivity. Banach-space families retain the explicit operator-norm continuity hypothesis on represented unit values. |
| Native Fredholm families | `KK.PinFredholmTransport`: `isFredholm_conjugate_iff`, `index_conjugate`, `pinFredholmFamily`, `pinFredholmFamily_index`, `pin_eventually_fredholm_index`, `exponentialFredholmFamily`, `exponentialFredholmFamily_index` | A bounded seed satisfying native `ContinuousLinearMap.IsFredholm` gives continuous Pin-conjugacy and exponential families in the Fredholm subtype. The native kernel-minus-cokernel index is preserved, and native local stability also controls nearby operators. Exponential continuity is derived in `KK.LinearDiracTransport.continuous_conjugate_expAutomorphism`. |

## Preconditions and conventions

The general matrix category consists of semilinear additive involutions over a
specified coefficient ring automorphism. It is not identified with a direct-sum
`ZMod 2` grading over arbitrary rings where two may fail to be invertible.
The real Clifford tensor specialization supplies a native graded algebra and
derives involutivity of coefficient parity from its even and odd components.
Its tail action is `diag(a, θ a)`, and its inverse reconstructs every matrix
entry. No commutativity or finite-dimensionality of the tail is assumed.

The source Klein Dirac operator changes the orientation character of the
section's equivariance sector. Its chain-rule proof precedes quotient descent.
The volume-composed suspended operator preserves each sector because the volume
action contributes a second sector change. The two-dimensional Klein model is
not identified with the repository's three-dimensional quaternion model.
Neither ambient evenness nor the smooth-domain doubling supplies a grading on
the original irreducible spinor fibre.

An analytic domain is an actual `Submodule`, and an unbounded operator is a
linear map on that domain. Density, closed graph, and compact-resolvent data are
explicit inputs to transport. A right-resolvent identity requires injectivity
of the shifted source operator. General continuous linear conjugation does not
imply adjoint or metric compatibility. The theorem
`KK.CompactPhaseObstruction.finiteDimensional_of_compact_phase` proves that a
compact bounded operator with compact square defect forces finite-dimensionality;
a compact resolvent is not silently treated as an infinite-dimensional bounded
Fredholm phase.

The Fredholm family starts from a bounded operator satisfying native
`ContinuousLinearMap.IsFredholm`, which includes strictness, closed range,
finite kernel and cokernel, and a complemented kernel. Operator-norm continuity
of represented Pin unit values is explicit; inverse continuity follows from
Banach-algebra inversion. The exponential family derives continuity from its
actual derivative law. The bounded maps defining kernel-range sectors need not
be projectors unless idempotence is supplied. Finite-dimensionality is an
additional hypothesis when interpreting their `finrank` differences as chiral
zero-mode indices; those differences remain distinct from the native Fredholm
index.

## Dependency order and remaining edges

The ordered algebra maps precede represented Pin actions; generator equations
precede grading and operator intertwining. The actual derivative calculation
precedes equivariant descent. Continuous conjugation precedes graph and
resolvent transport; kernel equivalences and Fredholm transport precede index
invariance. No index or geometric interpretation is used to justify an earlier
algebraic identity.

The concrete Klein smooth operator is connected to the particular Pin
construction through its full algebra representation, normalized glide-reflection element,
differential coefficients, and smooth domains. It is **not yet instantiated
as an object of the split-tower Morita equivalence**, and no concrete Morita
corner reduction of that operator is constructed. The general algebraic
operator-reconstruction theorem and the concrete differential construction
remain separate results.

The concrete operator also has no constructed `L²`/Sobolev completion here and
has not been instantiated as the generic closed-domain or bounded Fredholm
seed. The algebraic Morita equivalences do not establish analytic Hilbert-module
equivalence. The tower result concerns the algebraic colimit and naturality of
finite matrix presentations, without a categorical colimit of module categories.
The full represented Pin group is distinct from the subgroup preserving the
Klein deck lattice. A curved Pin-frame bundle, geometric elliptic regularity,
a general family index in `KO(B)`, and differential `KO` groups and pushforwards
remain separate construction targets.

## Verification record

### Acceptance policy

Acceptance requires exact focused kernel builds, exhaustive declaration axiom
inspection, source/debt screening, and independent mathematical review. The
audit selects fourteen mathematical owners, including private and generated
declarations. It rejects unsafe and partial declarations, requires a positive
count for every owner, and allows only `propext`, `Classical.choice`, and
`Quot.sound`. The focused build does not certify unrelated root default targets
or optional path dependencies.

The pre-existing Maurer-Cartan curvature definition and its skewness theorem
were moved unchanged, with the same namespace and types, from `BerryConnection`
to `Canonical.MaurerCartanCurvature`. `BerryConnection` re-exports that owner;
`BogoliubovVielbein` imports it directly. This narrows the quasilattice import
closure without changing the mathematical declarations, dependency pins, or
genuine blueprint annotations elsewhere.

### Accepted code and exhaustive audit

[Focused CI run 43394851127](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43394851127)
completed successfully at upstream commit
`8f5bbd0bbc297ce407b184e17eda75510ccba067`, tree
`f17d6496cb73e2e2b1bb72bf1c5206ee2d79e053`. The corresponding local checkpoint
is `4ffd54100330803359fce34fda4c26f957951702`, with the same tree. This is the
accepted code checkpoint; subsequent documentation changes do not alter the
mathematical owners or audit source certified by that run.

| Validation | Observed result |
| --- | --- |
| Foundations: representations, geometry, and domains | Passed; 8993 build jobs. |
| Clifford tensor, operator, and family compatibility | Passed; 9020 build jobs. |
| Actual algebraic Clifford tower | Passed; 3597 build jobs. |
| Complete focused default-target closure | Passed; 9055 build jobs. |
| Exhaustive audit during the default-target build | Passed; 682 declarations across all 14 selected owners. |
| Direct audit with `-DwarningAsError=true` | Passed; the same 682 declarations and owner counts. |
| Reported axiom dependencies in both executions | Exactly `[propext, Classical.choice, Quot.sound]`. |
| Existing audit-generator Python fixtures | All 27 tests passed through the shared-lock wrapper. |

The two audit executions were reconciled by exact declaration name and owner:
each contained 682 distinct declaration records, the ordered lists matched,
and the owner counts summed to 682. The coverage includes private and generated
declarations. The owner counts, with prefixes relative to `InfoGeometry`, are:

| Mathematical owner | Audited declarations |
| --- | ---: |
| `Clifford.FreedPinRepresentation` | 48 |
| `OperatorAlgebra.GradedMatrixMorita` | 153 |
| `Clifford.Cl11GradedMorita` | 42 |
| `Clifford.Cl11GradedTensorMorita` | 57 |
| `Geometry.KleinPinDirac` | 112 |
| `Geometry.KleinPinGradedDirac` | 22 |
| `Clifford.FreedKleinRepresentation` | 59 |
| `KK.LinearDiracTransport` | 50 |
| `KK.CompactPhaseObstruction` | 2 |
| `KK.LinearDiracExponentialTransport` | 7 |
| `KK.PinLinearDiracTransport` | 27 |
| `KK.PinFredholmTransport` | 28 |
| `Canonical.SplitCliffordHeadMorita` | 63 |
| `Canonical.MaurerCartanCurvature` | 12 |
| **Total** | **682** |

The workflow uploaded its logs and source/toolchain evidence in the
[freed-pin-compatibility-evidence artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43394851127/artifacts/14022219351).
The exact exhaustive commands, run from the repository root, are:

```sh
python3 verification/freed-pin-compatibility/check.py build
python3 verification/freed-pin-compatibility/check.py env lean \
  -DwarningAsError=true \
  "$PWD/lean/InfoGeometry/Clifford/FreedPinCompatibilityAudit.lean"
```

### Audit implementation and source review

The accepted audit caches `env.header.moduleNames` once, avoiding reconstruction
of the same array inside the full constant scan. It preserves the complete
`env.constants` scan, native `getModuleIdxFor?` ownership selection,
private/generated coverage, `Lean.collectAxioms`, unsafe/partial rejection,
logs, and counts. Independent source review confirmed equivalent selection,
and the generated audit was checked for exact equality with the maintained
generator's output. All 27 existing Python generator tests passed using:

```sh
python3 verification/freed-pin-compatibility/check.py env python3 \
  "$PWD/tests/test_reviewed_audit_source.py"
```

All fourteen mathematical owner files are byte-identical to the preceding
implementation checkpoint, local `20b29096f5ce6c753c4f0a0357888acaedb4360f`
and upstream `5a739b1cd6df28e4e69949dbd056cea9953717a1`. The accepted code
checkpoint adds only the audit-array optimization and matching existing test
fixture updates to those bytes. The preceding workflow's unfinished audit was
superseded; acceptance comes from the completed run linked above.

Independent mathematical source review found no sign, order, carrier,
noncommutativity, or circularity defect in the implemented constructions and
final tensor/tower repairs. The staged source gate passed on the source
commits. Source review and Python tests are distinct from Lean kernel
acceptance. A duplicate local focused run was intentionally interrupted after
the independent CI implementation stages succeeded; it is not a completed
local full build or audit.

### Root integration status

Root integration has **not** passed. Two completed upstream workflows for the
accepted PR head identify failures before the relevant integration builds:

| Workflow | Observed blocker |
| --- | --- |
| [Reviewed PR Integration, run 43394851591](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43394851591) | Recursive checkout failed with `No url found for submodule path 'external_refs/auto-ontology' in .gitmodules`; the kernel and audit steps were skipped. |
| [Root CI, run 43394851587](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43394851587) | Path-package preflight found missing/untracked HomotopyHypothesis and Atlas package configurations, plus an uninitialized pinned GIFT gitlink. The baseline build was skipped. A later smoke-summary attempt also reported that the HomotopyHypothesis package directory was absent. |

The relevant `.gitmodules`, root Lake configuration, dependency manifest, and
Lean toolchain are unchanged from the stated upstream baseline. These errors
are separate from the successful focused proof run. No substitute package,
dependency revision, or relaxed acceptance criterion was introduced.

The tracked local pre-push hook was also invoked manually over the full
follow-up range
`1369d7181834704a5879e2e5dfcc0e1ad931131a..4ffd54100330803359fce34fda4c26f957951702`.
Its workspace/ref prechecks and changed-owner classification completed. It
then waited for the shared build lock and was interrupted while still queued
(exit 130), after the completed upstream blockers were inspected. It produced
no root build or post-build acceptance result. The unrelated lock holder was
left running. Publication through the GitHub connector does not itself execute
the local pre-push hook.

PR #338 remains a published draft. Promotion still requires reproducible root
package/submodule configuration and a successful root integration gate. The
focused acceptance does not establish a concrete Klein Hilbert/Fredholm model,
a concrete Klein Morita corner, or a geometric/differential `KO` pushforward.
