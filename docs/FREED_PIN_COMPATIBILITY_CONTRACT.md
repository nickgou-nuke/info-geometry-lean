# Pin representation, graded Morita, and operator compatibility

## Scope and baseline

This work connects PR #338's ordered Clifford suspension and normalized-vector
Pin construction to explicit representations, grading comparisons, geometric
operators, domains, and operator families. The baseline is
`1369d7181834704a5879e2e5dfcc0e1ad931131a`, based on upstream
`a392af178af1fe2bcba2ba39eb405700c6ee103c`.

The focused construction and expanded declaration audit have passed at the
concrete checkpoint recorded below: 973 declarations across all eighteen
selected mathematical owners, checked twice. Lean `v4.34.1`, the root dependency
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

### Concrete follow-up declaration map

The four owners below extend the earlier accepted base and are included in
the accepted 973-declaration audit recorded in the concrete follow-up section.

| Layer | Namespace and key declarations | Exact result and inputs |
| --- | --- | --- |
| Concrete smooth Morita realization | `Geometry.KleinPinSmoothMorita`: `volumeEquiv`, `sectorCoordinates`, `operatorMatrix`, `operatorMatrix_dirac`, `cliffordHeadRepresentation`, `concreteObject`, `concreteCornerIso`, `concreteReconstructionIso`, `compensated_dirac_corner`, `gradedDirac_reconstruction` | The actual volume identifies the two smooth Klein sectors. Native matrix coordinates retain every coefficient in `End ℝ S₀`, identify geometric grading, and compute the complete Dirac matrix. The concrete graded object, corner, and even reconstruction use the existing Morita equivalence. An odd head involution recovers the nonzero reduced operator from its compensated corner. |
| Concrete Pin frame family | `Geometry.KleinPinFrameFamily`: `pinFrame`, `pinFrame_eq_suspended`, `frameSmoothEquiv`, `framedDiracSmoothLinear_apply`, `frameAssociatedEquiv`, `frameTotalEquiv_dirac`, `circlePin`, `circleFrames_noncommute`, `circleSuspendedDirac_joint_contDiff` | Actual normalized Pin elements act on the specified spinor fibre. Their frame changes transport deck monodromy, Clifford coefficients, smooth domains, quotient descent, grading, and volume. The first-order differential formula is compared by the chain rule. The explicit normalized circle family has jointly smooth evaluated fields and differential images. |
| Joint frame and reduction comparison | `Geometry.KleinPinMoritaFamily`: `framedSectorCoordinates_frame`, `framedOperatorMatrix_natural`, `framedOperatorMatrix_dirac`, `framedCliffordHead_grading`, `compensated_corner_intertwine`, `circleCorner_joint_contDiff` | The same frame commutes with the actual sector-coordinate square and conjugates every entry of the full noncommutative operator matrix. The represented Clifford head, independent grading, and head-compensated corner obey this comparison; the reduced family satisfies `A_U U = U A` on its actual smooth domains. |
| Analytic suspension comparison | `KK.FreedPinAnalyticCompatibility`: `evenPinInclusion`, `positive_action`, `negative_action`, `positive_operator`, `negative_operator`, `positive_graph`, `negative_graph`, `positive_resolvent`, `negative_resolvent`, `positive_fredholmFamily`, `negative_fredholmFamily` | The pullback and actual ambient even-Pin routes give equal continuous actions, transported domains, graphs, operators, resolvents, and continuous maps into the native Fredholm subtype. Both signs preserve the explicitly supplied analytic seed and continuity hypotheses. |

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

For the concrete smooth reduction, let `S₀` and `S₁` be the two actual smooth
sectors, `K` their Clifford volume map, and `A = KD` the same-sector operator.
The coordinate equivalence is `T(ψ₀, ψ₁) = (ψ₀, -Kψ₁)`. It gives
`T D T⁻¹ = [[0,-A],[-A,0]]` over the full ring `End ℝ S₀`. The ordinary
diagonal corner vanishes. The explicitly represented odd involution with
matrix `[[0,-1],[-1,0]]` converts this to `diag(A,A)`, whose corner is `A`.
The differential operator is treated as an element of this full coefficient
ring; it is not assumed linear or superlinear over every coefficient operator.

For a frame `U`, the family constructs the deck law `U ρ U⁻¹`, coefficient
maps `U γᵢ U⁻¹`, and volume `K_U = U K U⁻¹` together. Its domain equivalence
maps `ψ` to `Uψ`. The comparison `D_U U = U D` follows from differentiation,
and hence `A_U U = U A` holds for the actual reduced operators. The general
frame formulas specialize to the represented normalized Pin group, including
the explicit family `(cos t, sin t)`. Smoothness is asserted for evaluated
fields and differential images in these domain identifications.

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

The concrete follow-up connects the Klein smooth operator to the particular
Pin construction through its full algebra representation, normalized
glide-reflection element, differential coefficients, actual smooth domains,
and a graded matrix/Clifford-head Morita object. Its explicit head-compensated
corner is the same-sector differential operator, and that reduction obeys
the same Pin frame family. This is distinct from constructing a representation
of the separate canonical infinite Clifford tail into `End ℝ S₀`. That tail
representation, and therefore an identification with the canonical split-tower
module, remain absent.

The concrete operator also has no constructed `L²`/Sobolev completion here and
has not been instantiated as the generic closed-domain or bounded Fredholm
seed. The algebraic Morita equivalences do not establish analytic Hilbert-module
equivalence. The tower result concerns the algebraic colimit and naturality of
finite matrix presentations, without a categorical colimit of module categories.
The full represented Pin group is distinct from the subgroup preserving the
Klein deck lattice. A curved Pin-frame bundle, geometric elliptic regularity,
a general family index in `KO(B)`, and differential `KO` groups and pushforwards
remain separate construction targets.

### Analytic source boundary

The bounded source review inspected the Klein geometric owners, split-Krein
domain and resolvent interfaces, Cantor/Cuntz analytic owners, bounded `L²`
multiplier owner, and the pinned native Fourier, `lp`, compact-operator, and
Fredholm APIs. No complete declaration-graph absence claim is made.

[`Canonical/KreinCarrierInstances/Carrier.lean`](../lean/InfoGeometry/Canonical/KreinCarrierInstances/Carrier.lean)
defines `KleinBottleCarrier` as `WithLp 2 (ℝ × ℝ)`, a finite-dimensional chart
carrier. It is not the Hilbert space of spinor sections needed here.
[`KK/RealSplitKreinUnboundedCycle.lean`](../lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean)
stores density, closed graph, and resolvent data as input fields; its regularity
theorem reads those fields. These owners therefore cannot discharge the
concrete operator's analytic hypotheses by themselves.

Native `UnitAddTorus.mFourierBasis`, `lp.mapCLM`, `lp.hasSum_single`, and
`isCompactOperator_of_tendsto` supply useful ingredients for a later compact
Fourier model with full finite matrix blocks. The first missing geometric
comparison is an actual Hilbert inclusion of the existing smooth Klein
sections, followed by a proof that Fourier transformation takes their
Fréchet-defined Dirac operator to the appropriate block multiplier and that
the equivariant finite Fourier modes form a dense core. A weighted sequence
domain without that comparison would leave the particular geometric operator
unidentified. None of these future analytic conclusions is inferred from the
smooth Morita or frame identities in this PR.

## Verification record

### Acceptance policy

Acceptance requires exact focused kernel builds, exhaustive declaration axiom
inspection, source/debt screening, and independent mathematical review. The
expanded audit selects eighteen mathematical owners, including private and generated
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

### Earlier accepted base and exhaustive audit

[Focused CI run 43394851127](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43394851127)
completed successfully at upstream commit
`8f5bbd0bbc297ce407b184e17eda75510ccba067`, tree
`f17d6496cb73e2e2b1bb72bf1c5206ee2d79e053`. The corresponding local checkpoint
is `4ffd54100330803359fce34fda4c26f957951702`, with the same tree. This is the
accepted base checkpoint. The later concrete checkpoint below separately
certifies the four added owners and expanded audit.

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
concrete follow-up head `bc3cea7eebc70360085200126ebb3fca101508e2` identify
failures before the relevant integration builds:

| Workflow | Observed blocker |
| --- | --- |
| [Reviewed PR Integration, run 43469885061](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43469885061) | Recursive checkout failed with `No url found for submodule path 'external_refs/auto-ontology' in .gitmodules`; the kernel and audit steps were skipped. |
| [Root CI, run 43469884527](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43469884527) | Path-package preflight found missing/untracked HomotopyHypothesis and Atlas package configurations, plus an uninitialized pinned GIFT gitlink. The baseline build was skipped. A later smoke-summary attempt also reported that the HomotopyHypothesis package directory was absent. |

The relevant `.gitmodules`, root Lake configuration, dependency manifest, and
Lean toolchain are unchanged from the stated upstream baseline. These errors
are separate from the successful focused proof run. No substitute package,
dependency revision, or relaxed acceptance criterion was introduced.

The tracked local pre-push hook was also invoked manually over the full
concrete follow-up range
`1369d7181834704a5879e2e5dfcc0e1ad931131a..f7693d40d29b6d957063b5fa9e0a6e76d426818b`.
Its workspace/ref prechecks and classification of 21 changed Lean owners
completed, and it acquired the shared build lock. The Lake child terminated
with signal 9 (wrapper exit 247), and the semantic source audit later exited
137. The separate source debt scan found no `sorry`, `axiom`, or `admit` in
those 21 files. Tracked-scope and quarantine classification completed. This
was a failed root gate, not kernel or semantic acceptance. The cause of the
local process termination was not established. Publication through the GitHub
connector does not itself execute the local pre-push hook.

PR #338 remains a published draft. Promotion still requires reproducible root
package/submodule configuration and a successful root integration gate. The
focused acceptance now includes the concrete smooth Klein Morita corner and
its joint Pin frame family. It does not claim a concrete Klein
Hilbert/Fredholm model or a geometric/differential `KO` pushforward.

## Concrete follow-up contract

The four concrete owners extend the earlier accepted checkpoint and satisfy
the following construction contract. Their kernel builds and expanded
exhaustive audit have completed successfully.

| New owner target | Construction specified by the contract |
| --- | --- |
| Concrete smooth Morita realization | Use the actual volume action to identify the two smooth Klein sectors. Construct coordinates on their doubled domain, identify its full endomorphism algebra with matrices over the first sector's noncommutative endomorphism ring, compare grading, and compute the actual differential operator matrix. Instantiate the existing graded module equivalence. Recover the reduced differential operator through an explicit off-diagonal entry or head-compensated corner; the ordinary diagonal corner of the odd operator is zero. |
| Concrete Pin frame family | Construct frame changes from the actual represented normalized Pin elements. Conjugate the deck monodromy and Clifford coefficients together, prove smooth-domain and derivative compatibility and quotient descent, and retain the ordered group composition. Construct an explicit normalized-vector trigonometric family and derive its represented parameter continuity. |
| Joint Morita and frame compatibility | Transport the volume with the same frame, prove the square of smooth-sector coordinate maps commutes, and prove naturality of every entry of the full operator-valued matrix. Compare the actual geometric grading, differential operator, represented split head, and compensated corner; derive joint smoothness of evaluated coordinates and reduced differential images for the explicit Pin family. |
| Analytic suspension compatibility | Compare the pullback Pin action with the actual ambient even-Pin inclusion as continuous linear equivalences. Prove equality of image domains, transported graphs, resolvents, and continuous native Fredholm families, for both suspension signs and with the source analytic hypotheses unchanged. |

The new targets are implemented in `Geometry.KleinPinSmoothMorita`,
`Geometry.KleinPinFrameFamily`, `Geometry.KleinPinMoritaFamily`, and
`KK.FreedPinAnalyticCompatibility`. Independent source review found no
mathematical sign, order, carrier, or assumption defect. Compiler-guided
repairs made the subtype evaluation, extensionality depth, smooth function
comparisons, and componentwise arithmetic explicit without changing the
mathematical statements or weakening the audit.

### Accepted concrete checkpoint

[Focused CI run 43469884874](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43469884874)
completed successfully at upstream commit
`bc3cea7eebc70360085200126ebb3fca101508e2`, tree
`6428205d009042434a42fb3bc903367eee351776`. The corresponding local commit is
`4555cb54074cd67d19d4edf7443f8afead8dc75f`, with the same tree. Subsequent
documentation changes preserve all eighteen mathematical owner files and the
audit source certified by this run.

| Validation | Observed result |
| --- | --- |
| Representation, geometric, and domain foundations | Passed; 8993 build jobs. |
| Existing Clifford tensor, operator, and family compatibility | Passed; 9020 build jobs. |
| All four concrete follow-up owners, including the joint comparison | Passed; 9023 build jobs. |
| Actual algebraic Clifford tower | Passed; 3597 build jobs. |
| Complete focused default-target closure | Passed; 9059 build jobs. |
| Exhaustive audit during the default-target build | Passed; 973 distinct declarations across all 18 selected owners. |
| Direct audit with `-DwarningAsError=true` | Passed; the same 973 declaration names and owner counts. |
| Reported axiom dependencies in both executions | Exactly `[propext, Classical.choice, Quot.sound]`. |

The two exhaustive logs were reconciled by exact ordered declaration name and
owner, with no duplicates. Every owner had a positive count, and the counts
summed to 973 in both executions. The fourteen earlier owner counts remain
exactly as listed above. The four added owners contribute 291 declarations:

| Mathematical owner | Audited declarations |
| --- | ---: |
| Earlier fourteen owners | 682 |
| `Geometry.KleinPinSmoothMorita` | 89 |
| `Geometry.KleinPinFrameFamily` | 120 |
| `Geometry.KleinPinMoritaFamily` | 49 |
| `KK.FreedPinAnalyticCompatibility` | 33 |
| **All eighteen owners** | **973** |

The build reports two nonfatal unused-simplifier-argument lints in
`KleinPinMoritaFamily.coordinateFrame_symm_single`; these are repeated when
Lake replays that owner. There are no proof errors. The direct exhaustive
audit with warnings treated as errors passed. The existing audit generator
and its previously passing 27 fixture tests are unchanged.

The workflow uploaded all stage logs and the source/toolchain receipt in the
[freed-pin-compatibility-evidence artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43469884874/artifacts/14061865897).
Local single-owner compiler attempts had terminated with exit 247 before
Lean diagnostics (the profiled attempt reported 843204 KiB maximum resident
memory); the completed upstream run provides the kernel acceptance evidence.

The new targets preserve the distinction between an actual algebraic Morita
object and an operator that is linear or superlinear for its coefficient
action. No centrality of the concrete differential operator is assumed.
An arbitrary fibre Pin frame need not preserve a fixed Klein deck law; the
family target therefore constructs the transported deck law explicitly.
The concrete Hilbert/Sobolev realization, its Fredholm seed, and differential
`KO` pushforward remain analytic construction targets unless separately proved.
The new coefficient ring is the full endomorphism algebra of the concrete
positive smooth sector. No representation of the separate canonical infinite
Clifford tail in that coefficient ring has been constructed here.
