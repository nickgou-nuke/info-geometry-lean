# Dual-seed Hodge splitting and the native Lean architecture

## Intake, provenance, and scope

This continuation of PR #304 addresses the Bulgarian Lean architecture proposal
received on 2026-11-10, after published head
`11550b59ebd1ac88e8fb54fd1d78afeeefb66894`. The proposal supplies a weak
`CliffordAtom` record, a proposed `Derivation ℝ A A` constructor, the ordinary
adjoint anticommutator, and an elementary joint-commutation equivalence. It also
discusses Clifford towers, Cantor inverse systems, Krein topology, modular
theory, and Majorana protection.

The new mathematical construction concerns an arbitrary associative algebra
and an explicit normalized dual-seed pair. It constructs the harmonic
projection and Green operator, identifies the adjoint-Laplacian kernel and
range, and proves their algebraic direct-sum decomposition. The remaining
architecture is connected to actual existing owners below.

The dependency pins are unchanged: Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## 1. Correct the types before proving the claim

| Input surface | Source-grounded correction |
| --- | --- |
| `CliffordAtom` supplies square-zero generators and a commuting element | These laws describe a real associative algebra with selected elements. They do not construct a native `CliffordAlgebra`, its universal property, or the relation `db + bd = 1`. |
| `P₀ : A` is called the kernel | The joint centralizer is a `Subalgebra`. A selected element of it, such as the tilt direction `z`, has type `A`. The residual support `r = 1-db-bd` is a third, different object. |
| `inner_derivation : Derivation ℝ A A` | At the pinned Mathlib revision, `Derivation R A M` requires `[CommSemiring A]`; its Leibniz law uses a left module, and its constructor includes `map_one_eq_zero'`. Adding commutativity would make the intended inner commutators vanish. |
| `ring` is used for the noncommutative multiplication proofs | Use the existing native `LieAlgebra.ad` and associative-ring identities. `CliffordDirac.inner_ad_leibniz` already proves the full ordered Leibniz rule. |
| `harmonic_iff_in_P₀` | The displayed equivalence only unpacks two zero commutators. It contains neither the anticommutator operator nor a decomposition theorem. |
| `D = [P₁,P₂]` is called a Radon–Nikodym generator | The algebraic commutator is the existing Cartan coefficient. A measure/state and a proved transport or modular identification are separate requirements. |
| A two-dimensional real quadratic form takes values `1` and `-1` | In that dimension the sign condition does force indefiniteness and nondegeneracy. The snippet still supplies no selected fundamental symmetry, compatible topology, Clifford equivalence, or tower maps. |

The native derivative is already

$$
\operatorname{ad}_d(x)=dx-xd.
$$

The exact ordinary square-zero identity is
`LieJordanBoundaryOperators.ad_sq_of_sq_zero`:

$$
\operatorname{ad}_d^2(x)=-2dxd \quad\text{when }d^2=0.
$$

Thus square-zero coefficients alone do not turn the ordinary adjoint maps into
a cochain differential. The graded differential, doubled boundary operators,
and ordinary double commutator have separate existing owners.

## 2. Exact carrier and normalization

The operator identities before division use

```lean
[CommRing R] [Ring A] [Algebra R A]
```

The harmonic/Green construction uses

```lean
[Field K] [Ring A] [Algebra K A]
h : IsDualSeedPair d b
h2 : (2 : K) ≠ 0
```

The existing `IsDualSeedPair` means exactly

$$
d^2=b^2=0,\qquad dbd=d,\qquad bdb=b.
$$

There is no star operation, positivity assumption, finite-dimensionality
assumption, full-support assumption, or ambient commutativity assumption.
A zero pair is permitted; the independent closed matrix fixtures supply
nontrivial instances.

Put

$$
p=db,\quad q=bd,\quad e=p+q,\quad r=1-p-q.
$$

The existing operator is
`LieJordanGenerators.symmetricGenerator`, with its existing minus sign.
Throughout this document,

$$
\Delta=-\operatorname{symmetricGenerator}(d,b)
=\operatorname{ad}_d\operatorname{ad}_b+
 \operatorname{ad}_b\operatorname{ad}_d.
$$

This is a sign convention for an algebraic endomorphism, not an abstract
positivity assertion. Multiplication in `Module.End K A` is composition.

## 3. Construct the balanced projection and normalized Green operator

The old, directional retraction is

$$
\Phi_{d,b}(x)=pxp+bxd+rxr.
$$

The new definition `balancedCentralizerProjection` reuses that owner:

$$
\Psi=\tfrac12(\Phi_{d,b}+\Phi_{b,d}),\qquad
\Psi(x)=\tfrac12(pxp+qxq+dxb+bxd)+rxr.
$$

The new `dualSeedGreen` is a native linear combination of the existing
bilateral linear maps:

$$
G(x)=exr+rxe+\tfrac12(pxq+qxp)
 +\tfrac18(pxp+qxq-dxb-bxd).
$$

Both maps act on the whole ambient algebra. Their formulas retain arbitrary
corner coefficients and multiplication order.

The proof resolves three operator sectors, on both the input and output side:

| Sector evaluated at `x` | Action of `Δ` |
| --- | --- |
| `e*x*r + r*x*e` | Multiplication by `1` |
| `p*x*q + q*x*p` | Multiplication by `2` |
| `p*x*p + q*x*q - d*x*b - b*x*d` | Multiplication by `4` |

These six sector/readout lemmas are proved over a commutative coefficient ring
and an unrestricted associative ambient ring. They are not coordinate or
diagonal replacements for that ambient algebra. The weights need not be
distinct in every allowed field.

Cancelling two and its powers proves the two exact Green identities:

$$
\boxed{\Delta G=G\Delta=I-\Psi.}
$$

The explicit formula also proves that `G x = 0` for every element commuting
with both seeds. This normalizes the Green operator on the harmonic subspace.

Owner:
[`Core/DualSeedHodgeOperators.lean`](../lean/InfoGeometry/Core/DualSeedHodgeOperators.lean).

Principal declarations, in `InfoGeometry.Core.DualSeedPeirce`:

- `balancedCentralizerProjection`, `dualSeedGreen`;
- `balancedCentralizerProjection_apply`, `dualSeedGreen_apply`;
- `IsDualSeedPair.neg_symmetricGenerator_mixed`;
- `IsDualSeedPair.neg_symmetricGenerator_offDiagonal`;
- `IsDualSeedPair.neg_symmetricGenerator_diagonalDifference`;
- the three reverse-order readout lemmas;
- `IsDualSeedPair.neg_symmetricGenerator_mul_dualSeedGreen`;
- `IsDualSeedPair.dualSeedGreen_mul_neg_symmetricGenerator`;
- `IsDualSeedPair.dualSeedGreen_eq_zero_of_commute`.

## 4. Kernel, range, and algebraic Hodge decomposition

Averaging the existing retractions proves directly that `Ψ` lands in the
whole common commutant and fixes every element of it. Consequently,

$$
\Psi^2=\Psi,\qquad
\operatorname{im}\Psi=C_A(\{d,b\}).
$$

For the nontrivial kernel converse, apply `GΔ=I-Ψ` to an element killed by
`Δ`. It is fixed by `Ψ`, hence belongs to the common commutant. The reverse
inclusion follows from vanishing of both adjoint maps. This proves the native
submodule equality

$$
\boxed{\ker\Delta=C_A(\{d,b\}).}
$$

Both Green identities and the projection laws give

$$
\Psi\Delta=\Delta\Psi=0,\qquad
\operatorname{im}\Delta=\ker\Psi.
$$

The construction then establishes native `IsCompl`:

$$
A=\ker\Delta\oplus\operatorname{im}\Delta,
\qquad
x=\Psi(x)+\Delta(G(x)).
$$

The summands are uniquely determined by their complementary subspaces.
This is an algebraic kernel/range split. It supplies no elliptic complex,
analytic domain theorem, boundary conditions, or de Rham/cohomological
interpretation.

The Green operator also satisfies the existing repository predicate

```lean
InfoGeometry.Singular.Drazin.IsDrazinInverse
  (-symmetricGenerator (R := K) d b) (dualSeedGreen K d b) 1
```

by proving its three equations. This is a constructed Drazin witness at index
one; the statement does not assert a separately defined minimal-index theorem.

Owner:
[`Core/DualSeedHodge.lean`](../lean/InfoGeometry/Core/DualSeedHodge.lean).

Principal declarations in the `IsDualSeedPair` namespace:

- `balancedCentralizerProjection_mem`, `balancedCentralizerProjection_eq_self_iff`;
- `balancedCentralizerProjection_mul_self`, `balancedCentralizerProjection_range`;
- `ker_neg_symmetricGenerator_eq_centralizer`;
- `range_neg_symmetricGenerator_eq_ker_balancedCentralizerProjection`;
- `balanced_hodge_decomposition`;
- `isCompl_ker_range_neg_symmetricGenerator`;
- `dualSeedGreen_mul_balancedCentralizerProjection`;
- `dualSeedGreen_isDrazinInverse`.

## 5. Closed witnesses and the two necessary distinctions

The fixture reuses the existing dense real three-by-three `denseSeed` and
its adjoint. The actual carrier for coefficients is the whole matrix algebra;
its native adjoint actions are endomorphisms of all nine matrix coordinates.

First, the weak input permits taking the partner to be zero. Both generator
squares then vanish and a centralizing stored element can also be zero, while
the anticommutator itself vanishes everywhere. The actual adjoint partner
`denseSeedᴴ` does not commute with the source. The new closed theorem therefore
proves strict inclusion

$$
C_A(\{d,0\})\subsetneq\ker\Delta_{d,0}.
$$

This demonstrates why the normalization hypotheses of the generic theorem
must remain visible.

Second, the old directional retraction and new harmonic projection differ.
For `H=db-bd`,

$$
\Phi_{d,b}(H)=e,\qquad\Psi(H)=0,\qquad\Delta(H)=4H.
$$

The dense fixture proves `Φ(Δ(H)) ≠ 0`. Thus the old retraction cannot be
substituted for the harmonic projection in the Green identities.

Owner:
[`Canonical/JointCentralizerHodgeAudit.lean`](../lean/InfoGeometry/Canonical/JointCentralizerHodgeAudit.lean).

Closed declarations:

- `dense_ad_seeds_not_commute`, on the actual adjoint-endomorphism carrier;
- `dense_zero_partner_kernel_counterexample`;
- `dense_zero_partner_centralizer_lt_kernel`;
- `dense_directional_projection_ne_balanced`;
- `dense_directional_projection_laplacian_ne_zero`.

## 6. Existing architecture to reuse

This table records source inspection. The listed downstream owners are not
automatically included in the new compilation closure.

| Requested layer | Actual existing source and proved interface | Boundary |
| --- | --- | --- |
| Native split Clifford stage | `Clifford/SplitQ11.lean`: `splitQ11`; `Clifford/Tower.lean`: `Clsplit`, `clsplit_succ_equiv` | The successor Clifford equivalence uses the graded tensor product. |
| Represented tensor tower | `Clifford/Cl11TensorTower.lean`: full real matrix stages and injective `stageEmbed` | Its ordinary matrix tensor product is a represented tower; identifying it with another Clifford presentation needs the actual equivalence. |
| Algebraic universal property | `Clifford/Cl11StarAlgebraColimit.lean`: `lift`, `lift_ofStage`, `lift_unique`, `existsUnique_lift`, faithful stage maps | Genuine real star-algebra colimit universal property, before analytic completion. |
| Hilbert completion | `Canonical/FilteredIsometricHilbertCompletion.lean`: `HilbertDirectLimit`, isometric stage maps, `dense_iUnion_range_stageToHilbertDirectLimit` | Uses a positive inner-product directed system and `UniformSpace.Completion`; distinct from C*-completion and von Neumann closure. |
| Krein carrier | `Krein/KreinSpace.lean`: `KreinSpace`, `kreinInner`, `kreinAdjoint`, doubled `WithLp 2 (E × E)` model | Starts from a complete real Hilbert topology and constructs the indefinite pairing through a self-adjoint isometric involution. |
| Cantor inverse limit | `Canonical/UHFInductiveColimitBoundaryInverseLimit.lean`: `prefixDiagram : ℕᵒᵖ ⥤ TopCat`, `prefixConeIsLimit`, `prefixBoundaryLimitIso` | Actual backward-prefix topological limit, separate from forward algebra embeddings. |
| Cantor measure transport | `Canonical/CantorBernoulliL2OperatorTransport.lean`: `prependBit_measure_map_eq_two_restrict_branch` | Exact fair-product-measure identity `map(prependBit b) μC = 2 • μC.restrict(range(prependBit b))`; no identification with the Cartan commutator is supplied by this formula alone. |
| Existing positive matrix kernel theorem | `Canonical/RealLieJordanGeometry.lean`: `ker_symmetricGenerator_eq_centralizer`, `range_symmetricGenerator_eq_centralizer_orthogonal` | Real matrices with transpose-paired generators, via Frobenius positivity, without square-zero assumptions. |
| Existing complex adjoint counterpart | `OperatorAlgebra/PeirceSuperoperators/DoubleCommutator.lean`: `doubleCommutator_ker_eq_centralizer` | A separate matrix/adjoint positivity route. |

In particular, `Canonical/TensorTowerColimit.lean` should not be cited for a
universal property or topology: it proves finite cone compatibility and a
conditional nonvanishing transport statement. The actual universal-property
owners above should be used when that is the required scope.

Pinned Mathlib already has `WStarAlgebra`, concrete `VonNeumannAlgebra`,
and standard-subspace foundations. The inspected
`Analysis/InnerProductSpace/StandardSubspace.lean` explicitly lists Tomita
conjugation, Tomita's theorem, and KMS work as future development. This bounded
source audit does not justify a blanket claim that all von Neumann foundations
are absent, nor does it certify a complete Type-III modular theory.

## 7. Validation record

Independent A-A mathematical/source review passed for the three new owners,
the workflow and the mathematical documentation. A distinct QA-A ran the
maintained exact-source checker afresh: **53 project modules compiled, zero
modules reused**, with **zero warnings in all 11 selected owners**.

The native recursive declaration audit checked **all 160 declarations owned
by the selected modules**, including private/generated helpers. The new
owners contribute 35, 25 and 5 declarations respectively. The only axiom
dependencies reported are `propext`, `Classical.choice` and `Quot.sound`.
This native verification run used neither `--incremental` nor `--skip-audit`.

The three new owners also passed actual `lean -DwarningAsError=true`
checks. Strict OpenGauss screen and refute exited zero with no traps. All 11
static Gate 4 verdicts are `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`; the
separate native audit above supplies kernel evidence. All 11 placeholder
reports each scanned one selected source and found zero issues. YAML parsing,
all five Bash blocks, all three embedded Python blocks and all-target workflow
coverage passed. `actionlint` was unavailable; no full local GitHub expression
or schema validation is claimed.

The additional semantic-vacuity scanner **exited 1** under `--fail-on warning`.
Its complete 11-file scan found exactly two lexical `trivial_surface`/`rfl`
warnings: existing `centralizerProjection_apply` and new `dualSeedGreen_apply`.
Independent A-A review classified both as legitimate `[simp]` definitional
application lemmas used in the substantive projection/Green proofs. No source
repair, suppression, gate edit or result rewrite was made. The raw exit one
and both warnings remain part of the evidence; this gate is not reported as
passing.

The named SOP vacuity linter is regex-based and exited zero on all 11 files.
It retained a score-0.3 `no_hyp_use` signal for existing `dualSeed_trace_zero`.
The proof explicitly uses `h.pd` and `h.dp`; source review classifies the signal
as a cross-line/trailing-space heuristic limitation. That signal is preserved
as well. Root integration is a separate, still-pending scope below.

The unchanged import closure emits 41 warnings:

| Existing imported owner | Warnings |
| --- | ---: |
| `Singular.MoorePenrose` | 14 |
| `Core.PeirceDecomposition` | 1 |
| `Core.JordanPeirceDecomposition` | 2 |
| `Core.JordanAssociator` | 7 |
| `Physics.HestenesKreinOperatorCalculus` | 17 |

An independent read-only identity review compared all 53 live sources and
all 53 QA snapshots against the report, recomputed all dependency
fingerprints, and checked all four verifier hashes. There were no mismatches.
The repository, QA snapshot and installed Mathlib toolchains agree; the
installed Mathlib commit equals the unchanged manifest pin.

The exact new source hashes are:

| Owner | SHA256 |
| --- | --- |
| `Core/DualSeedHodgeOperators.lean` | `90808dd7c750eb80346e6df0eafa7a1aa0c833b24678cae74f20cab0b2af0be6` |
| `Core/DualSeedHodge.lean` | `eed6cff860c3f96f8097619f5d7af2b3e35425e5155dfae1ae1356bbfe794d45` |
| `Canonical/JointCentralizerHodgeAudit.lean` | `dbe0994c4172b22326d85d0ebc0858cc6e43f7b4f478bf8f6438c27dbc3be49e` |

The native report has SHA256
`f19b1895035f22d4fa9a61c00ef0860b4c1cf504c4cb01c75b437a06d8c32b70`;
the raw axiom log has SHA256
`be3f8cc619fdffb2c3086b1886208d92dd1c7cb7b204ec334f41cc0e975b3b1a`.
The earlier author development run used `--incremental --skip-audit` and is
retained as development evidence; it is not the native verification reported above.

The dedicated workflow retains the previous eight owners and adds all three
new owners to path selection, Mathlib-closure hydration, exact-source
compilation, selected-owner warning enforcement, and strict screening.

The completed native verification command was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root .lake/packages/mathlib \
  --lean /home/agent/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  --output scratch/dual-seed-hodge-qa \
  --target InfoGeometry.Core.DualSeedCentralizer \
  --target InfoGeometry.Canonical.JointCentralizerGeometry \
  --target InfoGeometry.Canonical.JointCentralizerGeometryAudit \
  --target InfoGeometry.Canonical.JointCentralizerDynamics \
  --target InfoGeometry.Canonical.JointCentralizerDynamicsAudit \
  --target InfoGeometry.Core.DualSeedTilt \
  --target InfoGeometry.Canonical.JointCentralizerTilt \
  --target InfoGeometry.Canonical.JointCentralizerTiltAudit \
  --target InfoGeometry.Core.DualSeedHodgeOperators \
  --target InfoGeometry.Core.DualSeedHodge \
  --target InfoGeometry.Canonical.JointCentralizerHodgeAudit
```

### Root-package integration and publication gates

At the evidence snapshot, the maintained root-wrapper runner has started
and is waiting for its first file check to acquire the shared build lock.
Later wrapper calls in that serial runner have not executed. The path
`external_refs/homotopy-hypothesis-lean4` is still absent in this checkout.
The prior published head recorded a root build failure at that missing
dependency and two semantic-corpus findings in `Physics/NuclearColimit.lean`.
These are historical root-gate observations; a fresh root build result is not
inferred from them.

The normal installed pre-commit hook passed for local preparation commit
`f644e73b20259bf89ac38892106e61ddd01adaab` (`proof_proxy_staged_gate: ok`).
The native pre-push hook was actually invoked for the exact update from
published parent `11550b59ebd1ac88e8fb54fd1d78afeeefb66894` to that commit.
It passed its initial ref/source checks, classified the three new Lean files,
and requested their locked Lake build at 2026-11-10 16:00 UTC. It is waiting
for the shared lock; no completion or successful root-gate result is claimed.

The subsequent evidence-only documentation update changes no Lean owner,
workflow, dependency pin or verifier. The upstream continuation remains a
draft with outstanding root integration made explicit. Current hook outcomes,
QA disposition and hosted CI are recorded on PR #304.

The source of `Physics/NuclearColimit.lean`, the root Lake configuration,
manifest and toolchain are byte-identical at original main
`732d97c30f292d61ea332ca9da4d1e1d8f69bd00`, published parent
`11550b59ebd1ac88e8fb54fd1d78afeeefb66894`, and this continuation.
The NuclearColimit source has SHA256
`294541eb235d232b4ea132190efdc1dbb2f9a6743bc75d7e8885c4edc41aaf73`
and is outside the 53-module verified source closure.

Native selected-source verification, final QA acceptance, root-package
integration, and source-only inspection of the downstream architecture are separate scopes. Hosted CI and
the final published source identity are recorded on PR #304 after publication.

## 8. Remaining constructions

The forward Clifford algebra colimit, backward Cantor prefix limit, Hilbert
completion, and operator-algebra closure are separate mathematical operations.
Transporting these new operators to or between them requires the corresponding
maps and compatibility laws. The inspected existing owners do not by
themselves identify additive tilt with the Cantor prefix shift.

A Berry connection, braid representation, modular-state/Radon–Nikodym
identification, analytic Hodge theory, and a physical Majorana-protection
theorem require their own objects and hypotheses. Kernel checking of the
algebraic construction establishes the statements above at their exact types.
The explicit formulas do not turn the whole imported library into a
constructive-foundations development; foundational axiom use is audited
separately.
