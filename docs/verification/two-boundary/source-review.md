# Independent A-A review: two-boundary operator geometry

**Verdict: PASS for the exact source and verification-tool scope below.** No further source changes are requested by this review. This is a mathematical, architectural, and verification-tool source review; it is not a substitute for the separate native declaration audit or independent QA execution. The ordinary root Lake integration path remains blocked by the recorded path-package preflight described below.

- Reviewer: `repository_scout`, independent A-A lane.
- Reviewed at: `2026-11-09T09:06:34.720698+00:00`.
- Repository: `/workspace/scratch/ec4ca3191aef/info-geometry-lean`.
- Branch: `feat/two-boundary-operator-geometry`.
- Base and current HEAD: `cfbcbca21cf57a4614a9646768ba9356cf3cc6b0`.
- Frozen scope: 26 staged paths; every staged path was byte-identical to its worktree copy when this report was generated.
- Mathematical scope: five new owners and four promoted or repaired owners; all nine owner pairs are byte-identical between `lean/` and `src/`. Both `AllExhaustive.lean` files are byte-identical as well.
- Auditor actions: source and diff reads, declaration and hypothesis inspection, byte comparisons, and SHA256 calculation. The auditor did not edit any theorem or verification implementation, run Lean, compile a module, run tests, invoke a gate, or publish anything. Writing this report and preserving its earlier version are the only artifact creations in this final review.

This refreshed review supersedes the preceding source manifest, preserved byte-for-byte as `two-boundary-aa-review-before-type-value.md`, SHA256 `6422c8cb404a5534c6a4592c80528ea040468574206100526417e0554ad9f6dd`. The original before-foldr report also remains preserved as `two-boundary-aa-review-before-foldr.md`, SHA256 `a09a6bd2821787cfaa6f069f9722157c436c0c5ef7142db4952d84b044244a9e`. Both are historical and do not certify the latest changed sources.

## 1. Mathematical findings

### BoundaryInstrument

The carrier remains arbitrary finite full complex matrices. An outcome can contain an arbitrary finite internal Kraus family. The amplitude is ordered as `sqrt E * K * sqrt ρ`; its Gram trace gives the stated branch weight. Positivity and the exact zero/nonzero support criteria use positive-semidefinite boundary hypotheses. The positive-normalizer criterion is an actual existence statement for a nonzero amplitude, including the correct behavior for empty finite index types.

The totalized quotient is not silently claimed to be a normalized distribution at zero denominator: the sum-one theorem requires a positive normalizer. The upper bound on the normalizer uses a trace-one positive input, Kraus completeness, and the one-sided effect bound `(1 - E).PosSemidef`; nonnegativity is a separate result requiring positivity of `E`.

The disturbance identity compares the instrument normalizer with the bare overlap through the Heisenberg defect, with all factors in their original operator order. A fixed backward effect is a sufficient equality condition; no unjustified converse is asserted. The completeness-based commutator formula is ordered correctly. Instrument composition places the later Kraus operator on the left. No scalarization or ambient commutativity premise replaces these identities.

### MixedBoundaryReadout

The readout is `tr(E * A * ρ) / tr(E * ρ)`, and its representing ordered matrix is `tr(E * ρ)⁻¹ • (ρ * E)`. The product orientation is essential and is correct. Complex linearity and the pure-boundary reduction reuse the existing native matrix/vector and weak-functional owners.

The normalization result and the Hermiticity equivalence explicitly require a nonzero overlap. The exact adjoint defect depends on the commutator of the boundaries, and the theorem identifying Hermiticity of the normalized product with boundary commutation also requires Hermitian boundaries. No positivity or reality of a general weak readout is claimed. The pure-state theorem is tied to the existing `RegularBoundaryPair` nonzero-overlap invariant rather than a new assumed witness.

### MatrixBoundaryPurification

The rectangular amplitude is vectorized as `vec Sᵀ`, fixing the row-first index convention. Its outer product has second-factor partial trace exactly `S * Sᴴ`; it is not accidentally the transposed or opposite marginal. The norm theorem uses native `EuclideanSpace` and `WithLp` with exponent two. The final `sq_eq_sq₀` proof extracts norm one from its squared value using norm nonnegativity; it does not change the statement or add a mathematical assumption.

The CFC square root constructs a purification for each positive matrix. Trace-one hypotheses are explicit for the normalized vector and idempotent density. The Gibbs density is explicitly trace-normalized, and the trace-one theorem has the necessary nonempty index hypothesis. The existential Gibbs purification supplies a concrete outer-product witness and proves positivity, trace one, idempotence, and the exact marginal.

The doubled generator uses the correct right-factor transpose: `(H ⊗ 1 - 1 ⊗ Hᵀ) vec Sᵀ = vec (H*S - S*H)ᵀ`. Vanishing for the Gibbs square-root amplitude follows from CFC commutation. This is a derived special property of that amplitude, not a restriction of the ambient full matrix algebra to commuting matrices. The source does not claim general dynamics, thermalization, entanglement generation, or a physical interpretation of doubled sectors.

### SemilinearBoundaryReversal

The construction reuses the existing real algebra equivalence `sheetConj`. It conjugates complex scalars, preserves the order of multiplication, and is compatible with adjoints. The reversed family is `τ(K*)`, with boundary interchange. The forward/backward weight identities use trace cyclicity and real-part invariance under conjugation with the correct orientations.

The reversed completeness theorem does not confuse trace preservation and unitality: reverse trace preservation is equivalent to the original family being unital. The new `forwardWord_reverse_adjoint` reverses the chronological list and adjoints each family. The new `reversed_word_weight` combines that complete chronological reversal with `sheetConj` and endpoint interchange; it is stronger than an entrywise conjugation identity and implements the stated word-level reversal.

The mixed-readout conjugation and endpoint-swap statements preserve their required Hermitian hypotheses. No stronger antiunitary Hilbert-space theorem or physical CPT theorem is inferred from the real algebra equivalence.

### TwoBoundaryOperatorExamples

The example boundaries are dense positive Hermitian 2-by-2 matrices; the effect complement is also positive. The two Kraus matrices are dense and complete. Separate exact theorems establish failure of commutation for the boundaries and for the Kraus operators. The examples therefore exercise genuine operator order.

The exact conclusions are consistent with the general statements: bare overlap `4/9`, instrument normalizer `7/18`, weak readout `(3-i)/4` for a Hermitian probe, and temporal-order weights `5/72` and `1/8`. Positivity is established by explicit matrix Gram factorizations, and the arithmetic proofs evaluate matrix entries without introducing a diagonal or commuting model.

## 2. Owner reuse, baseline repairs, and integration

The canonical real-weight unitary-mixture declaration is synchronized with the already-existing `src` spelling `unitaryMixtureChannel_real`, avoiding its collision with the imported complex-weight declaration. The corrected prose acknowledges unrestricted real coefficients. The theorem's conclusion is exactly unitality and trace preservation; this review does not infer complete positivity for arbitrary signed weights from its historical name.

`FinitePartialTrace` is promoted as a focused existing owner. Its original namespace is retained, while the duplicated declarations are removed from `FiniteAttentionCanonicalBridges` and replaced with an import, preserving consumer names. The finite-attention proof edit removes unused simp arguments; its mathematical statement is unchanged. The comment now states the real quadratic-form convention without the inaccurate blanket assertion that complex numbers have no order structure.

The final revision also strengthens `diagonalFiniteDensity_partialTrace` to accept only the arbitrary real array `p`, removing its unused positivity and normalization assumptions. The identity follows directly from the existing complex-valued `partialTraceSecondOp_diagonal`, with the real-to-complex sum coercion discharged by simplification. It is an unconditional algebraic marginal identity, and no probability-state conclusion is added. The tracked-source consumer search found only its defining copies. Byte reconstruction against the preceding hash confirms this lemma block is the only subsequent change in the finite-attention source. Both source lanes match.

`SemilinearSheetGeometry` is promoted unchanged from its existing `src` source. The seven required module imports are registered in both exhaustive entry points. No unrelated root package, assumption, or alternate carrier is added to make the focused sources compile. All nine audited owner pairs and both entry-point mirrors match byte for byte.

### Reviewed foldr repair after the first native audit

The parent reported that the first combined native audit correctly stopped on the preexisting generated `InfoGeometry.Quantum.Choi.backwardWord._unsafe_rec` declaration. No native PASS was produced for that attempt. The local recursive word implementations were replaced by the existing native `List.foldr`. At that repair stage, the strict declaration-audit source, axiom policy, and checker were unchanged. The later dependency-extraction correction is reviewed below; the axiom and safety policies remain unchanged.

The forward folding step is `fun V next => next.comp (krausMap V)`, and the backward step is `fun V next => (krausMap (fun i => star (V i))).comp next`. These preserve the exact original chronological application and reverse pullback. Four named `[simp]` nil/cons equations are proved by `rfl`. They expose the definitional interface instead of recreating recursive executable companions. The append proofs use the corresponding cons equations. The only change to `SemilinearBoundaryReversal` is replacing the definition-unfolding simp entry with `Choi.forwardWord_cons`; byte reconstruction against the previous source hash confirmed that it is the sole change in that file.

A tracked Lean-source search found no consumers of `forwardWord.eq_*`, `backwardWord.eq_*`, or either generated `_unsafe_rec`. The existing `KrausInvariantGeometry.backwardWord_eq_of_mem_invariantOperators` remains an unchanged consumer. Its nil and cons proof steps use the same definitional reductions. The parent reports that both the revised owner and this unchanged consumer have compiled in the new run; the auditor did not run that compilation. The updated contract correctly records the native-fold rationale and the inclusion of this consumer in the validation closure.

The exact source delta is accepted. Whether every owned generated declaration now satisfies the unchanged audit must be established by the rerun; removal of the runtime companion is not inferred solely from this source review. At the foldr repair stage, only five staged paths changed from the original report: the two word-owner copies, the two semilinear-reversal copies, and the contract. The subsequent final delta is separately recorded below.

## 3. Native audit and checker source review

The native audit enumerates constants by actual defining module from the Lean environment, including private and generated constants. Its nine-owner list is explicit, and every owner must be imported and nonempty. Unsafe declarations, partial definitions, local axioms, and dependencies on axioms outside `propext`, `Classical.choice`, and `Quot.sound` are rejected. Type/value dependency edges are now computed explicitly as the union of `info.type.getUsedConstantsAsSet` and the constants of `info.value? (allowOpaque := true)`, with an empty value contribution when no value exists. The latter option includes theorem and opaque proof values.

The pinned Lean `Lean/Util/FoldConsts.lean` implementation was inspected directly. Its broader `ConstantInfo.getUsedConstantsAsSet` helper adds inductive-constructor metadata, a constructor self-name, and recursor metadata when no value is present. Those are not the declared syntactic type/value edges. The explicit expression-level union implements that documented scope; it does not filter actual expression self-references after collection. No declaration is omitted from enumeration, and the separate transitive axiom and safety checks are unchanged. Byte reconstruction confirms this extraction block is the only change in the native audit source. The maintained graph consumer and Python exact-edge validator are unchanged. This graph must not be presented as a complete graph of all kernel reduction dependencies.

The contract now states this metadata exclusion and distinguishes it from the all-owned-declaration safety and axiom audit. This is a scope correction in graph extraction, not a weakened axiom policy or a gate bypass. The only four staged paths changed since the preceding report are the contract, both finite-attention copies, and the native audit source. All remaining staged hashes are unchanged.

The Python validator requires the exact requested module scope, a unique final PASS summary, a matching declaration count, unique declaration names, recognized declaration kinds, safe/nonpartial records, the exact allowed-axiom policy, and a consistent explicit empty-module policy. Owned dependency edges must equal the intersection of all emitted dependencies with audited declaration names; omitted owned edges are rejected as well as unknown ones.

The checker now rejects `--audit-source` without `--audit`. Explicit or strict owner scopes fail if an owner is not present in the compiled closure. Strict warning handling applies both to selected owner recompilation and to the audit itself. The source lane is recorded and isolated, with original and staged source hashes checked after execution. The receipt distinguishes requested, compiled, and audited scopes. These changes close the concrete earlier scope and validation findings without granting a verification exemption.

The review inspected the new regression tests as source. Their assertions cover module mismatch, duplicate/missing records, empty-module policy, unsupported/missing declaration kinds, unsafe/partial/axiom cases, and missing or unresolved dependency edges. The parent reports 35 selected parser, pre-push, and routing tests passed; this A-A report does not independently reproduce that execution.

## 4. Gate and pre-push source review

The post-build gate routes changed `src` Lean owners through `run_locked_lake_build.py --source-lane`, and source deletion or `lakefile.src.lean` changes through the source entry point. Changed source files also participate in semantic and axiom-debt auditing. The custom `TwoBoundaryDeclarationAudit.lean` is explicitly routed through the same locked native Lean route as the prior supported audit. Failure propagation remains nonzero; unrecognized Lean paths are not silently exempted.

The pre-push source guards now include `src`, `lakefile.src.lean`, and `lean-toolchain`, retaining the pushed-HEAD, tracked/untracked-source, and worktree checks. No hook bypass or approval bypass is introduced. The routing tests deliberately use a subprocess recorder: they establish command routing, not native Lean verification. That distinction is explicit and must remain explicit in the final evidence.

## 5. Evidence boundary and root Lake blocker

The parent reported a successful 284-declaration audit across all nine owners and compilation of 31 project modules, including the invariant-word consumer, at the preceding hashes. Those earlier results do not certify the latest finite-attention and audit-source changes. At this source-review refresh, the staged gate, native rerun, and independent QA acceptance for the revised bytes remain separate and pending; no result from the earlier hashes is silently transferred.

This source review accepts the mathematical statements and implementation scope at the hashes below. Native candidate compilation and the combined nine-owner audit are separate parent/QA responsibilities. A completed native receipt and independent QA result must be bound to these same source bytes before a final kernel-verified claim is made. This report does not claim a successful root `lake build`, successful ordinary pre-push gate, successful complete-repository build, or successful CI run.

The existing `verification-runtime/root-path-preflight.json` is for base `cfbcbca21cf57a4614a9646768ba9356cf3cc6b0` and reports `ok: false`. `HomotopyHypothesis` and `Atlas` have missing untracked path-package directories/configuration. `GIFT` is an uninitialized gitlink with missing package configuration, pinned at `e6f3c3ac2140c2324fb2ae029c32233e73aa5e92`. `InfoGeometryCore` is available. This preflight is a path-package availability/provenance check, not a compilation or transitive dependency audit.

Those recorded conditions block a claim of ordinary root Lake integration. A successful isolated native closure using the real repository sources and pinned Mathlib establishes that scoped result only. The reviewed gate changes preserve the ordinary gate; this PASS supplies no authorization to bypass it or to characterize the path-package blocker as resolved.

The contract carefully bounds the extraction to finite-dimensional operator mathematics. It does not claim to prove cosmological hypotheses or identify a direct sum with a tensor product. Its proposed dependency graph concerns formal declaration dependencies, not physical causation. Bibliographic provenance is recorded by the parent; this A-A source review does not independently authenticate the source PDF.

## 6. Exact SHA256 manifest

All paths below are relative to the repository root. Hashes are of the staged bytes, independently compared with the worktree copies during report generation. Any change to a listed source invalidates the corresponding exact-source acceptance until reviewed again.

| Staged path | SHA256 |
| --- | --- |
| `.githooks/pre-push` | `5ea58fd402899bf7e8c04f26158146dd429485fab636367fd6671df207dfbaaf` |
| `docs/TWO_BOUNDARY_OPERATOR_CONTRACT.md` | `e19d92030a6537c2ea45525a16b3c4cfac08688fd6d86b50b03d6e67ba32247e` |
| `lean/InfoGeometry/AllExhaustive.lean` | `59769bb22e6f3d814588b7322ef64d408b681fafaf0473b7bc2ea1576b6d6af7` |
| `lean/InfoGeometry/OperatorAlgebra/SemilinearSheetGeometry.lean` | `a4154cd1c50d7c7d7207b5fe692cefcf5ff76ab50ab37fc5b86fbfcb40689aaa` |
| `lean/InfoGeometry/Quantum/BoundaryInstrument.lean` | `33a1f8604ef1755adab2cee9a16321296c1a8fcb6673e5b40b5b95df5aa5db15` |
| `lean/InfoGeometry/Quantum/FiniteAttentionCanonicalBridges.lean` | `fe181c5428136dd0b86cb2676115f7a0dd149b561e6277c8ffdc4c4ca8cd0592` |
| `lean/InfoGeometry/Quantum/FinitePartialTrace.lean` | `bfb3db143b95aee547e5241d2f854bc2cfcd964c116afd89817726d54a52d7c1` |
| `lean/InfoGeometry/Quantum/KrausBoundaryDuality.lean` | `374742918777bd4f507de8809c3e2fc42eea4200e4f04379cc03ec81ff9e2bf4` |
| `lean/InfoGeometry/Quantum/MatrixBoundaryPurification.lean` | `3414dabfa40cc746d6511c4a9d57b0986228044bcf6eff73d13fcd06f85af7e1` |
| `lean/InfoGeometry/Quantum/MixedBoundaryReadout.lean` | `3708e31d8f41bc14b957e357c768101d5e5dc0b96c383d892bba09c69b72a600` |
| `lean/InfoGeometry/Quantum/SemilinearBoundaryReversal.lean` | `972734ce15376f0458db8598615f9f57fa117ab0df152b575c06404d113b52a1` |
| `lean/InfoGeometry/Quantum/TwoBoundaryOperatorExamples.lean` | `c3f603ad869f59dd7f35444df1c03f3373a298f0c159097a85e9d32064737252` |
| `scripts/quality/post_build_gate.sh` | `548ecf9d42268fbef3a4a89b5c90834568a7e9c5ad046d78bf78a6bfce7bcf8a` |
| `src/InfoGeometry/AllExhaustive.lean` | `59769bb22e6f3d814588b7322ef64d408b681fafaf0473b7bc2ea1576b6d6af7` |
| `src/InfoGeometry/Quantum/BoundaryInstrument.lean` | `33a1f8604ef1755adab2cee9a16321296c1a8fcb6673e5b40b5b95df5aa5db15` |
| `src/InfoGeometry/Quantum/FiniteAttentionCanonicalBridges.lean` | `fe181c5428136dd0b86cb2676115f7a0dd149b561e6277c8ffdc4c4ca8cd0592` |
| `src/InfoGeometry/Quantum/FinitePartialTrace.lean` | `bfb3db143b95aee547e5241d2f854bc2cfcd964c116afd89817726d54a52d7c1` |
| `src/InfoGeometry/Quantum/KrausBoundaryDuality.lean` | `374742918777bd4f507de8809c3e2fc42eea4200e4f04379cc03ec81ff9e2bf4` |
| `src/InfoGeometry/Quantum/MatrixBoundaryPurification.lean` | `3414dabfa40cc746d6511c4a9d57b0986228044bcf6eff73d13fcd06f85af7e1` |
| `src/InfoGeometry/Quantum/MixedBoundaryReadout.lean` | `3708e31d8f41bc14b957e357c768101d5e5dc0b96c383d892bba09c69b72a600` |
| `src/InfoGeometry/Quantum/SemilinearBoundaryReversal.lean` | `972734ce15376f0458db8598615f9f57fa117ab0df152b575c06404d113b52a1` |
| `src/InfoGeometry/Quantum/TwoBoundaryOperatorExamples.lean` | `c3f603ad869f59dd7f35444df1c03f3373a298f0c159097a85e9d32064737252` |
| `tests/quality/test_two_boundary_gate_routing.py` | `6ac0fd80f0add086ea020e91f5da46106a2efe0e68160fc0ea606b0a1299cc73` |
| `tests/test_operator_geometry_audit_scope.py` | `dcb77659d5b1e793de40ae287284f01f8848f7026c64aa8794f3efb9ec124744` |
| `tools/quality/TwoBoundaryDeclarationAudit.lean` | `8c274f1935e96955474444b359f575d5ab8b13f0dc0f1a6c14767753b5ccbb7c` |
| `tools/quality/check_operator_geometry.py` | `2e3a78cb576936ca16951108a90ceed22934cad35a38b243fe53eff415512495` |

The unchanged preexisting mirror `src/InfoGeometry/OperatorAlgebra/SemilinearSheetGeometry.lean` has SHA256 `a4154cd1c50d7c7d7207b5fe692cefcf5ff76ab50ab37fc5b86fbfcb40689aaa` and is identical to its staged canonical promotion. It is not one of the 26 changed paths.

The consulted root preflight record has SHA256 `6dd6f66260edc9c21b20fe4a263c12a1574c4f7be5b4c97c350eafb013de964b`. Its scope and failure are reported above rather than converted into a compilation claim.

**Final disposition:** no outstanding mathematical or tooling source correction is requested for this frozen scope. Source A-A PASS; separate exact-source native/QA acceptance and the unresolved ordinary root Lake integration limitation must remain visible in subsequent reporting.
