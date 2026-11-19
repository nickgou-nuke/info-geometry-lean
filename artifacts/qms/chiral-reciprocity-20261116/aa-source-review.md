# A-A source and semantic review: chiral reciprocity

## Disposition and reviewed revision

**PASS for mathematical/source fidelity of the exact snapshots below.** No unresolved semantic correction is required. This is independent A-A review, not QA acceptance, a compilation claim, or permission to report the owners as kernel-verified before their checks complete.

Review date: 2026-11-16. Repository: `/workspace/scratch/9eb3301f34a1/info-geometry-lean`. Observed HEAD: `08c34e03f610b452e03422037949196dc7d92d6d`. The three new owners, the two companion documents, and the three additions to `lean/InfoGeometry/All.lean` were read directly. The source attachment and primary-source audit are separately frozen in `source-audit.md`.

This reviewer authored no Lean source, made no repository edits, and ran no builds, tests, source gates, or remote actions. The commands used were read-only source reads, focused `rg` searches, `git diff HEAD -- lean/InfoGeometry/All.lean`, `git rev-parse HEAD`, and SHA256 hashing. The author reported that the initial compiler lane was waiting for the shared lock; this review does not treat that report as a compiler result.

### Exact SHA256 record

| Reviewed artifact | SHA256 |
|---|---|
| `lean/InfoGeometry/Analysis/HilbertGramReciprocity.lean` | `509d924afe43d1e9420becafd7f9f7b19ae719ecb5b98a8cc641e94cecca90a2` |
| `lean/InfoGeometry/Analysis/HilbertGramMoorePenrose.lean` | `2a218f7f5995df24c075d711ef4a1bac519445ddcae010c3dc3f123058eae7d0` |
| `lean/InfoGeometry/Analysis/GradedExponentialTrace.lean` | `45755d760281cd434c364f8aa7e009c496355839081059b8f51a53ff116c767c` |
| `docs/CHIRAL_RECIPROCITY_CONTRACT.md` | `676d3e9fb0e01a507cc6b79fdf95cedd66ead9dc76bf91dc6c20b43aaeb766b9` |
| `docs/CHIRAL_RECIPROCITY_FORMALIZATION.md` | `90d13097a19342fb78ed88e0d8db8b0ef545ede3b281885bf9ab95ef891c1e8f` |
| `lean/InfoGeometry/All.lean` | `5bd6c78068eab621d0ba45fc64a5f1da9ba7172295a2ab3fddf69a469537d09f` |

The source-level inventory is **20 theorem declarations and one definition**: HilbertGramReciprocity has five theorems and the isometric-equivalence definition; HilbertGramMoorePenrose has seven theorems; GradedExponentialTrace has eight theorems. This count excludes compiler-generated declarations and is not an axiom-audit declaration count.

## 1. HilbertGramReciprocity

**PASS.** Actual carrier: arbitrary complete `RCLike` Hilbert spaces and bounded continuous linear maps between them, with no dimension equality or finite-dimensionality assumption.

* **Lines 43–72:** The positivity statements use `Module.End.HasEigenvalue`, extract its nonzero eigenvector, and divide by its nonzero squared norm. The reality equation explicitly embeds `RCLike.re μ` back into the scalar field. Strict positivity uses both the actual eigenvalue witness and `μ≠0`. A scalar alone, or the zero vector in an eigenspace, cannot satisfy the missing witness condition.
* **Lines 77–105:** `normalizedGramEigenspaceEquiv` constructs a native `LinearIsometryEquiv`. It reuses `HilbertGramDuality.gramEigenspaceEquiv`, composes with native scalar multiplication by a proved nonzero scalar, and proves inner-product preservation. The real normalization coefficient is fixed by conjugation, so the complex inner-product convention is handled correctly. Norm preservation is derived, not supplied as a theorem premise or an arbitrary structure field.
* **Lines 110–144:** The forward, inverse, and adjoint-exchange readouts match the construction. In particular, the inverse is `A†/sqrt r`, not `A†/r`, because the unnormalized inverse and the inverse of the forward normalization combine. The adjoint-exchange statement explicitly transports membership using `adjoint_adjoint` rather than identifying two subtypes without justification.

The positive-parameter construction also covers a zero eigenspace; this is legitimate and is not used to assert existence of an eigenvector. The construction is nonvacuous, for example for an identity operator at eigenvalue one. Its scope excludes a global inverse and any assertion of a complete spectral decomposition, as the module documentation states.

The short readout proofs are legitimate consequences of an actual constructed equivalence. They should not be classified as proof holes or vacuous existence wrappers merely because the forward action is definitionally equal to its displayed formula.

## 2. HilbertGramMoorePenrose

**PASS.** Operator order and source/target spaces are retained throughout.

* **Lines 42–52:** `comp_adjoint_eq_of_inner_inverse` genuinely derives `BAA†=A†` from `ABA=A` and self-adjointness of `BA`. Taking adjoints reverses the multiplication order; the subsequent rewrite uses exactly the assumed self-adjointness. The other two Penrose equations are not smuggled into this minimal lemma.
* **Lines 57–83:** The arbitrary Moore–Penrose-pair theorem consumes the existing four-equation predicate and derives its reciprocal eigenspace action. The closed-range specialization then consumes the existing constructed `moorePenroseInverse`, together with its proved Penrose laws. It does not replace construction by an existential or a user-supplied desired conclusion.
* **Lines 87–120:** The normalized inverse identity has the correct square-root direction: `U⁻¹ y = sqrt r • B y`. The norm formula follows from the actual isometry and the positivity of `sqrt r`; zero vectors remain allowed.
* **Lines 125–146:** The quantitative inequality `1≤r‖B‖²` requires an actual nonzero eigenvector. Its positive norm, rather than a possibly zero operator norm, is cancelled. Squaring the resulting bound preserves direction because the quantities are nonnegative.
* **Lines 151–165:** The small-positive-eigenvalue premise quantifies over every positive epsilon and includes an actual `HasEigenvalue` witness. Under a contrary closed-range premise, the existing bounded inverse is constructed and epsilon `1/(‖B‖²+1)` produces the contradiction. This proof covers `B=0` without dividing by its norm.

The final premise is not intrinsically contradictory: a bounded diagonal map with entries `1/n` on `ℓ²` has target Gram eigenvalues `1/n²` and nonclosed range. This example is a mathematical nonvacuity check, not a new Lean theorem in the package. The source correctly describes a one-way point-spectrum criterion and does not claim its converse, an eigenbasis, a Fredholm theorem, or an extra spectral point at infinity.

The reused Moore–Penrose owner was read directly at its predicate, kernel-complement restriction, continuous equivalence, bounded inverse definition, and four-equation proof. The companion report's description of that construction matches these sources.

## 3. GradedExponentialTrace

**PASS.** The general trace statements preserve noncommutative multiplication; the finite matrix results are specializations, not replacements for the general statements.

* **Lines 47–66:** Positive powers vanish by applying the existing `gradedTrace_odd_square_eq_zero` to the weight `G(D²)^k`. The source proves that this weight still anticommutes with `D`. Characteristic zero of the target field supplies the required absence of additive two-torsion. No involution or star hypothesis is hidden in the reused owner.
* **Lines 70–73:** Only `E²=0` is needed for `E` to commute with `EF+FE`. The arbitrary partner `F` is not assumed square-zero. This is a valid strengthening of the original two-square-zero contract.
* **Lines 84–106:** The generic analytic theorem uses `NormedRing`, `NormedAlgebra`, and completeness, an actual continuous linear functional, explicit cyclicity, and explicit anticommutation. It composes the functional with continuous left multiplication by `G`, transports a native `HasSum` for `NormedSpace.exp`, and proves termwise that only degree zero remains. The limit is therefore the actual exponential, not a formal-series symbol or an unchecked totalized sum. The right side correctly retains `τ G`.
* **Lines 110–117:** The weighted commutator theorem needs only an additive cyclic functional, because it uses exponential commutation followed by finite algebraic cancellation. Continuity of this functional is not used to interchange a sum. The order is handled correctly by an initial cyclic permutation and then the existing graded-commutator theorem with the exponential as the commuting weight.
* **Lines 131–155:** Actual two-block exponential transport is derived from convergent matrix series and native diagonal-block powers. The degree-zero term and both off-diagonal zero blocks are included. No diagonalization of the block entries is assumed.
* **Lines 160–183:** The rectangular theorem forms the actual doubled `D` and signed block `G`, proves their anticommutation and `D²=diag(AB,BA)`, supplies the continuous native matrix trace, and specializes the general analytic theorem. The output dimension defect has the correct sign and scalar casts. Empty index types are retained by the stated finite-type assumptions; no `Nonempty` premise appears.
* **Lines 187–215:** The matrix cancellation is a direct specialization of the general theorem. The explicit `2×2` witness proves noncommutation, both square-zero equations, trace one against the separate weight `EF`, and zero trace against the anticommutator exponential for every parameter. It does **not** prove the different claim that an unrelated exponential regulator has nonzero trace. The docstring and companion report preserve this distinction.

The generic analytic theorem does not assume `G²=1`, self-adjointness, positivity, or a constructed ordinary trace on all bounded Hilbert operators. Those omissions are mathematically valid and are stated explicitly in the report. A nonzero constant is possible: rectangular partners with dimensions two and one, `A=(1,0)ᵀ`, `B=(1,0)`, have exponential trace difference one with nonzero doubled operator. Thus the theorem is not merely cancellation of an assumed zero functional or zero operator.

The pinned Mathlib exponential-series, block-power, matrix norm, and projectivization sources were inspected as relevant. The source does not rely on a new custom algebra, trace structure, generalized-inverse definition, or index object.

## 4. Documentation, provenance, and integration

**PASS after the two status-wording corrections below.** The contract/report match the actual owners and distinguish constructed results, supplied premises, existing results, explanatory calculations, and open analytic claims.

The reviewed report correctly states:

* real positivity is inferred from an actual eigenvalue witness;
* the normalized equivalence acts on actual native eigenspaces, including arbitrary ambient Hilbert spaces;
* closed range supplies the previously constructed Moore–Penrose map;
* point-spectrum accumulation is sufficient for nonclosed range, with no converse claimed;
* the Banach-algebra trace is supplied as continuous and cyclic;
* one square-zero factor is sufficient for commutator cancellation, and that cancellation only needs additivity/cyclicity of the functional;
* the separate finite weight is `EF`, not an asserted unrelated exponential;
* matrix lift order, projective order, support corners, Drazin inverse, Moore–Penrose inverse, Fredholm index, eta, and regularized non-Fredholm indices are distinct;
* primary-source discussion does not itself certify a Lean theorem;
* selected-module checks cannot certify the repository's root build.

Existing-owner references were checked against their actual declarations, including the nilpotent MP/Drazin obstruction and criteria, partner generalized eigenspaces and shifted powers, the fixed-scalar chiral normalization, paired zero-supercharge index, polynomial supertrace, conditional spectral sums, and native projective scalar-kernel behavior. The documented import distinction is accurate: the historical polynomial owner reaches `SpinorialCore.Algebra`, whose first import is `Mathlib`; the new owner instead imports the generic cyclic-trace owner and focused native analytic/matrix modules. This is not a claim that every historical module currently compiles.

`git diff HEAD -- lean/InfoGeometry/All.lean` shows exactly the three requested import additions, with no other change in that file.

### Nonconformance and closure record

| ID | Evidence at initial review | Requested action | Closure |
|---|---|---|---|
| DOC-1 | Formalization report line 287 initially said “new checked declarations” while validation was pending. | Use source-level language until kernel checking is complete. | Author changed it to “new source declarations”; directly reread. |
| DOC-2 | Initial final paragraph described acceptance as established by checks “recorded above,” although the record was pending. | State the check requirement conditionally. | Author changed it to “Lean acceptance requires the separate source-closure and axiom checks specified above”; directly reread. |

Both corrections are included in report hash `90d13097a19342fb78ed88e0d8db8b0ef545ede3b281885bf9ab95ef891c1e8f`. All three Lean source hashes remained unchanged during this review. There are no outstanding mathematical/source change requests for these snapshots.

## 5. Remaining acceptance work

The separate compiler and QA lanes must establish elaboration, selected source-closure compilation, axiom dependencies, warnings, strict source-gate results, and installed-hook results. This review does not predict that every tactic elaborates successfully; any proof repair must preserve the reviewed theorem types and mathematical content. Subsequent source changes require a hash-specific delta review. Validation-record-only documentation updates may record actual results without reopening the unchanged mathematics.

Final A-A disposition: **PASS — exact source semantics and documentation fidelity, with compiler and QA acceptance still pending.**
