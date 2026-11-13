# Knutsen localization: independent review and acceptance

Reviewer: `/root/knutsen_independent_review`. The reviewer did not author or
modify the mathematical owner files.

Reviewed checkout:
`/workspace/scratch/d18a558d1d7d/knutsen-localization-lean`.
Base revision: `a392af178af1fe2bcba2ba39eb405700c6ee103c`.
Input SHA256:
`bd31543386a90075f8bea22af36bdc630983313f5148eb6e2de6f2bfdfdb7db0`.
The seven mathematical sources were frozen from the existing exact-input
candidate checkout; the original active checkout was left untouched.

## Source review

The seven new mathematical owners were reviewed together with the exact
declarations reused from `Core.PeirceCompressionDefect`,
`Core.PeirceCompressionCStar`, `Algebra.NonCommutativeIsometry`,
`OperatorAlgebra.NoncommutativeKrausChannel`, and `Clifford.OperatorValuedJones`.
The initial frozen source hashes agreed with the separately captured candidate
receipt. The later three-file API/proof repair is separately reviewed and
fingerprinted in `repaired-source-review.json`, at local source checkpoint
`26c53a3a`. These repairs preserve all operator and analytic theorem statements;
the Weyl window equality also drops an unused star-ring instance assumption.

| Owner | Mathematical review |
| --- | --- |
| `OperatorAlgebra.ProjectionLocalization` | Native star projections, complementary Gram conservation, leakage and commutator variance preserve coefficient order. Positivity uses native star-order hypotheses; norm and faithful-vanishing claims use C-star hypotheses. |
| `OperatorAlgebra.IsometryCornerLocalization` | Constructs an actual non-unital star-ring homomorphism, proves injectivity, and gives an explicit ring equivalence onto the native idempotent corner. Intertwining, complement partitions, positive-power transport, all-power pullback, norm transport, and projection-preservation criterion have the stated scope. |
| `OperatorAlgebra.FiniteOperatorFrame` | Rectangular matrices retain both index types and arbitrary noncommutative star-ring coefficients. Multiplier, Gram-power, star, trace, and Parseval claims are genuine algebraic identities. The one-row comparison connects to the existing Kraus owner. |
| `Clifford.WeylFrameMasks` | Reuses the Jones matrices with the attachment's fourth-generator sign. Explicit full, balanced, parallel, and singleton masks prove finite identities; the same-cardinality witness exposes the missing geometric/analytic implication. |
| `Analysis.PorosityIteration` | The real geometric-loss recurrence, finite sum, closed form, monotone loss, uniform bounds, and retained-fraction estimates are mathematically correct, with appropriate unit-interval and positive-dimension hypotheses. |
| `Analysis.MetricPorosity` | Uses genuine disjoint metric balls and positive scales. Thickening shrinks holes by the explicit radius loss. The recurrence bridge uses one thickness and does not presume equality of iterated thickenings in arbitrary pseudometric spaces. |
| `Analysis.MultiscaleLocalization` | The one-step energy estimate and terminal bound remain explicit assumptions. Ordered list products preserve multiplication order, and the empty-product norm uses `NormOneClass`. Strict contraction requires a positive-length list and strict factor bounds. |

No false target, vacuous substitute, local theorem axiom, or hidden conclusion
field was found in this source review. The constructions have ordinary
nontrivial instances: matrix star rings for the finite algebra, native C-star
operator algebras for norm statements, and real metric spaces for the porosity
statements. The seven source files contain no textual proof holes, unsafe proof
bypasses, or custom axiom declarations.

## Interpretation and coverage

The original attachment's omitted algebraic consequences are present:
range-corner complement partition, powers, Gram self-adjointness/trace, and the
uniform retained-fraction inequality. The implementation also supplies explicit
corner equivalence, rectangular transport, metric thickening, and conditional
multiscale estimates.

The following boundaries are correct and must remain in publication claims:

- `star v * v = 1` is a one-sided isometry assumption.
- The generic finite Gram identity is not Knutsen's Lemma 5.2.
- A star square alone does not provide an order or a faithful involution.
- Four indexed Weyl labels need not be distinct in characteristic two.
- The coefficient-diagonal twirl output need not be central.
- A finite mask does not establish metric porosity or an analytic FUP exponent.
- Real recurrence estimates do not prove the one-step Fock sampling inequality.
- Gaussian STFT/Bargmann transforms, Fock subaveraging, the geometric-to-energy
  implication, and lattice-cell estimates remain open analytic obligations.


The final source checkpoint is `0149b1f0a017b423d318b54e84662a7e6dd32022`. Its one-keyword recurrence repair is separately recorded in `noncomputable-source-review.json`. All seven final source hashes match both the fresh accepted CI run and the completed local strict static scans.

## Verification design and native acceptance

The accepted native evidence is **fresh GitHub Actions execution**, independently
reconciled against this checkout. The maintained
`tools/quality/check_clifford_dirac.py` freshly elaborated all 16 selected
repository modules and executed the native transitive axiom audit. All module
return codes were zero and every `reused` field was false. Pinned Mathlib
artifacts were used; this is not a claim that Mathlib itself was rebuilt.

- Run: `43383097703`; job: `131745210917`, completed successfully.
- Published source head: `3f7282ceb5076e16bae8acc696adffd3771494c9`.
- Tested merge commit: `8e9221d29001ebe80558237992ce9be8a35920af`.
- Artifact: `14017786847`, `knutsen-localization-evidence`.
- Artifact ZIP SHA256:
  `848fa6c5663cf19fbc48a5570ac3bf40ce0d1441f49ab5bdfd5162fc667b91d3`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The reviewer independently fetched completed run/job metadata and the raw job
log; checked the ZIP against the GitHub artifact digest; matched all 16 source
hashes and all four verifier-source hashes to the current checkout; verified
the 23 evidence-checksum entries; reconstructed the selected repository import
closure; and compared the generated native audit source byte-for-byte with the
maintained generator. The raw log contains 490 distinct audited declarations
and a positive count for each selected module. Its only foundational axioms
are `propext`, `Classical.choice`, and `Quot.sound`.

| New owner | Native audited declarations | Compiler warnings |
| --- | ---: | ---: |
| `OperatorAlgebra.ProjectionLocalization` | 11 | 0 |
| `OperatorAlgebra.IsometryCornerLocalization` | 44 | 0 |
| `OperatorAlgebra.FiniteOperatorFrame` | 31 | 0 |
| `Clifford.WeylFrameMasks` | 31 | 0 |
| `Analysis.PorosityIteration` | 21 | 0 |
| `Analysis.MetricPorosity` | 11 | 0 |
| `Analysis.MultiscaleLocalization` | 5 | 0 |
| **New-owner total** | **154** | **0** |

The remaining 336 declarations belong to nine unchanged imported owners, all
freshly elaborated in this accepted run. Two existing style warnings remain:
`Core.PeirceDecomposition` reports unnecessary tactic sequence focus, and
`Clifford.OperatorValuedJones` reports an unused `Matrix.mul_apply` simp
argument. Both complete compiler logs and source-specific dispositions are
preserved. No linter was disabled to obtain these results.

The executed CI command was constructed from the seven-owner target manifest:

```python
roots = json.loads(Path('verification/knutsen-localization/targets.json').read_text())
owners, _, _ = closure(Path.cwd(), roots)
command = [sys.executable, 'tools/quality/check_clifford_dirac.py',
           '--mathlib-root', '../mathlib', '--output', '../knutsen-report']
for module in owners:
    command += ['--target', module]
subprocess.run(command, check=True)
```

It used neither `--incremental` nor `--skip-audit`. The exact executed script
and output remain in the CI job log; the full ordered list of 16 targets is
in `native/report.json` after packaging. The production umbrellas import
mathematical owners directly. The candidate-only audit metaprogram and separate
Lake package were not promoted into the mathematical import surface.

## Strict static scans and individual dispositions

After receiving the final source, the independent reviewer executed seven
`placeholder_audit.py --strict` commands and one seven-file
`semantic_vacuity_gate.py --fail-on warning` command under the shared build
lock. `static-gates.json` records every exact argument, actual return code,
scanner hash, and the seven source hashes before and after the scans.

| Check | Actual result |
| --- | --- |
| Seven strict placeholder scans | All exit 0; no hard findings; 8 soft `skeletal-proof` findings |
| Strict semantic warning-threshold scan | Exit 1; 13 `trivial_surface` warnings; no semantic errors or unreadable inputs |
| Independent review of flagged declarations | All 21 scanner findings individually dispositioned; no unresolved finding |

The warning-threshold scanner is **not reported as passing**. Its raw exit 1,
original findings, and unchanged policy are preserved. Manual semantic
acceptance rests on the actual statements, their definitions and consumers,
and the independent native proof/axiom evidence. A short definitional equation
or finite algebraic simplification is not by itself a proof of the paper's
analytic target, and the publication makes no such claim.

The 13 distinct declarations are accounted for as follows. Eight are flagged by
both heuristic scanners; five only by the semantic scanner.

| Declaration | Source-specific disposition |
| --- | --- |
| `matrixMultiplier_one` | The native diagonal identity reduces the constant-one symbol to `S * Sᴴ`; this is used in complementary reconstruction. |
| `multiplier_const` | A definitional agreement with the existing finite Kraus channel; records owner reuse. |
| `multiplier_add` | Finite-sum distributivity proves additivity while preserving noncommutative factor order. |
| `multiplier_star` | The star laws and associativity establish adjoint compatibility for arbitrary symbols. |
| `multiplier_indicator` | The zero/one finite symbol reduces to the selected partial frame sum consumed by the mask owner. |
| `gram_apply` | An entry equation for an independently defined native matrix; substantive Gram consequences are proved separately. |
| `trace_gram` | Native trace unfolds to the actual diagonal sum without cyclicity or commutativity. |
| `isometryEmbedding_apply` | An accessor for a constructed native non-unital star-ring homomorphism; its injectivity and corner equivalence are separate proofs. |
| `compression_apply` | An accessor for the independently constructed additive compression map, with no ambient multiplicativity claim. |
| `embedding_compression` | Associativity identifies the actual ordered product with its range-corner representative. |
| `compression_star` | Star reversal and involutivity give adjoint compatibility without assuming self-adjoint symbols. |
| `card_balancedSelection` | Exact cardinality of the concrete set `{0, 2}` in `Fin 4`, supporting the explicit equal-cardinality counterexample. |
| `card_parallelSelection` | Exact cardinality of the concrete set `{0, 1}` in `Fin 4`, with the operator comparison proved separately. |

`findings-dispositions.json` retains each original scanner finding, its source
hash, report hash, specific reason, and disposition. The two unchanged-owner
compiler warnings are separately retained there.

## Initial failures, repair evidence, and cancelled local runs

The first local development compilation failed and is not an acceptance
certificate. Its report and relevant logs are preserved under
`initial-development/` with SHA256 checksums. It found an absent pinned native
Mathlib `Idempotents.olean` artifact, unfinished Weyl-twirl simplification, two
Multiscale API/notation errors, and a deprecated Real import. That development
pass skipped its native axiom audit. The later source repairs and matching-pin
artifact restoration were followed by the successful fresh CI execution above.

An initial remote native audit also rejected a compiler-generated unsafe
recursive helper for `remainingPorosity`. The author added the explicit
`noncomputable` modifier to that definition, following the repository's existing
recurrence precedent. The reviewer inspected the pinned Lean implementation:
explicit `modifiers.isNoncomputable` suppresses this executable helper, whereas
the surrounding noncomputable section has a separate error-logging effect.
The one-keyword repair changes no mathematical statement, kernel recurrence,
proof, or permitted axiom. Its exact source review and hash appear in
`noncomputable-source-review.json`; the fresh accepted audit confirms the final
declaration closure satisfies the existing policy.

Both attempted independent local native invocations were cancelled while
waiting for the shared build lock, before either launched Lean, Lake, or a
native audit. The first cancellation followed the observed generated-helper
diagnostic; the second followed successful independent reconciliation of the
fresh remote evidence, avoiding duplicate native compilation. Each cancellation
has its exact invocation, waiting-only console, and observed exit 130 preserved
in a separate receipt. **No repaired local native run completed.** These
cancellations supply no passing proof evidence; native acceptance comes from
the explicitly identified fresh CI run.

## Scope limits and final disposition

This acceptance covers the selected source closure, native transitive axiom
audit, and independent semantic review of the seven new owners. It does not
certify a root/default build, either broad production umbrella, or every tracked
Lean file.

The separately executed root pre-push gate at source checkpoint
`26c53a3a7ae6d9a12b4b83604767c801791dc99c` returned 1 because the external
`HomotopyHypothesis` package directory was absent at
`external_refs/homotopy-hypothesis-lean4`. Its source-debt, semantic-content,
tracked-scope, and quarantine scans passed. The exact root-gate receipt is
preserved separately; the selected native acceptance does not supersede that
failed root build.

The companion CI review also records actual failures at the accepted published
code head: baseline run `43383097585` fails the local-package preflight for
missing `HomotopyHypothesis` and `Atlas` sources and an uninitialized `GIFT`
gitlink; style run `43383097857` rejects the existing case-colliding
`PellisFineStructure.lean` and `PellisfineStructure.lean` paths. Their preserved
provenance and raw log excerpts were read for this report and are packaged under
`ci/current-code-head/`. These broader workflow failures remain visible
alongside the successful dedicated native check.

The analytic obligations enumerated in the theorem contract remain open:
Gaussian STFT/Bargmann constructions, Fock sampling/subaveraging estimates,
the geometric-to-energy implication, and lattice-cell estimates. The proved
finite algebra, metric thickening, real recurrence, and conditional multiscale
theorems retain their stated hypotheses and do not constitute an unconditional
analytic FUP.

Final disposition: **independent acceptance passed at this stated scope**.
The authoritative machine-readable receipt is `acceptance.json`, binding the
native report, native-origin reconciliation, audit log, strict static receipts,
and individual findings dispositions by SHA256.
