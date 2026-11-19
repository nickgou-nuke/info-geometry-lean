# Validation of the Aitchison contingency projection

Date: 19 November 2026. Base repository commit:
`fea96b564201654cd4693008585039a56f66adf3`.

**Accepted scope:** the finite real matrix projection, its actual subspace
dimensions, and the unique closest strictly positive normalized product table
for the unscaled squared CLR distance. The complete local proof closure passed
fresh native compilation and declaration-wide axiom auditing. The normal root
Lake package remains blocked during dependency initialization, as recorded below.

The mathematical contract, source-paper corrections, theorem map, and physical
interpretation boundary are in [AITCHISON_CONTINGENCY_CONTRACT.md](AITCHISON_CONTINGENCY_CONTRACT.md).

## Environment and dependency provenance

| Item | Checked value |
| --- | --- |
| Root and Mathlib toolchains | `leanprover/lean4:v4.34.1` |
| Native Lean release | `4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` |
| Lake version observed | `5.0.0-src+5045d00 (Lean version 4.34.1)` |
| Mathlib commit | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Root manifest SHA256 | `ceb11ec7ca6c59a1d7787a9bb90a46c8fed69f1b751ee1834ea6a446c92cec98` |
| Official Lean archive SHA256 | `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4` |

The maintained `scripts/build/hydrate_pinned_mathlib_cache.sh` completed
successfully. The final verifier checked Mathlib and each of its eight selected
dependency checkouts against the unchanged manifests and required clean source
checkouts before and after compilation. It also checked the running Lean version
against both toolchain files. Lake's version was recorded, rather than treated
as an additional theorem or independent release assertion.

The dependency artifacts came from this pinned Mathlib workspace. The check did
not rebuild every Mathlib source, and did not use stale root or candidate
artifacts for repository-owned modules.

## Independent fresh native check

The final run used `verification/aitchison-contingency/check.py`, selecting the
task's verified Lean/Lake installation with its `--lake` argument. With the
pinned toolchain on `PATH`, the portable reproduction command is:

```bash
python3 verification/aitchison-contingency/check.py
```

The run completed from **11:26:43 to 11:31:31 UTC** on 19 November 2026
(13:26:43 to 13:31:31 in Europe/Sofia). Its receipt status is `pass`.
The retained run directory is
`.artifacts/aitchison-contingency/check-7s4m2ob1/`.

The verifier acquired the maintained shared build lock, created a fresh local
artifact directory, and compiled the entire canonical local import closure in
dependency order. It enforced exact agreement between that closure and the six
audited mathematical owners plus the audit module. It stopped on failure and
rechecked all selected source, pin, helper, and repository-HEAD identities at
the end. All identities remained unchanged.

| Canonical module, abbreviated | Exit | Seconds |
| --- | ---: | ---: |
| `Probability.BipartiteLogCoupling` | 0 | 51.38 |
| `Probability.AitchisonContingency` | 0 | 49.50 |
| `Probability.AitchisonContingencyDimensions` | 0 | 47.97 |
| `Algebra.FiniteSpinAlgebra` | 0 | 6.45 |
| `Convex.LogSumExp` | 0 | 3.08 |
| `Probability.AitchisonContingencyProbability` | 0 | 51.88 |
| `Probability.AitchisonContingencyAudit` | 0 | 73.94 |

Every module has prefix `InfoGeometry.`. The three new mathematical modules
produced empty diagnostic logs. The existing `BipartiteLogCoupling` owner
retained its pre-existing linter warnings; its source was not changed.

## Declaration-wide axiom audit

The audit requires all 18 named acceptance declarations, then enumerates every
constant owned by the six mathematical modules in the actual Lean environment.
This includes private and generated declarations, not only a source-regex list
of public theorems. It rejects introduced axioms, unsafe or partial declarations,
and transitive axiom dependencies outside the explicit foundational allowlist.

| Mathematical owner | Audited declarations |
| --- | ---: |
| `Probability.AitchisonContingency` | 67 |
| `Probability.AitchisonContingencyDimensions` | 47 |
| `Probability.AitchisonContingencyProbability` | 63 |
| `Probability.BipartiteLogCoupling` | 39 |
| `Convex.LogSumExp` | 13 |
| `Algebra.FiniteSpinAlgebra` | 86 |
| **Total** | **315** |

Native output:

```text
AUDIT_REQUIRED_DECLARATIONS: 18
AUDIT_AXIOMS: [propext, Classical.choice, Quot.sound]
AUDIT_DECLARATIONS: 315
AUDIT_THEOREMS_INCLUDING_GENERATED: 216
AUDIT_SUCCESS: 6 owners
```

The three new owners account for 177 of the audited constants. Their directly
written source contains 23 definitions and 78 theorem/lemma declarations; these
are different counts because Lean generates additional constants.

## Exact accepted source identities

| File under `lean/InfoGeometry/Probability/` | SHA256 |
| --- | --- |
| `AitchisonContingency.lean` | `400c21d7d118b4d19fdbb1540dea2c35ba1bcd814db7124e7f23b7199b012418` |
| `AitchisonContingencyDimensions.lean` | `b6c51bd4ffc987f09f9e94462a30a8c0212e4e77ce00a7df9f9af6b2c3b39101` |
| `AitchisonContingencyProbability.lean` | `c1719c701b0a60b075b8d94f089de599acd8990a54b284075fbeffbf51dc9554` |
| `AitchisonContingencyAudit.lean` | `73dfe585d62151a5acb5989455a5d1b0f094f51910588bbff14849e74ef65d98` |

The reviewed verifier SHA256 is
`af81b3de52e3fc287b4b5cb4f096bff83172bd5070b7c57c0141b14af3507613`.
The independent semantic reviewer read the complete frozen mathematical sources
and checked their canonical copies byte-for-byte against the passing candidates.

## Source and independent semantic checks

The maintained source debt, semantic content, semantic vacuity, and source-scope
checks selected the four new Lean files plus the changed `InfoGeometry.All`
import surface. Each command exited zero; coverage included all five files.
The debt scan found zero `sorry`, `admit`, or custom `axiom` gaps. The semantic
content audit found zero blocking or review findings.

The lexical semantic-vacuity checker reported seven warning-level
`trivial_surface` findings. Independent review accepted them individually:

| Supporting declaration | Reason the short proof is appropriate |
| --- | --- |
| `interactionLinear_apply` | Connects the bundled map to the existing concrete interaction. |
| `additiveProjection_apply` | Exposes the complementary map as `X - interaction X`. |
| `interaction_zero` | Supplies the elementary zero identity used by kernel arguments. |
| `additiveProjection_mem` | Derives membership from proved idempotence; it does not assume the desired minimum. |
| Private `interaction_single_diagonal` | Computes the actual basis coefficient used by the trace/finrank proof. |
| `softmaxSimplex_weights` | Connects native simplex weights to the reused softmax. |
| `productSimplex_weights` | Exposes actual product probabilities for positivity and logarithmic identities. |

These lemmas support the substantive projection, uniqueness, and dimension
proofs. None is substituted for those conclusions. Independent review found no
blocking mathematical defect, circular assumption, or vacuous carrier in the
accepted sources. It explicitly checked the positive-probability domain,
unscaled Frobenius convention, normalization, uniqueness of tables rather than
unfixed logit parameters, and singleton index cases.

## Pre-commit source repair

The first local commit attempt was rejected by the installed staged gate. Its
operator screen rejected three scalar arithmetic steps in matrix-parameter
proofs, and its unused-hypothesis screen rejected three positivity binders.
The gates were kept unchanged.

The repaired core evaluates the Frobenius pairing before applying an explicitly
real scalar identity, simplifies the zero cross-term directly, and uses exact
division cancellation for total centering. The probability module adds
`independent_interaction_reconstruction`: a positive table equals the normalized
exponential of its independent CLR component plus log interaction. This result
requires positivity; it fails on the boundary table `(1, 0)`. The Pythagorean
proof uses its CLR consequence, and minimum/uniqueness derive from Pythagorean.
The earlier public probability statements retain their domain and conclusions.

The repaired canonical files passed the supported staged gate in **strict**
mode before the final fresh native run recorded above. All four source gates
were rerun on the final hashes and passed. Independent semantic revision 2
accepted the actual reconstruction dependency, both scalar repairs, all 18
required declarations, and the seven supporting-lemma warnings.

## Normal root build and publication boundary

The ordinary maintained root-package target was separately attempted:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Probability.AitchisonContingencyAudit
```

It **exited 1 during dependency initialization**, before compiling the target:

```text
error: HomotopyHypothesis: package directory not found:
external_refs/homotopy-hypothesis-lean4
```

That authoritative path dependency is absent in this checkout. The other declared
path `external_refs/atlas-lean` is also absent, so restoring only the first
reported dependency is not asserted to make the complete root build pass. The unchanged
base owner probe had already failed at the same dependency before the new
theorems were integrated. No source or pin substitution was used to make the
root command appear successful.

`InfoGeometry.All` now imports the new audit, but the root umbrella was not
certified by this focused run. The repository's pre-push hook requires the
normal root-package quality gate. The passing focused theorem check does not
override that requirement. No push or pull request is claimed by this record.

The installed pre-commit hook continues to enforce the repository's staged
source checks when the local change is committed.
