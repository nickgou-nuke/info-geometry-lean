# Pauli–Zorn–Quaternion–Peirce Recovery Ledger

Date: 2026-07-13
Status: restoration integrated and aggregate-verified; repository-wide non-owner debt remains explicitly open

## Scope and method

This ledger records the recovery pass over live Lean owners, Git history and unreachable objects, repository archives and generated inventories, and local agent/session/worktree stores. Recovered text is treated as provenance evidence only. A claim is classified as restored only when it is integrated under `InfoGeometry`, consumes live owner definitions, and is accepted by the Lean kernel without `sorry`, `admit`, or a new top-level axiom.

Machine-readable evidence:

- `sandbox/pauli_zorn_arango_ledger.json`
- `sandbox/pauli_zorn_arango_ledger_before_restore.json`
- `sandbox/pauli_zorn_arango_ledger_pre_refresh.json`
- `sandbox/pauli_zorn_git_provenance.json`
- `sandbox/pauli_zorn_companion_ledger.json`
- `sandbox/pauli_zorn_agent_provenance.json`

## Exhaustive search coverage

### Live declaration graph

After the final forced live-stream refresh, Arango contains 130,953 declarations and 46,452 edges. The post-refresh Pauli–Zorn ledger selected 8,368 declarations and 18,844 incident edges from 536 files. It contains 4,467 theorems, 3,326 definitions, 230 inductives, 194 constructors, 147 recursors, and four opaque declarations.

Central-family counts are not disjoint: Zorn 3,176; quaternion 1,533; Pauli 1,786; octonion 2,957; Peirce 175. Bridge-family counts are likewise overlapping: determinant/norm 1,148; equivalence 331; ladder/projector 372; chirality 153; triality/G2 393; Tomita/commutant 32.

Direct AQL prefix checks found all restored namespaces in the live database: canonical derivations 19 declarations; canonical derivation dimension 6; TL chain 12; Jones B3 3; presented B3 41; Yang–Baxter Q-swap 4; split-octonion braid/SU3 141; Zorn scaling 62; Yang–Baxter/Zorn bridge 54; Zorn braid/scaling covariance 38. The previously suspect stale declaration `InfoGeometry.Categorical.ZornBraidColimit.zornContinuumAlgebraInst` has count zero.

### Repository, archives, external references, and generated inventories

The companion scanner traversed 306,712 files, 184,064,829,712 bytes, and 568,108,668 lines. It found 8,532 matching files and reported zero errors. This lane included the repository, Git-associated recovery material, external references, generated inventories, and large expression-graph artifacts rather than skipping them for size.

### Git provenance

The Git scanner covered 155 ref lines, 222 worktree lines, 4,010 reflog lines, 4,490 regex-history lines, 4,483 `fsck` lines, and 3,424 unreachable blobs. Of the unreachable blobs, 797 matched the recovery vocabulary.

Exact pickaxe results:

- `PauliZornTrifactor`: commit `8ee1bb57bf478eb2021c496b2aa76fe71bd2a41a` and duplicate historical commit identity `28bb08d9e7b7bdabfef42cd4470130fb45669be1` record the vendored auto proof.
- `SplitOctonionModularJ`: a historical aggregate/summary integration appears in commit `328fecca581b28d662fae521491d6c14e1cbb394`.
- `canonicalVectorEquiv`, `kingdonZornLinearEquiv`, `preimageHom_comp_realization`, `Hl_mul_Hl`, and `finrank_canonicalZornDerivations`: no committed pickaxe history. Their recovered evidence was uncommitted/session/worktree material or current live code, not a stronger deleted committed theorem.

### Agent/session/worktree/backups

The agent scanner traversed 978,275 files, 110,945,389,763 bytes, and 191,666,651 lines across:

- Hermes: 93,622 files
- Codex: 5,461 files
- Claude: 1,306 files
- Pi: 42 files
- Antigravity/Gemini stores: 847,491 files
- Archon: 9,830 files
- epoch3 Codex export: 13,115 files
- fusion-migrate worktree: 5,649 files
- external backup drive proofs: 1,759 files

It found 120,219 matching files. Four traversal errors were disappearing ephemeral copies of unrelated `PrimitiveSetsAboveX.lean`; the surviving canonical copy at `external/Erdos1196/PrimitiveSetsAboveX.lean` was covered by the zero-error companion scan. No Pauli–Zorn candidate was hidden by those races.

## Owner and theorem-strength ledger

| Claim family | Canonical live owner | Strength | Classification |
|---|---|---|---|
| Canonical Zorn matrix ↔ vector Zorn model | `lean/InfoGeometry/Algebra/Zorn/CanonicalVectorMatrixBridge.lean:11` | Explicit equivalence; additive, scalar, zero/one, multiplication preservation, with inverse readbacks | Present |
| Kingdon realization into Zorn matrices | `lean/InfoGeometry/Algebra/KingdonSplitOctonion.lean:1900` | Native universal-property left inverse `preimageHom_comp_realization` | Present; stronger than multiplication-only recovery fragments |
| Kingdon ↔ Zorn linear equivalence | `lean/InfoGeometry/Algebra/KingdonSplitOctonion.lean:1997` | Explicit linear equivalence backed by realization/preimage | Present |
| Kingdon ↔ canonical Zorn bridge | `lean/InfoGeometry/Algebra/Zorn/KingdonCanonicalBridge.lean:72` | Composed linear equivalence with multiplication readback | Present |
| Quaternion split-octonion shadow product | `lean/InfoGeometry/Projective/Cl44QuaternionSplit.lean:115` | Native theorem `Hl_mul_Hl` | Present |
| Canonical-Zorn derivation Lie algebra | `lean/InfoGeometry/Lie/CanonicalZornDerivation.lean:35` | Genuine `LieSubalgebra`; constructive transport to/from vector derivations; linear and Lie equivalences | Missing, then restored |
| Dimension of canonical-Zorn derivations | `lean/InfoGeometry/Lie/CanonicalZornDerivationDimension.lean:611` and `:667` | Explicit 14-parameter linear equivalence; kernel-checked `finrank = 14` | Missing, then restored |
| Pauli/Zorn trifactor finite matrix packet | `lean/InfoGeometry/External/Auto/PauliZornTrifactor.lean` | Concrete finite matrix/determinant/nilpotent theorems | Present from committed vendored source |
| TL/Jones/B3/Yang–Baxter/Zorn scaling chain | `lean/InfoGeometry/External/Auto/{TLChain,JonesBraidB3,B3PresentedGroup,YangBaxterQSwap,SplitOctonionBraidSU3,ZornScalingFlow,YangBaxterZornBridge,ZornBraidScalingCovariance}.lean` | Concrete finite-dimensional theorem chain | Present text but noncanonical root namespaces; restored as canonical `InfoGeometry.External.Auto.*` declarations |
| Generic witnessed Zorn colimit algebra | `lean/InfoGeometry/Categorical/ZornBraidColimit.lean` | Depends on an explicit multiplication witness/instance surface | Conflicting with native-closure mandate; not used as authority for recovered owner claims |
| Concrete UHF-style Zorn colimit | `lean/InfoGeometry/Categorical/ZornUHFColimit.lean` | Concrete pointwise finite stages, descended tensor multiplication, and a transported square-zero seed | Independently promoted concurrently; repaired and aggregate-verified, but not evidence for the 14-dimensional derivation classification |

## Candidate comparison and decisions

### Restored

1. `CanonicalZornDerivation.lean` restores the missing transport from the already constructive vector Zorn derivations to canonical Zorn matrices. It defines the derivation submodule/Lie subalgebra and proves linear and Lie equivalences; it does not postulate a classification.
2. `CanonicalZornDerivationDimension.lean` restores the missing finite-dimensional classification by constructing both directions of a 14-parameter linear equivalence. The final `finrank = 14` theorem follows from this equivalence, not from an external certificate.
3. The eight external finite-matrix/braid modules were moved from root namespaces to `InfoGeometry.External.Auto.*`. The theorem bodies and multiplication definitions were retained. Backup copies under the external proof drive and `Physics/` tree corroborate provenance.

### Present or superseded

1. Agent-worktree copies of `SplitOctonionModularJ.lean` are duplicates of an already integrated live owner; they were not re-imported.
2. Sandbox/root/`Physics` copies of the TL/Jones/Yang–Baxter/Zorn files are superseded by the canonical namespaced copies. They remain provenance evidence, not competing owners.
3. Multiplication-only Kingdon fragments are superseded by the live `preimageHom_comp_realization` universal-property left inverse and the resulting linear equivalences.
4. Pauli matrix and quaternion/Peirce table fragments already represented by live theorems were classified present rather than duplicated.

### Conflicting or noncanonical

1. Transcript prose, generated summaries, and theorem statements without complete proof context were never promoted as code.
2. The generic witnessed/admitted Zorn-colimit surface is not accepted as closure for native owner claims. Its declarations are not used to justify the restored derivation or dimension results.
3. Stale declaration-graph entries produced by the importer’s historical upsert-only behavior are not source authority. Live source and a successful Lean build take precedence.
4. No recovered fragment justified identifying finite `G₂(2)` with real split `G_{2(2)}`; no such identification was introduced.

## Verification

Successful gates executed during this pass:

- `lake env lean lean/InfoGeometry/Projective/Sandbox/BCFWShift.lean`
- `lake build InfoGeometry.Projective.Sandbox.BCFWShift`
- `lake build InfoGeometry.External.Auto.ZornBraidScalingCovariance` — 8,037 jobs
- direct and aggregate builds of the canonical derivation/dimension chain
- `lake env lean lean/InfoGeometry/Categorical/ZornUHFColimit.lean`
- `lake build InfoGeometry.Categorical.ZornUHFColimit`
- `lake build InfoGeometry.All` — 21,692 jobs
- `/home/goutev/miniforge3/envs/sage/bin/python3 tools/infra/refresh_decl_graph.py --stream --force --arango-db infogeometry` — imported 130,953 declarations and 46,452 edges
- `PYTHONPATH=. python3 sandbox/build_pauli_zorn_arango_ledger.py` — selected 8,368 declarations, 18,844 incident edges, and 536 files

A prior full recursive build completed 21,939 jobs. A later recursive run correctly detected concurrently added, non-aggregate sandbox/source failures. Those moving targets are not reported as green and are not used as evidence for this restoration.

Exact executable-hole audit over `lean/InfoGeometry` found two actual `sorry`s outside this restored slice:

- `lean/InfoGeometry/Categorical/SandboxConcrete.lean:119`
- `lean/InfoGeometry/Meta/OwnerTarget.lean:30`

The restored canonical derivation files and the eight canonical external modules contain no `sorry`, `admit`, or newly introduced top-level axiom. Comment-only uses of the words “axiom” and “admit” were not misclassified as declarations.

## Open debt

- The two unrelated repository-wide holes listed above remain open.
- Full recursive build status remains red while concurrent untracked/non-aggregate files are changing; the aggregate owner surface is green.
- The on-disk `artifacts/dag/index/*.jsonl` snapshots retain older mtimes because this verification used direct `--stream` import. The live Arango database is refreshed, but those generated snapshots remain non-authoritative until separately regenerated.
- This restoration proves the 14-dimensional derivation Lie algebra of the canonical real Zorn model. It does not by itself prove the full automorphism-group classification as real split `G_{2(2)}`; that remains a separate owner theorem obligation.
