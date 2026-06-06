# External Repository Inventory

Audit date: 2026-06-06.

Shallow-clone audit updated: 2026-06-06. All nested git checkouts under
`external_refs/` and `external/` now report `rev-parse --is-shallow-repository`
as `false`.

Source archive audited:

```text
/media/goutev/SP DS72/auto/external
```

Repo locations checked:

```text
external_refs/
external/
```

## Summary

The archive was not fully represented as git checkouts in this repo at audit
time. The missing checkouts listed below were cloned from the local archive into
`external_refs/` after the audit. A follow-up unshallow pass fetched full
history and tags for every shallow external checkout.

Most source dependencies from the archive are present under `external_refs/` at
the same git commit. The real gaps are:

- cloned after audit: `atlas-embeddings`, `VirasoroProject`, `QuAIRKit`,
  `PauLie`, `affine-charform`, `RIA_EISA`;
- added or recorded from upstream after audit: `LeanEuclid`,
  `Lean-QuantumInfo`, `deepmind-debate`, `LeanAide`, `Canonical`,
  `CanonicalLean`;
- `pyw`: source files are present, but the repo has no `.git` metadata;
- AFP: present, but under the normalized name `external_refs/mirror-afp-devel`,
  not `external/isabelle`.

Do not infer that a directory is incomplete just because its raw file count
differs. Some count differences are from `.git` internals. Use git HEAD and
tracked-file counts as the source of truth.

## Fully Covered At Same Git Commit

| Archive group | Archive repo | Archive HEAD | Repo path | Repo HEAD | Status |
|---|---|---|---|---|---|
| lean | `LeanDojo` | `7a9f600` | `external_refs/LeanDojo` | `7a9f600` | same tracked source |
| lean | `atlas-lean` | `34ffed3` | `external_refs/atlas-lean` | `34ffed3` | same tracked source |
| lean | `repoprover` | `386adba` | `external_refs/repoprover` | `386adba` | same tracked source |
| lean | `lean-auto` | `7b6f80f` | `external_refs/lean-auto` | `7b6f80f` | same tracked source |
| python | `qutip` | `6933114` | `external_refs/qutip` | `6933114` | same tracked source |
| python | `sympy` | `1991693` | `external_refs/sympy` | `1991693` | same tracked source |
| python | `SymPy-LieAlgebras` | `93f810f` | `external_refs/SymPy-LieAlgebras` | `93f810f` | same tracked source |
| python | `get-physics-done` | `0f41769` | `external_refs/get-physics-done` | `0f41769` | same tracked source |
| python | `sage` | `d8c708d` | `external_refs/sage` | `d8c708d` | same tracked source |
| formal | `afp-devel` | `93084377` | `external_refs/mirror-afp-devel` | `93084377` | same tracked source |
| math | `Semisimple-Lie-Algebras` | `ffa5906` | `external_refs/Semisimple-Lie-Algebras` | `ffa5906` | same tracked source |
| math | `geoalg` | `642992d` | `external_refs/geoalg` | `642992d` | same tracked source |
| math | `SplitOct` | `e29e72f` | `external_refs/SplitOct` | `e29e72f` | same tracked source |

## Covered But Not As A Git Checkout

| Archive group | Archive repo | Archive HEAD | Repo path | Status |
|---|---|---|---|---|
| python | `pyw` | `e44b4fe` | `external_refs/pyw` | all 71 tracked archive files are present, plus local `index.json` and `keyword_index.json`; `.git` metadata is absent |

## Cloned From Archive After Audit

These repositories are now present as local nested git checkouts under
`external_refs/`. They were cloned from the local archive paths and then had
their `origin` remotes reset to upstream URLs. Each checkout also has an
`archive` remote pointing back to `/media/goutev/SP DS72/auto/external`.
They have also been unshallowed from upstream.

They are intentionally not staged as top-level gitlinks/submodules yet. Decide
separately whether to add them as submodules, keep them as untracked local
checkouts, or vendor selected source files.

| Archive group | Archive repo | Archive HEAD | Origin |
|---|---|---|---|
| lean | `atlas-embeddings` | `578453e` | `https://github.com/The-UOR-Foundation-Archive/atlas-embeddings.git` |
| lean | `VirasoroProject` | `555a909` | `https://github.com/kkytola/VirasoroProject.git` |
| python | `QuAIRKit` | `48e7d68` | `https://github.com/QuAIR/QuAIRKit.git` |
| python | `PauLie` | `a13f11b` | `https://github.com/QPauLie/PauLie.git` |
| math | `affine-charform` | `e03d439` | `https://github.com/deehzee/affine-charform.git` |
| math | `RIA_EISA` | `f3292e5` | `https://github.com/csoftxyz/RIA_EISA.git` |

## Added Or Recorded From Upstream After Audit

These repositories were not part of the `/media/goutev/SP DS72/auto/external`
archive comparison, or were present locally but not recorded in this inventory.
They are tracked here as upstream external references after the archive audit
and are intentionally kept outside the `lean/InfoGeometry` owner proof tree
unless specific source is later ported or cited.

| Repo | HEAD | Origin | Local path | Notes |
|---|---|---|---|---|
| `LeanEuclid` | `7c8f38b` | `https://github.com/loganrjmurphy/LeanEuclid.git` | `external_refs/LeanEuclid` | Lean 4.19.0 project for System E, Euclid Book I, UniGeo, and E3 autoformalization/equivalence tooling; nested checkout is full-history and not staged as a top-level gitlink/submodule |
| `Lean-QuantumInfo` | `56e83a9` | `https://github.com/Timeroot/Lean-QuantumInfo.git` | `external_refs/Lean-QuantumInfo` | Lean 4.28.0 project for finite-dimensional quantum information, classical information, statistical mechanics, entropy, CPTP maps, and resource-theory material; README says development moved into Physlib after March 2026; nested checkout is full-history and not staged as a top-level gitlink/submodule |
| `deepmind-debate` | `de3a6e5` | `https://github.com/google-deepmind/debate` | `external_refs/deepmind-debate` | Lean 4.8.0 project formalizing correctness of the stochastic doubly-efficient debate protocol; declares `Debate`, `Prob`, `Comp`, and `Misc`; local `main` matches `origin/main` after fetch; nested checkout is full-history and not staged as a top-level gitlink/submodule |
| `LeanAide` | `d7b5cc39` | `https://github.com/siddhartha-gadgil/LeanAide.git` | `external_refs/LeanAide` | Lean 4.28.0 mixed Lean/Python AI tooling project for autoformalization, code actions, theorem/definition translation, proof/document pipelines, embeddings, premise retrieval, and a server-client workflow; root package declares `LeanAide`, `LeanCodePrompts`, and many Lean executables including `translate` and `leanaide_process`; `LeanAideCore` is a path subproject for the client library; nested checkout is full-history and not staged as a top-level gitlink/submodule |
| `Canonical` | `dbd175b` | `https://github.com/chasenorman/Canonical.git` | `external_refs/Canonical` | Rust workspace for exhaustive term search in dependent type theory, with `canonical-core`, `canonical-compat`, and `canonical_lean` Lean FFI bindings; nested Lean test project under `lean/` pins Lean, mathlib, and `CanonicalLean` to `v4.30.0`; nested checkout is full-history and not staged as a top-level gitlink/submodule |
| `CanonicalLean` | `65510e4` | `https://github.com/chasenorman/CanonicalLean.git` | `external_refs/CanonicalLean` | Lean package named `Canonical` providing the `canonical` tactic; `lakefile.lean` defines a release-fetched `canonical_lean` dynlib target and a default `Canonical` Lean library; pinned to Lean `v4.30.0`; related homepage: `https://chasenorman.com/`; nested checkout is full-history and not staged as a top-level gitlink/submodule |

## Documented But Not Cloned

These repositories were inspected as architecture references only. They are not
present under `external_refs/`, are not proof dependencies, and must not be
treated as source authority without a separate license and provenance decision.

| Repo | Origin | Local documentation | Notes |
|---|---|---|---|
| `OpenCLAW-P2P` | `https://github.com/Agnuxo1/OpenCLAW-P2P` | `docs/P2PCLAW_PUBLICATION_PIPELINE_AUDIT.md` | Public P2PCLAW publication/preparation frontend and protocol reference. Useful for publication packet design and MCP/REST separation. Not cloned because the audited repository metadata did not expose a license and the protocol describes external network participation that must not be automatic. |
| `academic-research-skills` | `https://github.com/Imbad0202/academic-research-skills` | `docs/ACADEMIC_RESEARCH_SKILLS_AUDIT.md` | Claude Code academic research workflow suite for research, writing, review, revision, integrity gates, and finalization. Useful as publication-pipeline architecture. Not cloned because it is CC BY-NC 4.0 and should remain a workflow reference unless separately approved. |
| `academic-research-skills-codex` | `https://github.com/Imbad0202/academic-research-skills-codex` | `docs/ACADEMIC_RESEARCH_SKILLS_AUDIT.md` | Codex-native sibling package wrapping ARS as one `academic-research-suite` skill. Useful for future local experimentation, but not installed or vendored by default because of the same CC BY-NC 4.0 boundary. |

## Still Not A Git Checkout

| Archive group | Archive repo | Archive HEAD | Repo path | Status |
|---|---|---|---|---|
| python | `pyw` | `e44b4fe` | `external_refs/pyw` | all tracked archive files are present, but `.git` metadata is absent |

## Special Cases

### AFP / Isabelle

The archive path:

```text
/media/goutev/SP DS72/auto/external/formal/isabelle/afp-devel
```

corresponds to:

```text
external_refs/mirror-afp-devel
```

Both are git checkouts at `93084377`. The smaller `external/afp` directory is an
extracted working mirror and should not be treated as the full provenance copy.

### Python Quantum Group

The archive path:

```text
/media/goutev/SP DS72/auto/external/python/quantum
```

contains:

```text
QuAIRKit
qutip
```

Both are present. `qutip` was already present at the same commit; `QuAIRKit` was
cloned from the archive and then unshallowed from upstream.

## Shallow Clone Status

The follow-up audit checked 97 nested git repositories under:

```text
external_refs/
external/
```

Result:

```text
shallow_count = 0
error_count = 0
```

This includes the large repositories `mirror-afp-devel`, `qiskit`, `sage`,
`sympy`, `vampire`, `z3`, the newly cloned archive repos, `LeanEuclid`,
`Lean-QuantumInfo`, `deepmind-debate`, `LeanAide`, `Canonical`, and
`CanonicalLean`.

## Organization Policy

Use `external_refs/` for full upstream repository checkouts or source mirrors.

Use `external/` only for extracted corpora, local mirrors, or tool-specific
material that is not intended to preserve upstream git provenance.

Do not vendor new external repositories into `lean/` or owner proof namespaces.
External libraries are evidence and source material; Lean owner files remain the
proof authority.

Before copying an archive repo into `external_refs/`, check:

1. whether a same-HEAD checkout already exists;
2. whether the destination has `.git` metadata;
3. whether the repo is already represented under a normalized name;
4. whether generated caches, build products, `.lake`, virtualenvs, or package
   caches should be excluded;
5. whether the repo should be added as a submodule, plain vendored checkout, or
   documented external reference only.

## Recommended Next Actions

1. Decide whether the six newly cloned repos should become top-level git
   submodules/gitlinks or remain untracked local checkouts.
2. Replace `external_refs/pyw` with a full git checkout, or document it as a
   source-only mirror.
3. Keep `external_refs/mirror-afp-devel` as the AFP provenance owner and avoid
   duplicating it under another path.
4. Add a generated machine-readable manifest only after deciding whether
   missing repos should be copied from the archive or cloned from origin.
