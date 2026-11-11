# Dahm–Klein verification status

## Focused hosted kernel, axiom, and screen checks passed

The published mathematical source at commit
`51dc2dc48fdcfca8ac2e400b0ef236d9621c7cac`, tree
`202d72551f6ea23c2da25b1ad337efeccf5d2980`, passed the complete focused build,
a separate fresh declaration/axiom audit, and strict source screening in
GitHub Actions. An independent non-authoring QA reviewer then initiated and
inspected a second hosted execution against the same source tree.

The scoped acceptance disposition is
**`HOSTED_KERNEL_AXIOM_SCREEN_ACCEPTED`**. Full QA release acceptance remains
false. This report and the accompanying receipt do not certify unrelated
root targets, physical interpretations, or checks listed as pending below.

## Exact evidence

- Lean: `v4.34.1`; Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- [First focused run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43012096492/job/130493991879): successful complete build, fresh audit, and strict screen.
- [Independent rerun, attempt 2](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43012096492/job/130529780389): success; checkout merge commit `503dfadd399a36e400b9f223daa18a4216469a79`, with the same tree as the published branch.
- Attempt 2 used restored build artifacts and executed the audit separately and freshly. It is not described as a cache-free rebuild.
- Fresh audit: **96 declarations**, including **77 theorem declarations**: **37 named source theorems** and **40 additional generated theorem declarations**. The other **19 declarations** are not theorems.
- Every named source theorem appears under its actual owning module. Exactly one success marker and 96 unique declaration names were checked.
- Permitted transitive foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`; no introduced axioms or unsafe/partial declarations were accepted.
- Strict screen: all five mathematical owners, no findings.
- Actual tracked pre-commit staged proof gate and staged whitespace check passed at the source checkpoint.
- Independent source review passed for the contract, five mathematical owners, audit, focused configuration, and workflow.

The immutable [HOSTED_QA_RECEIPT.json](HOSTED_QA_RECEIPT.json) records the
observations, source identities, evidence hashes, declaration membership,
and remaining scope. Its SHA256 is
`3ab50da0fd9d1d22d3c6cbad1dbf9bfa7a9c26bfae94b5a762d7515e7914c9f3`.
The matching checksum is in [HOSTED_QA_RECEIPT.sha256](HOSTED_QA_RECEIPT.sha256).

The [attempt 2 artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43012096492/artifacts/13855602955)
has ZIP SHA256
`4f8cc5b5a510f99beb773e309a868bfb5269bc563365dd5fee2f151d1b3f1515`.
Its separately executed audit log has SHA256
`ad16f5cd3a23b1a09dc7fdfc5dd78ac8b322f8f6f551036bfaaaf052c2579c37`.

## Remaining acceptance and integration boundary

The broader earlier acceptance plan still has unexecuted strict refute,
static Gate 4, classified regex vacuity, broader style/traceability signoff,
full staged-index/root-control/dependency-worktree invariance, and compiled
artifact fingerprint coverage. They are not implied by the scoped receipt.

Root integration is not certified. The checkout lacks the
`homotopy-hypothesis-lean4` and `atlas-lean` path dependencies, and the
`gift-framework-core` submodule is uninitialized. Other repository workflows
also report existing setup/debt failures outside this change. These are
separate from the successful focused proof job. No root build or pre-push
success is claimed.

The receipt certifies the source tree above. This report-only follow-up adds
results and the unchanged receipt; it changes no Lean source, dependency pin,
root configuration, hook, or focused workflow. The PR remains a draft and
requests no merge.

## Reproduction

Use the exact focused commands in [README.md](README.md). The shared build
lock serializes local build and audit operations. The included workflow and
the receipt identify the hosted commands and their observed results.
