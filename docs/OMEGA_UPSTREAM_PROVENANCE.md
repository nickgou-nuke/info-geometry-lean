# Omega upstream provenance

Audit date: 2026-09-18.
Local comparison endpoint: `51ab1b40959911e1cb5c0d98113e963fcd14bd60`.

## Finding

The originally restored `lean/Omega` directory is an exact Git-tree match for
`lean4/Omega` in
[the-omega-institute/automath](https://github.com/the-omega-institute/automath).
The matching upstream snapshot declares **version `0.1.1`** in its
[VERSION file](https://github.com/the-omega-institute/automath/blob/11a7761afb1dd97ec7d5a36228f5c1d85911fbb2/VERSION).
This is a version-file value, not a verified release tag.

Our present Omega sources are a locally modified, vendored copy of that
snapshot, not an unchanged upstream checkout. This finding concerns the
project's `Omega` modules, not Lean's built-in `omega` tactic.

## Exact source fingerprint

| Evidence | Value |
| --- | --- |
| Upstream branch investigated | `dev` |
| Matching upstream commit | `11a7761afb1dd97ec7d5a36228f5c1d85911fbb2` |
| Upstream commit date | 2026-05-09 17:43:46 UTC |
| Upstream commit subject | Standardize HyperKernel Lean integration |
| Upstream directory | `lean4/Omega` |
| Local restoration commit | `b0c7612033272eb9fdf7c250053d551ecc0ef7b8` |
| Local restoration date | 2026-07-07 07:58:55 +03:00 |
| Local restoration subject | goal: Major restore and refactor of lost archives |
| Local directory | `lean/Omega` |
| Shared Git tree SHA | `90b99cd9054e3d9994168e7a6172485628a4d559` |
| Files in restored directory | 9,807 |

The matching tree SHA identifies the complete recursive directory contents,
including names, file modes, and blob contents; this is not a sampled-file
similarity claim. The enclosing directory names may differ without changing
the tree SHA.

Upstream evidence:

- [Matching commit](https://github.com/the-omega-institute/automath/commit/11a7761afb1dd97ec7d5a36228f5c1d85911fbb2).
- [Git tree API showing the Omega subtree SHA](https://api.github.com/repos/the-omega-institute/automath/git/trees/11a7761afb1dd97ec7d5a36228f5c1d85911fbb2:lean4).
- [Later matching snapshot](https://github.com/the-omega-institute/automath/tree/f76f46f07a1a48d5c12a20c2f8d366bb9df9330d/lean4/Omega),
  commit `f76f46f07a1a48d5c12a20c2f8d366bb9df9330d`, dated 2026-05-15.

## Limits of the identification

Both upstream commits above contain the same Omega tree. Consequently, the
source snapshot is established, but the exact commit checked out at download
time is not uniquely determined. The local restoration date is not evidence
of the original download date. No claim is made that the entire upstream
repository, its root umbrella module, or its toolchain was copied unchanged.

At inspection time, `external_refs/automath`, its Git metadata,
`docs/automath_github_manifest.json`, and
`docs/automath_github_load_report.json` were absent. No tracked history for
those manifest/report paths was found.

The repository's [sync script](../tools/infra/sync_automath_github.py) names the
upstream URL and `dev` ref, and its
[loader](../tools/infra/load_automath_github.py) copies `lean4/Omega` into
`lean/Omega`. These scripts corroborate the intended source route, but their
local introduction on 2026-07-24 postdates the restoration and does not prove
which command originally downloaded the files. Neither script was executed
for this audit.

## Local divergence at the audited endpoint

Comparing the restoration commit to the local endpoint recorded above, restricted
to `lean/Omega` and with rename detection disabled:

- 22 added files;
- 287 modified files;
- no deleted files;
- 3,479 inserted lines and 2,806 deleted lines across 309 files.

The endpoint's Omega tree SHA is
`d67d5e7ff9806068532a34e248160272dc67060a`.
These are source-control statistics, not counts of new mathematical results or
verified proofs. They exclude local bridge modules outside `lean/Omega`.
No uncommitted changes under `lean/Omega` were reported at inspection time.

## Reproduce the local comparison

These commands inspect history without changing the worktree or index:

```bash
cat AGENTS.md >/dev/null
git rev-parse b0c7612033272eb9fdf7c250053d551ecc0ef7b8:lean/Omega
git ls-tree -r --name-only b0c7612033272eb9fdf7c250053d551ecc0ef7b8:lean/Omega | wc -l
git diff --no-renames --name-status \
  b0c7612033272eb9fdf7c250053d551ecc0ef7b8 \
  51ab1b40959911e1cb5c0d98113e963fcd14bd60 -- lean/Omega
git diff --no-renames --shortstat \
  b0c7612033272eb9fdf7c250053d551ecc0ef7b8 \
  51ab1b40959911e1cb5c0d98113e963fcd14bd60 -- lean/Omega
```

The upstream links are commit-pinned so that future changes to `dev` do not
silently change this evidence. This provenance audit does not certify Lean
compilation, theorem strength, or upstream mathematical claims.
