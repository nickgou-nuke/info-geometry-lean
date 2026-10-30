# Repository-wide CI context

This record distinguishes the dedicated proof-closure workflow from unrelated
repository-wide workflow failures observed on PR #274. It does not waive any
gate or claim that the root package builds.

The following observations were retrieved from GitHub job logs for source
commit `2993176e98331ee2b37236a039a0ba5d8f248c53` (merge-test commit
`6d8441ff1018324cf79b1b855da8fd34d9d10288`). The later tensor-index repair changes
none of the cited workflow configuration, path dependencies, conflicting files,
or existing placeholder-bearing files.

| Workflow | Observed cause | Evidence |
|---|---|---|
| CI | Path preflight finds missing `external_refs/atlas-lean` configuration and an uninitialized GIFT gitlink. | [Job 123524608892](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834320/job/123524608892) |
| Post-Build Quality Gate | Root Lake build stops because the Atlas package directory is unavailable. | [Job 123524546767](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834356/job/123524546767) |
| Reviewed PR Integration | Recursive checkout attempts to clone the machine-local `/home/goutev/repos/pure_math_lib` submodule URL. | [Job 123524561964](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834223/job/123524561964) |
| Lean style lint | The case-sensitivity check stops at the existing `Physics/PellisFineStructure.lean` and `Physics/PellisfineStructure.lean` collision before running the style linter. | [Job 123524545903](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895833931/job/123524545903) |
| Closure Debt + Superorganism Smoke | The configured Python installation has no `pytest` module. | [Job 123524547127](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834331/job/123524547127) |
| Sorry Gate | The repository-wide debt audit reports existing placeholder-bearing files outside this proof closure. | [Job 123524546663](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834297/job/123524546663) |
| Build thesis, blueprint, and docs | GitHub Pages configuration lookup returns `Not Found`. | [Job 123524550516](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834374/job/123524550516) |

Both colliding filenames already exist at the intake base
`dc3ebf12fdd9ef4e88eb37acffb919e81932061a`. Root package configuration,
dependency pins, the existing workflows above, and the placeholder-bearing
files are unchanged by this PR.

The new `Real Peirce colimit (scoped)` workflow checks the exact imported
mathematical source closure using the repository-pinned compiler and Mathlib.
It has no unsafe-declaration exception or custom axiom allowance. Its own
initial failures were repaired in this PR: first a star-reindexing simplifier
order, then the inherited tensor index's generated executable helper. Final
acceptance must use the repaired source hashes and a successful exhaustive
audit, rather than either failed run.
