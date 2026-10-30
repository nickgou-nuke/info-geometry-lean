# CI comparison for PR #274 at 4468137

**Confirmed:** all seven listed broad workflow failures still have the previously evidenced causes. Each current run individually reports source commit `4468137c6b9bfac71874188c816d3fb95b44867b`; the tested merge commit is `950f8afbda490e76d9756ac40efba40aaf6a1d80`.

This candidate compares the current GitHub job logs with every prior job log cited by `docs/intake/2026-10-29-real-peirce-colimit/ci-context.md` for source `2993176e98331ee2b37236a039a0ba5d8f248c53`. Observed 2026-10-29 15:29:22 UTC.

| Workflow | Current verified failure | Current job | Prior job | Comparison |
|---|---|---|---|---|
| CI | Atlas has no checked-out directory/configuration at external_refs/atlas-lean; GIFT has missing configuration and an uninitialized gitlink at external_refs/gift-framework-core. | [123543623474](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40901169991/job/123543623474) | [123524608892](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834320/job/123524608892) | Same cause |
| Build thesis, blueprint, and docs | GitHub Pages site lookup returns Not Found. | [123543535582](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40901170032/job/123543535582) | [123524550516](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834374/job/123524550516) | Same cause |
| Closure Debt + Superorganism Smoke | The configured Python 3.11.17 interpreter has no pytest module. | [123543537676](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40901170041/job/123543537676) | [123524547127](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834331/job/123524547127) | Same cause |
| Lean style lint | The case-sensitivity phase rejects Physics/PellisFineStructure.lean and Physics/PellisfineStructure.lean before the style linter can proceed. | [123543534330](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40901169990/job/123543534330) | [123524545903](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895833931/job/123524545903) | Same cause |
| Sorry Gate | The tracked-scope audit reports 91 debt files and 878 findings: 867 forensic/fixture and 11 unclassified nonpackage, with zero lake_package findings. | [123543534981](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40901170046/job/123543534981) | [123524546663](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834297/job/123524546663) | Same cause |
| Reviewed PR Integration | Recursive checkout cannot clone the configured /home/goutev/repos/pure_math_lib repository, which does not exist on the hosted runner. | [123543534768](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40901170062/job/123543534768) | [123524561964](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834223/job/123524561964) | Same cause |
| Post-Build Quality Gate | The root Lake build cannot locate the Atlas package directory external_refs/atlas-lean. | [123543534214](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40901170003/job/123543534214) | [123524546767](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40895834356/job/123524546767) | Same cause |

## Stronger comparisons

- **CI path preflight:** the full Atlas/GIFT/InfoGeometryCore JSON is identical after excluding only the tested revision. Atlas is missing its configuration and checked-out path; GIFT has a missing configuration and an uninitialized gitlink. The later compiler-bridge smoke attempt also encounters the same missing Atlas package.
- **Sorry Gate:** the entire normalized **99-line report is identical**: **28,316** tracked Lean files, **91** debt files, **878** findings, **0** in `lake_package`, **867** forensic/fixture findings, and **11** unclassified nonpackage findings. None of the 91 reported debt paths belongs to the reviewed 32-module proof closure.
- **Style action:** its nested case-sensitivity check explicitly reports “Found files or folders with same name but different case” for the existing `PellisFineStructure.lean` / `PellisfineStructure.lean` pair.
- **Source changes:** the [GitHub comparison](https://github.com/nickgou-nuke/info-geometry-lean/compare/2993176e98331ee2b37236a039a0ba5d8f248c53...4468137c6b9bfac71874188c816d3fb95b44867b) contains two intervening source commits and only five changed paths: the scoped workflow, README, `TowerMatrix.lean`, `Causal/Cones.lean`, and scoped selector. None is an implicated broad-workflow configuration, dependency/submodule path, colliding filename, or reported debt file.

## Scope

The workflows remain failed. This comparison neither waives a gate nor claims that the root package builds. The GitHub Pages evidence establishes a `Not Found` response, not a complete diagnosis of repository settings or permissions. The dedicated mathematical workflow and final proof audit require their own successful evidence.

Only GitHub reads and scratch evidence writes were performed. No live repository/index file was edited, no workflow was rerun, and no compilation or test was executed.
