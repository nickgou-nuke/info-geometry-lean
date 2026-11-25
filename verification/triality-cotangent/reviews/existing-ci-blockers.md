# Independent comparison of initial CI failures

This checkpoint concerns PR #444 at remote head `501523dba3ec6e433e1d63b30b47f0cf9172099b`, base `fe24e350b08fdea04f74c0748ef9fd9417c47529`, and actual Actions merge `325da1357566a30085ebb3a407ca98a2d26cc3e1`.

The dedicated triality workflow has **introduced Lean failures** described in `initial-validation-review.md`. The additional failures below were independently read from their actual GitHub job logs and are separate. These are observed failures, not a claim that rerunning an untouched base would necessarily produce the identical external environment result.

| Run / job | Observed failure | Source-scope classification |
|---|---|---|
| CI `45370890334` / `138364635298` | Direct path preflight rejects missing `HomotopyHypothesis` and `Atlas` configs and uninitialized `GIFT` gitlink; baseline build skipped | Root manifest, lakefile, path validator and affected dependency paths unchanged by PR |
| Post-Build Quality Gate `45370890643` / `138364560444` | `HomotopyHypothesis: package directory not found` before relevant build | Same existing path dependency |
| Lean style lint `45370890337` / `138364559689` | Case-sensitive filename check finds `PellisfineStructure.lean` and `PellisFineStructure.lean` under `src/InfoGeometry/Physics` | Both files unchanged from base; failure occurs before Lean style checks |
| Sorry Gate `45370890614` / `138364560320` | Repository-wide scan reports 91 debt files and 878 findings | All 91 reported paths extracted and compared with exact PR changed-path list; intersection is empty |
| Closure Debt `45370890713` / `138364561330` | Python test invocation fails: `No module named pytest` | Existing workflow/environment dependency; tests did not run |
| Reviewed PR Integration `45370890468` / `138364560356` | Recursive checkout fails: no URL for gitlink `external_ref/open-math-harness` in `.gitmodules` | Both gitlink and `.gitmodules` unchanged from base |
| Docs `45370890533` / `138364560634` | Pages site lookup returns 404 | External repository Pages setup; Lean/docs build skipped |
| Idempotent chart calculus `45370890452` / `138364560216` | Python `SyntaxError: '(' was never closed` in `tools/quality/check_operator_geometry.py`, line 168 | Checker file unchanged from base |

Independent Git blob comparisons confirmed equality with the base for `lakefile.lean`, `lake-manifest.json`, `tools/infra/ci_bootstrap.py`, `.gitmodules`, the open-math-harness gitlink, `tools/quality/check_operator_geometry.py`, and both case-colliding source files.

The fetched remote PR patch has 18 files and matches the local base-to-candidate changed-file inventory. No root workflow, root package configuration, external gitlink, style-collision file, or Python checker above is part of the PR.

## Existing consumer extraction

The exact block removed from `KreinCl44SplitG2DerivationPosetSynthesis.lean` was independently recovered from the base commit and found byte-for-byte once in `CartanTriality.lean`:

- 5,435 UTF-8 bytes.
- SHA-256 `4accd6d59f1397005999062100d15ab0a046f9199829a646907f2ddffbd81ea2`.

Byte equality is a source-regression check. Successful elaboration of the existing deep consumer remains a separate requirement; its CI step was skipped in the first run.
