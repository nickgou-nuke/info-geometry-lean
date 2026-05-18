# Journal - lelouch (Part 1)

> AI development session journal
> Started: 2026-02-04

---



## Session 1: Quantum DS reduction MVP implementation progress

**Date**: 2026-03-04
**Task**: Quantum DS reduction MVP implementation progress

### Summary

Created and activated Trellis task, implemented pyw.walgebra quantum DS workflow MVP, added tests, and verified new suite passes.

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 7: Quantum DS phase 2a checks + H^q_N

**Date**: 2026-03-05
**Task**: Quantum DS phase 2a checks + H^q_N output

### Summary

Continued Phase 2 by adding decomposition-consistency checks and explicit $H^q_N$ output plumbing for BRST grade blocks, then expanded tests and verified under Sage runtime.

### Main Changes

- Extended candidate data with `cohomology_hq_by_grade` while keeping backward-compatible defaults in `AdmissibleWeightCandidate`
- Added phase-2 decomposition checks in BRST block repetition path (`rank(d0_N)`, `rank(d1_N)`, and expected `H^q_N` scaling checks)
- Kept survivor policy aligned to `N=0` via `by_grade[0]`
- Added input guard for non-integer `cohomology_max_grade`
- Added tests for `H^q_N` mapping consistency (including rank>1 path), grade bookkeeping, and invalid grade input

### Testing

- [OK] `sage -python -m pytest pyw/tests/test_quantum_ds_reduction.py -q --no-cov` (15 passed)

### Status

[OK] **Phase 2 check completed; task remains in progress for finish/create-pr**

### Next Steps

- Final pass on API/docs wording for new cohomology fields
- Run broader related suites as needed
- Prepare finish-work + PR creation when approved


## Session 8: Kazhdan-Lusztig core bring-up under Sage 10.5

**Date**: 2026-04-17
**Task**: kazhdan-lusztig-core-pyw

### Summary

Started the KL core task in `pyw`, validated the local Sage runtime entrypoint, and used it to execute the KL-focused pytest suite while tightening coset, cache, and inverse-KL semantics.

### Main Changes

- Recorded Sage test entrypoint: `/Users/lelouch/miniforge3/bin/sage`
- Recorded test invocation pattern: `"/Users/lelouch/miniforge3/bin/sage" -python -m pytest pyw/tests/test_kazhdan_lusztig.py -q`
- Tightened `CosetRepresentative` normalization and parabolic input validation
- Split `Q_tilde(q=1)` fallback/caching from full polynomial backend behavior
- Added semantic/cache boundary tests and aligned Bruhat interval ordering with the documented contract

### Testing

- [OK] `"/Users/lelouch/miniforge3/bin/sage" --version`
- [WIP] `"/Users/lelouch/miniforge3/bin/sage" -python -m pytest pyw/tests/test_kazhdan_lusztig.py -q`

### Status

[~] **In progress**

### Next Steps

- Re-run KL suite under Sage after current test and interval fixes
- Continue hardening finite/parabolic semantics before bounded-affine expansion


## Session 9: Kazhdan-Lusztig bounded-affine numerator debugging

**Date**: 2026-04-17
**Task**: kazhdan-lusztig-core-pyw

### Summary

Extended the KL core work into refs-backed bounded affine debugging. Added legacy numerator baseline parsing/tests, introduced a legacy-compatible numerator export surface in `pyw`, and then iteratively aligned bounded affine enumeration against `refs/Kazhdan-Lusztig/Algebra.py`. The work substantially reduced the mismatch: translation truncation and Weyl-product ordering now track the legacy implementation much more closely, and the smallest A2 baseline now matches exactly on its first three terms.

### Main Changes

- Added refs-based numerator baseline tests in `pyw/tests/test_kazhdan_lusztig_refs.py`
- Added `AffineWeight.to_legacy_expression()` for Mathematica-style affine weight output
- Added `KacWakimotoCharacter.legacy_numerator_terms(...)` as the pyw-side export contract for legacy `{weight, coefficient}` data
- Tightened bounded affine support in `pyw/algorithms/kac_wakimoto_character.py` by progressively aligning with legacy `GetTranslationsBynShift`, `GetWeylGroupForqSeries`, and coset enumeration behavior
- Added a legacy-style recursive inverse-KL path in `pyw/core/kazhdan_lusztig.py` for bounded affine numerator experiments
- Verified with a fake `coxeter3_sage` shim that the old `Algebra.py` enumeration layer can be exercised without the real backend, which was crucial for comparing `T`, `W`, `WLambda0`, and `WeylToBeSummed`

### Verified Findings

- Sage runtime path confirmed and used throughout: `/Users/lelouch/miniforge3/bin/sage`
- Working test invocation pattern:
  - `"/Users/lelouch/miniforge3/bin/sage" -python -m pytest pyw/tests/test_kazhdan_lusztig.py -q --no-cov`
  - `"/Users/lelouch/miniforge3/bin/sage" -python -m pytest pyw/tests/test_kazhdan_lusztig_refs.py -q --no-cov`
- refs numerator parser/tests are stable under Sage
- For the smallest bounded affine example `A_2^{(1)}, -omega[1]`:
  - the bounded translation set `T` was restored from a broken singleton to a 7-element set after fixing the legacy `nShift` object-space mismatch
  - the first three numerator terms now match refs exactly:
    1. `(-Lambda[1], 1)`
    2. `(Lambda[0] - 2*Lambda[2], -1)`
    3. `(-2*Lambda[0] + Lambda[2] - delta, -1)`

### Debugging Conclusions

- The main historical source of error was not one big algebraic mistake but a stack of smaller mismatches:
  - wrong object space in the legacy `nShift` translation filter
  - incomplete translation basis handling
  - wrong bounded Weyl-product ordering relative to legacy `W = WFinite × T`
  - premature conclusions about `Q`/`Qtilde` when the real remaining mismatch was often in the orbit/coset mapping
- The current remaining mismatch is **not** broad anymore. It has been narrowed to the tail of the bounded affine numerator pipeline:
  - late-term coset/orbit representative mapping
  - how the bounded `W` universe seen by `pyw` still differs from the one implicitly used by old `Alg`
  - a small set of remaining `q/-q/0` coefficient discrepancies in later A2 terms
- A subtle but important historical finding: old `Alg` can report `WLambda0 = [e]` even in a case where `s1` visibly fixes `Lambda` and is present in `W`. This means old internal state is not fully self-consistent at that layer, so exact reproduction must be driven by output behavior, not only by literal internal subgroup expectations.

### Later Correction

- The above `WLambda0 = [e]` suspicion was corrected after a direct run of the original legacy entrypoint provided by the user:
  - `alg = Alg.Alg(['A', 2, 1], QLoad=False)`
  - `llambda = -alg.omega[1]`
  - `alg.Kazhdan_Lusztig_numerator(llambda, 3)`
- In that real legacy workflow, after loading cached translations, old `Alg` reports:
  - `W_Lambda0 = [1, w1]`
- This matches the current `pyw` observation `W0 = [e, s1]`, so `WLambda0` is **not** the remaining root cause.
- Updated debugging interpretation: the remaining mismatch is downstream of the shared `WLambda0` shape and should stay focused on late-term orbit/coset mapping plus coefficient alignment against refs.

### Additional Narrowing

- A direct weight-to-coefficient comparison for the smallest refs-backed affine baseline `A_2^{(1)}, -omega[1]` shows that the **weight set is now complete**: every expected weight from refs appears in current `pyw` output.
- Therefore, the remaining mismatch is no longer about missing weights or broken bounded translation coverage. It is specifically about:
  - coefficient disagreement on a subset of shared weights, especially later `q/-q/0` terms
  - ordering differences in the emitted list, which matter for file-level exact comparison but are now secondary to the coefficient mismatch itself
- This is a meaningful milestone because it confirms the bounded affine enumeration universe is largely reconstructed; the remaining work is a tail-stage output-alignment problem rather than a broad semantic gap.

### Real Coxeter Reproduction

- After adding an `invpol` method to the installed `coxeter3_sage/coxeter3.py` and exposing the working command path
  - `/private/var/tmp/sage-10.4-current/local/bin/coxeter`
  through `PATH`, the legacy `Algebra.py` path was re-run against real coxeter instead of the fake shim.
- This confirmed an important point: the refs numerator files are consistent with the **real legacy `invpol` path**, not just with a fake or partially reconstructed path.
- For `A_2^{(1)}, -omega[1], order=3`, the old code produced the refs-style prefix under real coxeter:
  - `(-Lambda[1], 1)`
  - `(4*Lambda[0]-3*Lambda[1]-2*Lambda[2]-delta, q)`
  - `(2*Lambda[0]-5*Lambda[1]+2*Lambda[2]-2*delta, q)`
  - `(2*Lambda[0]+Lambda[1]-4*Lambda[2]-delta, 0)`
- Updated interpretation: the next high-value step is no longer to approximate legacy output indirectly. It is to make `pyw.core.kazhdan_lusztig.KazhdanLusztigPolynomials` successfully initialize its `_coxeter3` backend under the same environment and compare from that true `invpol` path.

### Pyw Coxeter Backend Activation

- `pyw/core/kazhdan_lusztig.py` was corrected to initialize `coxeter3_sage.Coxeter3` using the actual installed constructor signature `Coxeter3(W, q, command=...)` rather than the earlier incompatible type-string call.
- Added command discovery so `pyw` can locate the working executable path (including `/private/var/tmp/sage-*/local/bin/coxeter`) when the shell `PATH` does not expose it directly.
- Result: `KazhdanLusztigPolynomials(W)` now successfully initializes `_coxeter3` in this environment.
- Important follow-up finding: even after `pyw` is connected to real coxeter, the key affine `invpol/Q_tilde` values for the small A2 probe pairs remain `1`, so the remaining refs mismatch is **not** due to backend non-activation.

### Current Narrowest Mismatch

- A direct old/new comparison of `WeylToBeSummed` for the smallest affine refs case `A_2^{(1)}, -omega[1], q-order 3` now shows the first genuine divergence at **index 1**.
- Old path (real coxeter-backed `Alg`) chooses:
  - `([1,2,1,0], 4*Lambda[0]-3*Lambda[1]-2*Lambda[2]-delta)`
- Current `pyw` path chooses:
  - `([2,1,0], -4*Lambda[0]+Lambda[1]+2*Lambda[2]-3*delta)`
- This is the strongest current evidence that the remaining discrepancy is no longer in `Qtilde`, `WLambda0`, or backend activation. It is now concentrated in the **`weightsToBeSummed -> cosets` representative-selection rule**, i.e. which reduced word is retained as the canonical representative for a repeated weight during bounded affine enumeration.

### Scope Correction

- A later review against `.trellis/tasks/kazhdan-lusztig-core-pyw/prd.md` exposed a process mistake: the debugging path had drifted into `KacWakimotoCharacter` and end-to-end numerator reconstruction, even though the PRD explicitly marks `KacWakimotoCharacter`, `pyw/core/character.py`, and the admissible-character pipeline as **out of scope**.
- This means the refs-based `KacWakimotoCharacter` experiments were useful for discovering semantic gaps, but they should not be treated as the primary implementation target for this task.
- Corrected scope going forward:
  - keep any insights that improve `pyw/core/bruhat.py` and `pyw/core/kazhdan_lusztig.py`
  - stop treating `KacWakimotoCharacter` as the delivery surface for this PRD
  - reinterpret refs numerator data only as external historical evidence, not as a reason to keep expanding the unfinished character layer
- This correction also changes the testing goal: refs parsing tests can remain as format/reference utilities, but direct core-task success criteria must move back to KL core semantics, bounded affine behavior, backend contracts, and cache correctness inside `pyw/core`

### Core-Only Validation After Scope Reset

- After removing the `KacWakimotoCharacter`-dependent refs comparison assertions from `pyw/tests/test_kazhdan_lusztig_refs.py`, the refs test file now stays within PRD scope and only covers:
  - refs numerator file discovery
  - legacy numerator file parsing
  - affine-weight legacy formatting helpers
  - format/normalization utilities
- Updated one stale KL-core assertion in `pyw/tests/test_kazhdan_lusztig.py` so it matches the current inversion-based full-polynomial fallback semantics.
- Re-ran the scope-corrected core-only test suite with Sage:
  - `"/Users/lelouch/miniforge3/bin/sage" -python -m pytest pyw/tests/test_kazhdan_lusztig.py pyw/tests/test_kazhdan_lusztig_refs.py -q --no-cov`
  - Result: `40 passed, 1 skipped`
- This marks the scope-corrected KL core validation as green again, even though the earlier exploratory character-layer investigations remain unresolved and intentionally out of scope.

### Testing

- [OK] `"/Users/lelouch/miniforge3/bin/sage" -python -m pytest pyw/tests/test_kazhdan_lusztig.py -q --no-cov`
- [OK] `"/Users/lelouch/miniforge3/bin/sage" -python -m pytest pyw/tests/test_kazhdan_lusztig_refs.py -q --no-cov` for parser/contract phases earlier in the session
- [WIP] exact refs baseline comparison for bounded affine numerator remains incomplete; current focus is the A2 minimal example and later-term coefficient/order alignment

### Status

[~] **In progress**

### Next Steps

- Continue driving the bounded affine path by matching output behavior against refs, not by over-trusting old internal subgroup state
- Finish aligning `LambdaOrbitUnderWeylDot -> weightsToBeSummed -> cosets -> WeylToBeSummed` for the late A2 terms
- Re-run exact refs comparisons once the remaining A2 tail mismatch is resolved, then expand to the D-type baseline


## Session 2: Reproduce sl3 k=-9/4 DS non-vacuum list

**Date**: 2026-03-04
**Task**: Reproduce sl3 k=-9/4 DS non-vacuum list

### Summary

Added boundary reproduction API for sl3 k=-9/4, validated 16 AKM -> 12 DS surviving -> 6 independent pairs, and added tests.

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 3: Fix DS reproduction to remove hardcoded Table 3 survivors

**Date**: 2026-03-04
**Task**: Fix DS reproduction to remove hardcoded Table 3 survivors

### Summary

Replaced hardcoded Table 3 survivor list/pairs with computed pipeline: boundary AKM enumeration (16) by positivity, DS non-vanishing filter (lambda0!=0 for this case), and involution-based pairing to 6 classes; tests pass.

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 4: Refactor quantum reduction module and move sl3 case study to demo

**Date**: 2026-03-04
**Task**: Refactor quantum reduction module and move sl3 case study to demo

### Summary

Removed case-specific analysis from pyw/walgebra/quantum_ds_reduction.py, added generic linear nondegeneracy filter API, updated tests, and added a demo notebook for sl3 k=-9/4 Table 3 reproduction.

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 5: Quantum reduction refactor and demo migration (temporary)

**Date**: 2026-03-04
**Task**: Quantum reduction refactor and demo migration (temporary)

### Summary

Refactored quantum_ds_reduction into generic algorithm module with linear non-degeneracy filter API, moved sl3 k=-9/4 Table 3 reproduction into demo notebook, and updated tests.

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 6: Quantum DS phase 1.5

**Date**: 2026-03-05
**Task**: Quantum DS phase 1.5

### Summary

Implemented phase-1.5 BRST N=0 cohomology with structure-constant d1 and nilpotency check; added DS tests.

### Main Changes



### Git Commits

| Hash | Message |
|------|---------|
| `424dc55` | (see git log) |

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 7: Phase 2 decomposition checks + H^q_N output

**Date**: 2026-03-06
**Task**: Phase 2 decomposition checks + H^q_N output

### Summary

Completed Phase 2a: grade-wise BRST blocks via ghost Fock multiplicity model, decomposition-consistency rank checks, H^q_N output in cohomology_hq_by_grade. 15 tests pass. ruff (import sort fixed) + mypy clean.

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 8: KL core affine bounded helpers

**Date**: 2026-04-20
**Task**: KL core affine bounded helpers

### Summary

拆解 refs/Kazhdan-Lusztig/Algebra.py，补充 KazhdanLusztigPolynomials 的 Q 别名、affine bounded elements/interval/Q_tilde/stabilizer 辅助，并新增对应测试；使用 sage -python -m pytest pyw/tests/test_kazhdan_lusztig.py -q --no-cov 验证通过。

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 9: KL naming semantics correction

**Date**: 2026-04-20
**Task**: KL naming semantics correction

### Summary

修正 pyw/core/kazhdan_lusztig.py 的 Q 与 Q_tilde 语义：Q 现在表示 Weyl 群元素级 inverse KL，多项式/at_one 缓存标签改为 Q_at_one；Q_tilde 改为陪集级入口并转发到 parabolic_Q_tilde；affine_bounded_Q_tilde 退化为 legacy alias，新增 canonical 名称 affine_bounded_Q；同步更新测试、docstring 与缓存断言，并用 sage -python -m pytest pyw/tests/test_kazhdan_lusztig.py -q --no-cov 验证 36 passed。

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 10: Affine KL workflow and character assembly

**Date**: 2026-04-20
**Task**: Affine KL workflow and character assembly

### Summary

新增 pyw/core/affine_kl.py，打通 order 截断、dominant Lambda 搜索、stabilizer 与 quotient representative workflow；在 pyw/core/kazhdan_lusztig.py 新增 bounded affine coset-level Q_tilde helper；在 pyw/core/character.py 新增第一版 KazhdanLusztigCharacter，使用 VermaCharacter 进行 grade-only character 组装；补充 test_affine_kl_context.py 与 test_affine_kl_character.py，并通过 sage -python -m pytest pyw/tests/test_kazhdan_lusztig.py pyw/tests/test_affine_kl_context.py pyw/tests/test_affine_kl_character.py -q --no-cov（44 passed）。

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 11: Affine KL demo notebook

**Date**: 2026-04-20
**Task**: Affine KL demo notebook

### Summary

在 demos/ 下新增 affine_kl_current_workflow_demo.ipynb，介绍当前已实现的 Q/Q_tilde 语义、AffineKLContext、bounded affine workflow、VermaCharacter 与第一版 KazhdanLusztigCharacter 的使用方式；本地验证 notebook JSON 与关键示例调用可运行，并根据 Oracle 复核收紧了 Q_tilde 语境、order 语义和当前实现边界的表述。

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 12: D4 lambda-to-Lambda comparison

**Date**: 2026-04-20
**Task**: D4 lambda-to-Lambda comparison

### Summary

对照 demos/D4 characters M3.ipynb 与当前 pyw，从 lambda_hat 到 Lambda_hat 的映射在 D4 affine, k=-2 的三个例子上并不一致。旧 Algebra.py 给出：-2ω̂0 -> -Λ2+δ, wTollambda=w0；-2ω̂1 -> -Λ2, wTollambda=w1；-ω̂2 -> -Λ2, wTollambda=1。当前 pyw 的 AffineKLContext.build 在默认 bounded translation search（order=1）下对这三个例子均找不到 dominant representative。根因是两边的 Lambda 搜索策略不同：旧实现直接扫描 Sage affine Weyl group 的前 50 个元素，而 pyw 当前实现先按 translation box 截断半直积候选集。

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 13: Fix legacy GetLambda weight conversion

**Date**: 2026-04-20
**Task**: Fix legacy GetLambda weight conversion

### Summary

通过逐项对照 demos/Algebra.py:GetLambda 的上游中间量，定位到 pyw/core/affine_kl.py 的 legacy extended weight-lattice 组装函数错误。修复了 D4^(1) marks 的获取方式，并修正 legacy 权对象组装中对 Sage FiniteFamily 的取值逻辑。修复后，D4 vacuum 例子上 old Algebra 与 pyw 的 llambda、rho、llambda+rho 以及前五个 prefix Weyl 作用结果逐项一致。随后继续回归 D4 k=-2 的三个 Lambda case。

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete


## Session 14: AffineLieAlgebra invariants and flattening

**Date**: 2026-04-21
**Task**: AffineLieAlgebra invariants and flattening

### Summary

为 AffineLieAlgebra / finite_lie_algebra 补充 dim、num_roots、num_positive_roots、num_negative_roots 等常用标量接口；压平 alpha_0、rho、positive_roots、negative_roots、theta 的若干内部转发路径，减少不必要的 finite_lie_algebra 间接层；相关测试通过 sage -python -m pytest pyw/tests/test_affine_lie_algebra.py -q --no-cov（45 passed）。

### Main Changes



### Git Commits

(No commits - planning session)

### Testing

- [OK] (Add test results)

### Status

[OK] **Completed**

### Next Steps

- None - task complete
