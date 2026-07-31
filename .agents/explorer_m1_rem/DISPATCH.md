## 2026-08-01T01:33:14Z
<USER_REQUEST>
You are Explorer M1 Remediation (teamwork_preview_explorer).
Your assigned working directory is `/home/goutev/repos/info-geometry-lean/.agents/explorer_m1_rem`.
Create your directory `/home/goutev/repos/info-geometry-lean/.agents/explorer_m1_rem` and write `progress.md` and `handoff.md`.

Read:
1. `/home/goutev/repos/info-geometry-lean/ORIGINAL_REQUEST.md`
2. `/home/goutev/repos/info-geometry-lean/PROJECT.md`
3. Full Forensic Audit Report: `/home/goutev/repos/info-geometry-lean/.agents/auditor_m1/handoff.md`
4. Reviewer 1 Report: `/home/goutev/repos/info-geometry-lean/.agents/reviewer_1_m1/handoff.md`
5. Reviewer 2 Report: `/home/goutev/repos/info-geometry-lean/.agents/reviewer_2_m1/handoff.md`

Your mission:
Formulate a genuine, mathematically sound remediation plan for `lean/InfoGeometry/Albert/F4Action.lean` that addresses ALL audit evidence and reviewer feedback without any facades or cheat shortcuts.

Investigate:
1. How `H3ZornF4Derivations` in `lean/InfoGeometry/Algebra/BaezF4H3Zorn.lean` or `IsAlbertDerivation` in `lean/InfoGeometry/Canonical/AlbertAlgebraGenerationsBridge.lean` can be leveraged or re-exported to define `F4Derivation` as a genuine Lie subalgebra of `Module.End ℝ AlbertMatrix` preserving true Jordan product `jordanMul X Y = (1/2 : ℝ) • (X * Y + Y * X)` or `AlbertMatrix` Jordan multiplication.
2. How to use Mathlib's true Lie simplicity `LieAlgebra.IsSimple` or genuine simplicity properties of $\mathfrak{f}_4 = \mathfrak{der}(J_3(\mathbb{O}_s))$.
3. How to define the derivation action `act : F4Derivation → AlbertMatrix → AlbertMatrix` as genuine application `D.1 X` (or derivation action) satisfying the true Leibniz identity: `act D (jordanMul X Y) = jordanMul (act D X) Y + jordanMul X (act D Y)`.
4. Ensure `genPerm12`, `genPerm23`, `genPerm31`, `genPerm_closure`, CKM, and PMNS matrices are cleanly preserved.

Write your remediation plan to `/home/goutev/repos/info-geometry-lean/.agents/explorer_m1_rem/handoff.md` and send a message when done.
</USER_REQUEST>
