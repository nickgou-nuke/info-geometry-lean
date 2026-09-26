## 2026-09-22T06:00:13Z
You are teamwork_preview_worker (worker_weak_drazin_o1).
Your parent is orchestrator_5 (conversation ID: c310530f-678b-4c1c-948e-b8e7ff7beb38).
Your working directory is /home/goutev/info-geometry-lean/.agents/worker_weak_drazin_o1/.

TASK OBJECTIVE:
Refactor `/home/goutev/info-geometry-lean/.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` to eliminate all 22 occurrences of `native_decide`, replacing them with O(1) kernel-checked proofs (`decide`, `rfl`, finite entry expansion, structural unit conjugation) with 100% proposition fidelity.

STEPS:
1. Create CAS verification script in `.agents/sandbox_weak_drazin_o1/CAS/cas_weak_drazin_certificate.py` using SymPy to verify all 3x3 matrix identities, weak Drazin relations (B A^3 = A^2), Souriau-Frame coefficient, and unit conjugation symbolically.
2. In `.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean`:
   - Replace all 22 `native_decide` calls.
   - For matrix equalities: use `ext i j; fin_cases i <;> fin_cases j <;> decide` or `simp [Matrix.mul_apply, ...]` or `decide`.
   - For matrix inequalities (`≠`): prove by showing inequality at a specific entry (e.g. `intro h; have h0 := congr_fun (congr_fun h 0) 1; revert h0; decide`).
   - For `weakPolynomialInverseUnit`: $B \cdot 2I = 1$ reduces via `simp [weakPolynomialInverse, smul_smul]`.
   - For `weak_conjugated_polynomial_inverse_isWeak`: prove general structural theorem `unitConj_isWeakDrazin` (or conjugation identity $(u A u^{-1})^n = u A^n u^{-1}$) and apply it in 1 line, exactly like `unitConj_isMoorePenrose` in `Hartwig1976SVDMoorePenroseBorder.lean`.
3. Verify compilation under the shared build lock.
4. Verify Kernel Axioms (no `Lean.ofReduceBool`, no `sorryAx`).
5. Check Proposition Fidelity (100% character-for-character for all declarations).
6. Generate diff against original.
7. Write full report in `/home/goutev/info-geometry-lean/.agents/worker_weak_drazin_o1/handoff.md`, stage changes with `git add -A`, and send completion message to parent.
