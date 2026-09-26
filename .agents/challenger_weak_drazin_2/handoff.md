# Empirical Challenge Handoff Report: Campbell--Meyer Weak Drazin Refactor

**Target**: `.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean`  
**Verdict**: **APPROVE**  
**Challenger**: `challenger_weak_drazin_2` (`teamwork_preview_challenger`)  
**Date**: 2026-09-22T06:18:00Z  

---

## 1. Observation

1. **Elimination of `native_decide`**:
   - The live file `lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` utilized `native_decide` across 16 theorems.
   - The sandbox file `.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` replaced all 16 instances of `native_decide` with exact algebraic and matrix simplification proofs (`rw`, `ext i j`, `fin_cases`, `norm_num`, `simp`), achieving 100% formal Lean 4 kernel verification.
   - Diff inspection shows no alteration of the mathematical statements, while introducing foundational structural lemmas:
     - `unitConj_mul : unitConj u A * unitConj u B = unitConj u (A * B)`
     - `unitConj_pow : (unitConj u A) ^ n = unitConj u (A ^ n)`
     - `unitConj_isWeakDrazin : IsWeakDrazin A B k → IsWeakDrazin (unitConj u A) (unitConj u B) k`

2. **Universal Unit Conjugation Stress-Testing**:
   - In `.agents/challenger_weak_drazin_2/StressHarness.lean`, we constructed non-permutation unit representations:
     - **Diagonal Scaling Unit**: $S = \text{diag}(3, 5, 7) \in \text{GL}_3(\mathbb{Q})$ with $S^{-1} = \text{diag}(1/3, 1/5, 1/7)$. Verified `weak_scaling_conjugated_polynomial_isWeak` via `unitConj_isWeakDrazin` and confirmed via direct oracle calculation `weak_scaling_conjugated_polynomial_isWeak_direct`.
     - **Upper-Triangular Shearing Unit**: $U = \begin{pmatrix} 1 & 2 & -3 \\ 0 & 1 & 4 \\ 0 & 0 & 1 \end{pmatrix}$ with $U^{-1} = \begin{pmatrix} 1 & -2 & 11 \\ 0 & 1 & -4 \\ 0 & 0 & 1 \end{pmatrix}$. Tested on both commuting polynomial inverse and non-commuting wild inverse `weakWildInverse` (`weak_shear_conjugated_wild_isWeak` and direct oracle `weak_shear_conjugated_wild_isWeak_direct`).
     - **Dense $SL_3(\mathbb{Z})$ Unit**: $M = \begin{pmatrix} 1 & 2 & 3 \\ 0 & 1 & 4 \\ 5 & 6 & 0 \end{pmatrix}$ with $M^{-1} = \begin{pmatrix} -24 & 18 & 5 \\ 20 & -15 & -4 \\ -5 & 4 & 1 \end{pmatrix}$. Verified `weak_dense_conjugated_drazin_isWeak` on the singular Drazin inverse `weakDrazinInverse`.
   - **Higher Power Indices ($k=3, 4$)**:
     - Formulated and proved structural ascension lemmas:
       - `isWeakDrazin_succ : IsWeakDrazin a b k → IsWeakDrazin a b (k + 1)` (constructive, 0 axioms).
       - `isWeakDrazin_of_le : k ≤ m → IsWeakDrazin a b k → IsWeakDrazin a b m` (constructive, 0 axioms).
     - Proved stability under unit conjugation at powers $k=3$ and $k=4$:
       - `weak_shear_conjugated_k3 : IsWeakDrazin (unitConj U A) (unitConj U B) 3`
       - `weak_shear_conjugated_k4 : IsWeakDrazin (unitConj U A) (unitConj U B) 4`
   - **Index Minimality Obstruction ($k=1$)**:
     - Tested whether index $k$ can be reduced below nilpotency order 2.
     - Formally proved: `not_isWeakDrazin_k1_weakPolynomialInverse : ¬ IsWeakDrazin weakA weakPolynomialInverse 1` by demonstrating that the $(1, 2)$-coordinate yields $0 = 1 \implies \text{False}$.

3. **Two-Sided Invertibility of `weakPolynomialInverseUnit`**:
   - Formally verified two-sided inverse laws in `(Mat3 ℚ)ˣ`:
     - `weakPolynomialInverseUnit_val_inv : u.val * u.inv = 1`
     - `weakPolynomialInverseUnit_inv_val : u.inv * u.val = 1`
   - Formally verified direct entrywise two-sided matrix multiplication in `Mat3 ℚ`:
     - `weakPolynomialInverse_mul_right_eq_one : (1/2 I) * (2 I) = 1`
     - `weakPolynomialInverse_mul_left_eq_one : (2 I) * (1/2 I) = 1`
   - Non-tautological invertibility:
     - Formally proved `weakPolynomialInverse_det_ne_zero : Matrix.det weakPolynomialInverse ≠ 0` (det is $1/8 \ne 0$).
     - Contrasted with singular Drazin inverse: `weakDrazinInverse_det_zero : Matrix.det weakDrazinInverse = 0`.
     - Formally proved `weakDrazinInverse_not_invertible : ¬ ∃ B, weakDrazinInverse * B = 1`.

4. **Kernel Profiling and Axiom Audit**:
   - Axiom check (`#print axioms`) executed under sequential build lock (`/tmp/info-geometry-build.lock`):
     - Zero unapproved axioms: all theorems depend only on core foundational axioms `[propext, Classical.choice, Quot.sound]`.
     - Zero `sorry`, zero `admit`, zero `native_decide`.
   - Profiling results:
     - Full file compilation: 14.91s (includes Mathlib imports ~8s).
     - Individual theorem elaboration + typechecking: maximum 280ms (`weakA_cubic_eq_two_smul_square`), average ~150ms.
     - Simp tactic execution: maximum 209ms.

---

## 2. Logic Chain

1. **Adversarial Hypothesis 1**: `unitConj_isWeakDrazin` might be over-specialized or only hold for permutation matrices.
   - *Refutation*: The proof of `unitConj_isWeakDrazin` relies solely on the monoid homomorphism properties of conjugation (`unitConj_mul` and `unitConj_pow`). We verified empirically that arbitrary invertible matrices $u \in \text{GL}_3(\mathbb{Q})$ (including diagonal scaling, triangular shearing, and dense integers) preserve `IsWeakDrazin A B k`. The direct matrix arithmetic evaluation (`_direct` theorems) matched the theorem output exactly.

2. **Adversarial Hypothesis 2**: Higher power indices ($k=3, 4$) might require extra commutativity or block-diagonal conditions.
   - *Refutation*: We proved by pure ring associativity that $b a^{k+1} = a^k \implies b a^{k+2} = (b a^{k+1}) a = a^k a = a^{k+1}$. Thus, weak Drazin status is monotonically preserved for all $m \ge k$. The theorems compiled with zero additional axioms and zero extra hypotheses.

3. **Adversarial Hypothesis 3**: The index $k=2$ in `weakA` might be arbitrary or reducible.
   - *Refutation*: We proved $\neg \text{IsWeakDrazin weakA weakPolynomialInverse 1}$. Because the nilpotent Jordan block has index 2, $A^2$ collapses the nilpotent lane while $A^1$ preserves it. Thus $k=2$ is the minimal spectral index.

4. **Adversarial Hypothesis 4**: `weakPolynomialInverseUnit` could be a trivial syntactic wrapper without genuine two-sided inversion.
   - *Refutation*: We verified both the group-theoretic laws in `(Mat3 ℚ)ˣ` and the explicit matrix multiplication in `Mat3 ℚ`. Furthermore, we proved that $\det(\text{weakPolynomialInverse}) = 1/8 \ne 0$, whereas the classical Drazin inverse has determinant 0 and cannot possess any two-sided inverse. This formally establishes Campbell & Meyer's theorem that regular polynomial weak inverses can be units in the matrix algebra.

5. **Adversarial Hypothesis 5**: Replacing `native_decide` with explicit tactics could cause kernel typechecking timeouts or memory blowups.
   - *Refutation*: Profiling confirmed that every theorem typechecks in $\le 280\text{ ms}$, with total file compilation requiring $14.91\text{ s}$. The proofs are linear, clean, and well within standard CI tolerances.

---

## 3. Caveats

- The file formalizes the finite algebraic rational packet `diag(2, N₂)` in $M_3(\mathbb{Q})$ rather than arbitrary infinite-dimensional rings or arbitrary field extensions. This is consistent with the module scope declared in lines 30-33.
- Inversion over non-commutative base rings was not tested, as the matrix algebra is formalized over $\mathbb{Q}$.

---

## 4. Conclusion

The refactored file `.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` is **APPROVED**.
- 100% elimination of `native_decide`.
- Kernel-checked proofs using only standard foundational axioms.
- Structurally robust under general unit conjugations ($GL_3$, scaling, shearing, dense) and higher powers ($k=3, 4$).
- Validated two-sided unit properties without tautological bypasses.
- Excellent kernel execution time profile ($\le 280\text{ ms}$ per theorem).

---

## 5. Verification Method

To independently reproduce and verify all results under the build lock:

```bash
# 1. Run the comprehensive stress harness
python3 -c "
import sys, subprocess
from pathlib import Path
sys.path.insert(0, str(Path.cwd()))
from tools.build_lock import acquire_build_lock
with acquire_build_lock(None, 'verify_harness', block=True):
    res = subprocess.run(['lake', 'env', 'lean', '.agents/challenger_weak_drazin_2/StressHarness.lean'], capture_output=True, text=True)
    print('STDOUT:', res.stdout)
    print('STDERR:', res.stderr)
    assert res.returncode == 0
"

# 2. Run the axiom and profiling audit
python3 .agents/challenger_weak_drazin_2/profile_and_axioms.py

# 3. Check sandbox compilation directly
python3 -c "
import sys, subprocess
from pathlib import Path
sys.path.insert(0, str(Path.cwd()))
from tools.build_lock import acquire_build_lock
with acquire_build_lock(None, 'verify_sandbox', block=True):
    res = subprocess.run(['lake', 'env', 'lean', '.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean'], capture_output=True, text=True)
    assert res.returncode == 0
    print('Sandbox compilation clean!')
"
```
