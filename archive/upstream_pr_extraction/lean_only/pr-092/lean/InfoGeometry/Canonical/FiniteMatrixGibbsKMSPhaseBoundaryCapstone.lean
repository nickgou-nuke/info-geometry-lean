/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Finite Matrix Carrier Gibbs/KMS Functional & Phase Boundary Capstone

This capstone provides a strictly bounded, theorem-safe formalization of the Gibbs/KMS
state and thermodynamic phase boundary:

1. **Finite Matrix Carrier**:
   - Operates on matrix carrier algebra $\operatorname{Mat}_{N \times N}(\mathbb{R})$ for any finite
     cutoff dimension $N \in \mathbb{N}^+$.
2. **Real Temperature $\beta$ with Hypothesis $1 < \beta$**:
   - Mode energy $E(i) = \ln(i + 1)$, thermal Gibbs weight $w(i, \beta) = (i + 1)^{-\beta} > 0$.
   - Finite partition function $Z_N(\beta) = \sum_{i \in \text{Fin } N} (i + 1)^{-\beta} > 0$.
3. **Finite Normalized Gibbs/KMS Functional**:
   - $\phi_\beta(A) = \frac{1}{Z_N(\beta)} \sum_{i=1}^N A_{ii} (i + 1)^{-\beta}$.
   - Exact normalization: $\phi_\beta(I) = 1$.
   - Positivity on diagonal projections: $\phi_\beta(E_{kk}) = \frac{(k + 1)^{-\beta}}{Z_N(\beta)} > 0$.
4. **Phase Boundary Propositions**:
   - For $1 < \beta$: The infinite partition series $\sum_{n=1}^\infty n^{-\beta}$ converges.
   - For $\beta \le 1$: The infinite partition series $\sum_{n=1}^\infty n^{-\beta}$ diverges,
     strictly marking the critical thermodynamic boundary at $\beta_c = 1$.
5. **Strict Scope**:
   - Contains no unproved claims of complex analytic continuation or infinite Galois family.

All proofs are complete in native Mathlib 4 with 0 `sorry`s, 0 custom axioms, and 0 wrappers.
-/

open scoped BigOperators Real Matrix
open InfoGeometry.Canonical.YangBaxterProof

noncomputable section

namespace InfoGeometry.Canonical.FiniteGibbsKMS

/-- Mode energy: $E(i) = \ln (i + 1)$. -/
def modeEnergy (i : ℕ) : ℝ :=
  Real.log ((i + 1 : ℝ))

/-- Thermal Gibbs weight of mode $i$ at inverse temperature $\beta$:
    $w(i, \beta) = (i + 1)^{-\beta}$. -/
def gibbsWeight (i : ℕ) (β : ℝ) : ℝ :=
  ((i + 1 : ℝ)) ^ (-β)

/-- Finite partition function: $Z_N(\beta) = \sum_{i \in \text{Fin } N} (i + 1)^{-\beta}$. -/
def finitePartitionZ (N : ℕ+) (β : ℝ) : ℝ :=
  ∑ i : Fin N.val, gibbsWeight i.val β

/-- 🏆 THEOREM 1 (Gibbs Weight Positivity):
    The Gibbs weights are strictly positive for all real $\beta$. -/
theorem gibbsWeight_pos (i : ℕ) (β : ℝ) :
    0 < gibbsWeight i β := by
  unfold gibbsWeight
  have h_base : 0 < (i + 1 : ℝ) := by positivity
  exact Real.rpow_pos_of_pos h_base (-β)

/-- 🏆 THEOREM 2 (Finite Partition Function Positivity):
    $Z_N(\beta) > 0$ for all $N \in \mathbb{N}^+$ and $\beta \in \mathbb{R}$. -/
theorem finitePartitionZ_pos (N : ℕ+) (β : ℝ) :
    0 < finitePartitionZ N β := by
  unfold finitePartitionZ
  have i0 : Fin N.val := ⟨0, N.pos⟩
  have h_pos : 0 < gibbsWeight i0.val β := gibbsWeight_pos i0.val β
  have h_nonneg : ∀ i : Fin N.val, 0 ≤ gibbsWeight i.val β := fun i => le_of_lt (gibbsWeight_pos i.val β)
  exact Finset.sum_pos' (fun i _ => h_nonneg i) ⟨i0, Finset.mem_univ i0, h_pos⟩

/-- Finite normalized Gibbs/KMS functional on matrix carrier $\operatorname{Mat}_{N \times N}(\mathbb{R})$. -/
def finiteGibbsState (N : ℕ+) (β : ℝ) (A : Matrix (Fin N.val) (Fin N.val) ℝ) : ℝ :=
  (∑ i : Fin N.val, A i i * gibbsWeight i.val β) / finitePartitionZ N β

/-- 🏆 THEOREM 3 (State Normalization on Identity Matrix):
    $\phi_\beta(I) = 1$. -/
theorem finiteGibbsState_one (N : ℕ+) (β : ℝ) :
    finiteGibbsState N β (1 : Matrix (Fin N.val) (Fin N.val) ℝ) = 1 := by
  unfold finiteGibbsState
  have h_tr : (∑ i : Fin N.val, (1 : Matrix (Fin N.val) (Fin N.val) ℝ) i i * gibbsWeight i.val β) = finitePartitionZ N β := by
    unfold finitePartitionZ
    apply Finset.sum_congr rfl
    intro i _
    simp [Matrix.one_apply_eq]
  rw [h_tr]
  have hZ_pos := finitePartitionZ_pos N β
  exact div_self (ne_of_gt hZ_pos)

/-- 🏆 THEOREM 4 (Positivity on Diagonal Projection Operators):
    $\phi_\beta(E_{kk}) = \frac{(k+1)^{-\beta}}{Z_N(\beta)} > 0$. -/
theorem finiteGibbsState_diag_proj (N : ℕ+) (β : ℝ) (k : Fin N.val) :
    0 < finiteGibbsState N β (Matrix.diagonal (fun i => if i = k then 1 else 0)) := by
  unfold finiteGibbsState
  have h_eval : (∑ i : Fin N.val, Matrix.diagonal (fun j => if j = k then (1 : ℝ) else 0) i i * gibbsWeight i.val β) = gibbsWeight k.val β := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik
      simp [Matrix.diagonal_apply_eq, hik]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  rw [h_eval]
  have hw_pos := gibbsWeight_pos k.val β
  have hZ_pos := finitePartitionZ_pos N β
  exact div_pos hw_pos hZ_pos

/-- 🏆 THEOREM 5 (Low Temperature Summability: $1 < \beta$):
    The infinite series $\sum_{n=1}^\infty n^{-\beta}$ converges for $1 < \beta$. -/
theorem low_temp_summable_prop (β : ℝ) (hβ : 1 < β) :
    Summable (fun n : ℕ => ((n : ℝ) ^ β)⁻¹) :=
  Real.summable_nat_rpow_inv.mpr hβ

/-- 🏆 THEOREM 6 (Phase Boundary Divergence: $\beta \le 1$):
    The infinite series $\sum_{n=1}^\infty n^{-\beta}$ diverges for $\beta \le 1$ (Phase Boundary). -/
theorem phase_boundary_diverges_prop (β : ℝ) (hβ : β ≤ 1) :
    ¬ Summable (fun n : ℕ => ((n : ℝ) ^ β)⁻¹) := by
  intro h_sum
  have h_gt : 1 < β := Real.summable_nat_rpow_inv.mp h_sum
  exact not_lt_of_ge hβ h_gt

/--
🏆 **MASTER SYNTHESIS: Finite Matrix Gibbs/KMS & Phase Boundary**

Unifies:
1. **Gibbs State Normalization**: $\phi_\beta(I) = 1$.
2. **Diagonal Projection Positivity**: $\phi_\beta(E_{kk}) > 0$.
3. **Low-Temperature Convergence**: $\sum n^{-\beta} < \infty$ for $1 < \beta$.
4. **Phase Boundary Divergence**: $\neg \text{Summable}(n^{-1})$ at $\beta = 1$.
5. **Yang-Baxter Topological Integrability**: $F \cdot B \cdot F = R$ and $F^2 = 1$.
-/
theorem grand_finite_matrix_gibbs_kms_synthesis
    (N : ℕ+) (β : ℝ) (hβ : 1 < β) (k : Fin N.val) :
    (finiteGibbsState N β (1 : Matrix (Fin N.val) (Fin N.val) ℝ) = 1) ∧
    (0 < finiteGibbsState N β (Matrix.diagonal (fun i => if i = k then 1 else 0))) ∧
    (Summable (fun n : ℕ => ((n : ℝ) ^ β)⁻¹)) ∧
    (¬ Summable (fun n : ℕ => ((n : ℝ) ^ (1 : ℝ))⁻¹)) ∧
    (F * F = 1) ∧
    (F * B * F = R) :=
  ⟨finiteGibbsState_one N β,
   finiteGibbsState_diag_proj N β k,
   low_temp_summable_prop β hβ,
   phase_boundary_diverges_prop 1 le_rfl,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.FiniteGibbsKMS
