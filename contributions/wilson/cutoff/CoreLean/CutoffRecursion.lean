/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in
/-!
# Finite weighted comparison recursions

A monotone, positively homogeneous operator with a weighted bound is enough
to solve a finite comparison inequality. This is the elementary maximum
argument underlying the weighted norm step of Proposition
`prop:recursion-solution` in the continuum manuscript. A concrete nonnegative
matrix is a useful special case; it need not be symmetric, triangular, or
diagonalizable.

The row estimate and the comparison inequality remain explicit hypotheses.
They must be proved for the actual coupled RG recursion before applying this
lemma to the Wilson observables.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace CoreLean.CutoffRecursion

/-- The finite maximum argument applies to the nonlinear operator described
in the manuscript. Monotonicity and positive homogeneity are needed only
on the nonnegative cone. Only its action on the weight is bounded; the
desired bound on `u` is derived. -/
theorem le_weight_of_monotone_homogeneous
    {ι : Type*} [Finite ι] (T : (ι → ℝ) → ι → ℝ) (u s w : ι → ℝ)
    {θ C : ℝ} (hmono : MonotoneOn T (Set.Ici (0 : ι → ℝ)))
    (hhom : ∀ a : ℝ, 0 ≤ a → ∀ v, 0 ≤ v →
      ∀ i, T (fun j => a * v j) i = a * T v i)
    (hu : ∀ i, 0 ≤ u i)
    (hw : ∀ i, 0 < w i) (hθ : θ < 1)
    (hweight : ∀ i, T w i ≤ θ * w i)
    (hsource : ∀ i, s i ≤ C * w i)
    (hrec : ∀ i, u i ≤ T u i + s i) :
    ∀ i, u i ≤ C / (1 - θ) * w i := by
  classical
  let := Fintype.ofFinite ι
  intro i
  let : Nonempty ι := ⟨i⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
    (fun j => u j / w j) Finset.univ_nonempty
  let M : ℝ := u k / w k
  have hM : 0 ≤ M := div_nonneg (hu k) (hw k).le
  have hbound : ∀ j, u j ≤ M * w j := fun j =>
    (div_le_iff₀ (hw j)).mp (hk j (Finset.mem_univ j))
  have hTu : T u k ≤ M * T w k :=
    (hmono hu (fun j => mul_nonneg hM (hw j).le) hbound k).trans_eq
      (hhom M hM w (fun j => (hw j).le) k)
  have hMk : M * w k = u k := div_mul_cancel₀ _ (hw k).ne'
  have hineq : M * w k ≤ (θ * M + C) * w k := by
    rw [hMk]
    calc
      u k ≤ T u k + s k := hrec k
      _ ≤ M * T w k + C * w k := add_le_add hTu (hsource k)
      _ ≤ M * (θ * w k) + C * w k :=
        add_le_add (mul_le_mul_of_nonneg_left (hweight k) hM) le_rfl
      _ = (θ * M + C) * w k := by ring
  have hMineq : M ≤ θ * M + C := (mul_le_mul_iff_left₀ (hw k)).mp hineq
  have hMfinal : M ≤ C / (1 - θ) := by
    apply (le_div_iff₀ (sub_pos.mpr hθ)).2
    nlinarith
  exact (hbound i).trans (mul_le_mul_of_nonneg_right hMfinal (hw i).le)

/-- A finite nonnegative matrix whose weighted row sums are at most `θ < 1`
gives the resolvent bound `uᵢ ≤ C/(1-θ) · wᵢ` directly from `u ≤ T u + s`.
Monotonicity and homogeneity are proved from its entries. -/
theorem le_weight_of_row_bound
    {ι : Type*} [Fintype ι] (T : ι → ι → ℝ) (u s w : ι → ℝ)
    {θ C : ℝ} (hT : ∀ i j, 0 ≤ T i j) (hu : ∀ i, 0 ≤ u i)
    (hw : ∀ i, 0 < w i) (hθ : θ < 1)
    (hrow : ∀ i, ∑ j, T i j * w j ≤ θ * w i)
    (hsource : ∀ i, s i ≤ C * w i)
    (hrec : ∀ i, u i ≤ ∑ j, T i j * u j + s i) :
    ∀ i, u i ≤ C / (1 - θ) * w i := by
  apply le_weight_of_monotone_homogeneous (fun v i => ∑ j, T i j * v j)
    u s w ?_ ?_ hu hw hθ hrow hsource hrec
  · intro v _ v' _ hv i
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (hT i j)
  · intro a _ v _ i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The quarter-contraction used in the manuscript gives the sharper factor
`4/3`; its stated factor `2` follows immediately. -/
theorem le_two_mul_weight_of_quarter_row_bound
    {ι : Type*} [Fintype ι] (T : ι → ι → ℝ) (u s w : ι → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i j, 0 ≤ T i j) (hu : ∀ i, 0 ≤ u i)
    (hw : ∀ i, 0 < w i)
    (hrow : ∀ i, ∑ j, T i j * w j ≤ (1 / 4 : ℝ) * w i)
    (hsource : ∀ i, s i ≤ C * w i)
    (hrec : ∀ i, u i ≤ ∑ j, T i j * u j + s i) :
    ∀ i, u i ≤ 2 * C * w i := by
  intro i
  have h := le_weight_of_row_bound T u s w hT hu hw (by norm_num : (1 / 4 : ℝ) < 1)
    hrow hsource hrec i
  calc
    u i ≤ C / (1 - (1 / 4 : ℝ)) * w i := h
    _ ≤ 2 * C * w i := by
      apply mul_le_mul_of_nonneg_right _ (hw i).le
      norm_num
      nlinarith

end CoreLean.CutoffRecursion
