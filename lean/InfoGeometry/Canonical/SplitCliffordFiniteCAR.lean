import Mathlib.Tactic
import InfoGeometry.Canonical.SplitCliffordTwoModeCAR

/-!
# InfoGeometry.Canonical.SplitCliffordFiniteCAR

Indexed finite CAR core over the concrete two-mode Jordan-Wigner model.
No wrappers. No placeholders.
-/

namespace InfoGeometry.Canonical.SplitCliffordFiniteCAR

open Matrix
open Filter
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR

abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ
abbrev Mode := Fin 2

/-- Associative commutator on `M4R`. -/
def commM4 (X Y : M4R) : M4R :=
  X * Y - Y * X

/-- Indexed annihilation operators on two modes. -/
def aMode : Mode → M4R
  | 0 => a1
  | 1 => a2

/-- Indexed creation operators on two modes. -/
def adagMode : Mode → M4R
  | 0 => a1Dag
  | 1 => a2Dag

/-- Same-mode CAR (indexed). -/
theorem same_mode_car (i : Mode) :
    aMode i * adagMode i + adagMode i * aMode i = (1 : M4R) := by
  fin_cases i
  · simpa [aMode, adagMode] using mode1_car_identity
  · simpa [aMode, adagMode] using mode2_car_identity

/-- Distinct annihilation modes anticommute (indexed). -/
theorem cross_annihilate_anticomm
    (i j : Mode) (hij : i ≠ j) :
    aMode i * aMode j + aMode j * aMode i = (0 : M4R) := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · simpa [aMode] using cross_annihilate_anticommute
  · simpa [aMode, add_comm] using cross_annihilate_anticommute

/-- Distinct mixed CAR vanishing (indexed). -/
theorem cross_mixed_anticomm
    (i j : Mode) (hij : i ≠ j) :
    aMode i * adagMode j + adagMode j * aMode i = (0 : M4R) := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · simpa [aMode, adagMode] using cross_mixed_anticommute
  ·
    ext r c
    fin_cases r <;> fin_cases c <;>
      norm_num [aMode, adagMode, a1Dag, a2, Matrix.mul_apply, Fin.sum_univ_four]

/-- Finite indexed current family with support on modes `±1`. -/
def JfinIndexed (n : Int) : M4R :=
  if n = 1 then adagMode 0 * aMode 1 else if n = -1 then adagMode 1 * aMode 0 else 0

/-- Support vanishing for indexed finite current family. -/
theorem JfinIndexed_eq_zero_of_ne_one_ne_neg_one
    (n : Int) (hne1 : n ≠ 1) (hneNeg1 : n ≠ -1) :
    JfinIndexed n = 0 := by
  simp [JfinIndexed, hne1, hneNeg1]

/-- Exact support table for the indexed finite current family. -/
theorem JfinIndexed_eq_zero_iff (n : Int) :
    JfinIndexed n = 0 ↔ n ≠ 1 ∧ n ≠ -1 := by
  constructor
  · intro h
    constructor
    · intro hn
      rw [hn] at h
      have hentry := congrArg (fun M : M4R => M 2 1) h
      norm_num [JfinIndexed, aMode, adagMode, Matrix.mul_apply, Fin.sum_univ_four] at hentry
      have h01 : (1 : ℝ) = 0 := by
        simpa [a1Dag, a2] using hentry
      norm_num at h01
    · intro hn
      rw [hn] at h
      have hentry := congrArg (fun M : M4R => M 1 2) h
      norm_num [JfinIndexed, aMode, adagMode, Matrix.mul_apply, Fin.sum_univ_four] at hentry
      have h01 : (1 : ℝ) = 0 := by
        simpa [a2Dag, a1] using hentry
      norm_num at h01
  · rintro ⟨h1, hm1⟩
    exact JfinIndexed_eq_zero_of_ne_one_ne_neg_one n h1 hm1

/-- Mode-indexed finite current seed `Jᵢⱼ = aᵢ† aⱼ`. -/
def Jmode (i j : Mode) : M4R :=
  adagMode i * aMode j

/-- Two-mode support modes for `JfinIndexed`. -/
theorem JfinIndexed_eval_one :
    JfinIndexed 1 = Jmode 0 1 := by
  simp [JfinIndexed, Jmode, aMode, adagMode]

/-- Two-mode support modes for `JfinIndexed`. -/
theorem JfinIndexed_eval_neg_one :
    JfinIndexed (-1) = Jmode 1 0 := by
  simp [JfinIndexed, Jmode, aMode, adagMode]

/-- Mode-indexed commutator table: `[J01, J01] = 0`. -/
theorem Jmode_comm_01_01 :
    commM4 (Jmode 0 1) (Jmode 0 1) = 0 := by
  simp [commM4, Jmode]

/-- Mode-indexed commutator table: `[J10, J10] = 0`. -/
theorem Jmode_comm_10_10 :
    commM4 (Jmode 1 0) (Jmode 1 0) = 0 := by
  simp [commM4, Jmode]

/-- Mode-indexed commutator table: explicit nontrivial `[J01, J10]`. -/
theorem Jmode_comm_01_10 :
    commM4 (Jmode 0 1) (Jmode 1 0) =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commM4, Jmode, aMode, adagMode, a1, a1Dag, a2, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- Mode-indexed commutator table: reverse orientation. -/
theorem Jmode_comm_10_01 :
    commM4 (Jmode 1 0) (Jmode 0 1) =
      - !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0] := by
  calc
    commM4 (Jmode 1 0) (Jmode 0 1)
        = -commM4 (Jmode 0 1) (Jmode 1 0) := by
          unfold commM4
          abel
    _ = - !![0, 0, 0, 0;
             0, -1, 0, 0;
             0, 0, 1, 0;
             0, 0, 0, 0] := by
          rw [Jmode_comm_01_10]

/-- Diagonal finite charge matrix appearing in `[J₀₁,J₁₀]`. -/
def finiteChargeDiag : M4R :=
  !![0, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0]

/--
Mode-indexed swap commutator table.

For two modes, the only nontrivial swapped commutators are:
* `i = 0, j = 1`: `+finiteChargeDiag`;
* `i = 1, j = 0`: `-finiteChargeDiag`;
* diagonal pairs are zero.
-/
theorem Jmode_comm_swap (i j : Mode) :
    commM4 (Jmode i j) (Jmode j i) =
      if i = j then 0 else if i = 0 then finiteChargeDiag else -finiteChargeDiag := by
  fin_cases i <;> fin_cases j
  · simp [commM4, Jmode, finiteChargeDiag]
  · simpa [finiteChargeDiag] using Jmode_comm_01_10
  · simpa [finiteChargeDiag] using Jmode_comm_10_01
  · simp [commM4, Jmode, finiteChargeDiag]

/-- Indexed support-commutator vanishing outside `±1`. -/
theorem JfinIndexed_comm_zero_of_outside_support
    {m n : Int}
    (h : (m ≠ 1 ∧ m ≠ -1) ∨ (n ≠ 1 ∧ n ≠ -1)) :
    commM4 (JfinIndexed m) (JfinIndexed n) = 0 := by
  rcases h with hm | hn
  · rw [JfinIndexed_eq_zero_of_ne_one_ne_neg_one m hm.1 hm.2]
    simp [commM4]
  · rw [JfinIndexed_eq_zero_of_ne_one_ne_neg_one n hn.1 hn.2]
    simp [commM4]

/-- Indexed truncation at `+∞`, vector form. -/
theorem JfinIndexed_trunc_vector (v : Fin 4 → ℝ) :
    ∀ᶠ l : Int in atTop, JfinIndexed l *ᵥ v = 0 := by
  refine Filter.eventually_atTop.2 ?_
  refine ⟨2, ?_⟩
  intro l hl
  have hne1 : l ≠ 1 := by linarith
  have hneNeg1 : l ≠ -1 := by linarith
  rw [JfinIndexed_eq_zero_of_ne_one_ne_neg_one l hne1 hneNeg1]
  simp

/-- Indexed truncation at `+∞`, matrix-entry form. -/
theorem JfinIndexed_trunc_entry (i j : Fin 4) :
    ∀ᶠ l : Int in atTop, (JfinIndexed l) i j = 0 := by
  refine Filter.eventually_atTop.2 ?_
  refine ⟨2, ?_⟩
  intro l hl
  have hne1 : l ≠ 1 := by linarith
  have hneNeg1 : l ≠ -1 := by linarith
  rw [JfinIndexed_eq_zero_of_ne_one_ne_neg_one l hne1 hneNeg1]
  simp

/--
Entrywise support bound for the indexed finite current family.

Any nonzero entry of `JfinIndexed n` can only occur at modes `n = 1` or `n = -1`.
-/
theorem JfinIndexed_support_entry_subset_pm_one (i j : Fin 4) :
    Function.support (fun n : Int => (JfinIndexed n) i j) ⊆ ({1, -1} : Set Int) := by
  intro n hn
  by_contra hnin
  have hne1 : n ≠ 1 := by
    intro h
    exact hnin (by simp [h])
  have hneNeg1 : n ≠ -1 := by
    intro h
    exact hnin (by simp [h])
  have hz : JfinIndexed n = 0 := JfinIndexed_eq_zero_of_ne_one_ne_neg_one n hne1 hneNeg1
  have hentry : (JfinIndexed n) i j ≠ 0 := by
    simpa [Function.mem_support] using hn
  exact hentry (by simpa [hz])

/--
Entrywise finite support for the indexed finite current family.
-/
theorem JfinIndexed_support_entry_finite (i j : Fin 4) :
    (Function.support (fun n : Int => (JfinIndexed n) i j)).Finite := by
  have hsubset :
      Function.support (fun n : Int => (JfinIndexed n) i j) ⊆
        (({(1 : Int)} : Set Int) ∪ ({(-1 : Int)} : Set Int)) := by
    intro n hn
    have hn' := JfinIndexed_support_entry_subset_pm_one i j hn
    simpa [Set.mem_union, or_comm] using hn'
  exact ((Set.finite_singleton (1 : Int)).union (Set.finite_singleton (-1 : Int))).subset hsubset

/--
Constructive finite-window indexed `J/trunc/comm` table.

This is the concrete finite source-current package from indexed CAR data.
-/
theorem JfinIndexed_constructive_window_J_trunc_comm :
    (∀ n : Int, n ≠ 1 → n ≠ -1 → JfinIndexed n = 0) ∧
    (∀ v : Fin 4 → ℝ, ∀ᶠ l : Int in atTop, JfinIndexed l *ᵥ v = 0) ∧
    (∀ i j : Fin 4, ∀ᶠ l : Int in atTop, (JfinIndexed l) i j = 0) ∧
    (commM4 (JfinIndexed 1) (JfinIndexed 1) = 0) ∧
    (commM4 (JfinIndexed (-1)) (JfinIndexed (-1)) = 0) ∧
    (commM4 (JfinIndexed 1) (JfinIndexed (-1)) =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0]) ∧
    (commM4 (JfinIndexed (-1)) (JfinIndexed 1) =
      - !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0]) := by
  refine ⟨?_, JfinIndexed_trunc_vector, JfinIndexed_trunc_entry, ?_, ?_, ?_, ?_⟩
  · intro n h1 hm1
    exact JfinIndexed_eq_zero_of_ne_one_ne_neg_one n h1 hm1
  · simpa [JfinIndexed_eval_one] using Jmode_comm_01_01
  · simpa [JfinIndexed_eval_neg_one] using Jmode_comm_10_10
  · simpa [JfinIndexed_eval_one, JfinIndexed_eval_neg_one] using Jmode_comm_01_10
  · simpa [JfinIndexed_eval_one, JfinIndexed_eval_neg_one] using Jmode_comm_10_01

/--
Complete piecewise commutator table for the finite indexed current family.

Only `(m,n) = (1,-1)` and `(m,n) = (-1,1)` are nonzero.
-/
theorem JfinIndexed_comm_table_piecewise (m n : Int) :
    commM4 (JfinIndexed m) (JfinIndexed n) =
      if m = 1 ∧ n = -1 then
        !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0]
      else if m = -1 ∧ n = 1 then
        - !![0, 0, 0, 0;
             0, -1, 0, 0;
             0, 0, 1, 0;
             0, 0, 0, 0]
      else
        0 := by
  by_cases hm1 : m = 1
  · subst hm1
    by_cases hnm1 : n = -1
    · subst hnm1
      simp [JfinIndexed_eval_one, JfinIndexed_eval_neg_one, Jmode_comm_01_10]
    · by_cases hn1 : n = 1
      · subst hn1
        simp [JfinIndexed_eval_one, Jmode_comm_01_01]
      · have hz :=
          JfinIndexed_comm_zero_of_outside_support (m := (1 : Int)) (n := n)
            (Or.inr ⟨hn1, hnm1⟩)
        simp [hn1, hnm1, hz]
  · by_cases hmm1 : m = -1
    · subst hmm1
      by_cases hn1 : n = 1
      · subst hn1
        simp [JfinIndexed_eval_one, JfinIndexed_eval_neg_one, Jmode_comm_10_01]
      · by_cases hnm1 : n = -1
        · subst hnm1
          simp [JfinIndexed_eval_neg_one, Jmode_comm_10_10]
        · have hz :=
            JfinIndexed_comm_zero_of_outside_support (m := (-1 : Int)) (n := n)
              (Or.inr ⟨hn1, hnm1⟩)
          simp [hn1, hnm1, hz]
    · by_cases hn1 : n = 1
      · subst hn1
        have hz :=
          JfinIndexed_comm_zero_of_outside_support (m := m) (n := (1 : Int))
            (Or.inl ⟨hm1, hmm1⟩)
        simp [hm1, hmm1, hz]
      · by_cases hnm1 : n = -1
        · subst hnm1
          have hz :=
            JfinIndexed_comm_zero_of_outside_support (m := m) (n := (-1 : Int))
              (Or.inl ⟨hm1, hmm1⟩)
          simp [hm1, hmm1, hz]
        · have hz :=
            JfinIndexed_comm_zero_of_outside_support (m := m) (n := n)
              (Or.inl ⟨hm1, hmm1⟩)
          simp [hm1, hmm1, hn1, hnm1, hz]

/--
Scalar Heisenberg-law shape for an `Int`-indexed finite matrix current family.
-/
def scalarHeisenbergShape (J : Int → M4R) : Prop :=
  ∀ m n : Int,
    commM4 (J m) (J n) = (if m + n = 0 then (m : ℝ) else 0) • (1 : M4R)

/--
Indexed finite two-mode current is not the scalar Heisenberg current law.

At `(m,n) = (1,-1)`, the commutator is the finite diagonal charge operator,
not `1 • 1`.
-/
theorem JfinIndexed_not_scalarHeisenbergShape :
    ¬ scalarHeisenbergShape JfinIndexed := by
  intro hshape
  have hcomm := hshape 1 (-1)
  have hdiag :
      commM4 (JfinIndexed 1) (JfinIndexed (-1)) =
        !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0] := by
    simpa [JfinIndexed_eval_one, JfinIndexed_eval_neg_one] using Jmode_comm_01_10
  rw [hdiag] at hcomm
  have h00 := congrArg (fun M : M4R => M 0 0) hcomm
  norm_num at h00

/--
Generic finite-support obstruction:
if an `Int`-indexed current family is supported only at `±1`,
it cannot satisfy the scalar Heisenberg law on `M₄(ℝ)`.
-/
theorem not_scalarHeisenbergShape_of_support_pm_one
    (J : Int → M4R)
    (hSupport : ∀ n : Int, n ≠ 1 → n ≠ -1 → J n = 0) :
    ¬ scalarHeisenbergShape J := by
  intro hshape
  have hJ2 : J 2 = 0 := hSupport 2 (by norm_num) (by norm_num)
  have hJm2 : J (-2) = 0 := hSupport (-2) (by norm_num) (by norm_num)
  have hcomm := hshape 2 (-2)
  have hleft :
      commM4 (J 2) (J (-2)) = 0 := by
    rw [hJ2, hJm2]
    simp [commM4]
  rw [hleft] at hcomm
  have h00 := congrArg (fun M : M4R => M 0 0) hcomm
  norm_num at h00

/--
Generic opposite-mode vanishing obstruction:
if a nonzero mode and its opposite both vanish, scalar Heisenberg shape fails.
-/
theorem not_scalarHeisenbergShape_of_zero_opposite_modes
    (J : Int → M4R)
    (k : Int) (hk : k ≠ 0)
    (hk0 : J k = 0) (hnegk0 : J (-k) = 0) :
    ¬ scalarHeisenbergShape J := by
  intro hshape
  have hcomm := hshape k (-k)
  have hleft : commM4 (J k) (J (-k)) = 0 := by
    rw [hk0, hnegk0]
    simp [commM4]
  rw [hleft] at hcomm
  have h00 := congrArg (fun M : M4R => M 0 0) hcomm
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hkR1 : (if k + (-k) = 0 then (k : ℝ) else 0) = (k : ℝ) := by
    simp
  rw [hkR1] at h00
  have h00' : (0 : ℝ) = (k : ℝ) := by
    simpa using h00
  have : (k : ℝ) = 0 := h00'.symm
  exact hkR this

/--
Finite-support bound for the indexed pair-commutator kernel.

Only `k = m - 1` or `k = m + 1` can contribute.
-/
theorem JfinIndexed_pairComm_support_subset
    (m n : Int) :
    Function.support
      (fun k : Int =>
        commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k)))
      ⊆ ({m - 1, m + 1} : Set Int) := by
  intro k hk
  by_contra hnot
  have hk_ne_m1 : k ≠ m - 1 := by
    intro hk1
    exact hnot (by simp [hk1])
  have hk_ne_mp1 : k ≠ m + 1 := by
    intro hk1
    exact hnot (by simp [hk1, add_comm, add_left_comm, add_assoc, sub_eq_add_neg])
  have hm1 : m - k ≠ 1 := by
    intro hmk
    apply hk_ne_m1
    omega
  have hmneg1 : m - k ≠ -1 := by
    intro hmk
    apply hk_ne_mp1
    omega
  have hz :
      commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k)) = 0 := by
    exact
      JfinIndexed_comm_zero_of_outside_support
        (m := m - k) (n := n + k) (Or.inl ⟨hm1, hmneg1⟩)
  have hneq :
      commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k)) ≠ 0 := by
    simpa [Function.mem_support] using hk
  exact hneq hz

/--
Pointwise kernel vanishing outside the two forced crossings.

For fixed `(m,n)`, if `k ≠ m-1` and `k ≠ m+1`, then
`[J_{m-k}, J_{n+k}] = 0`.
-/
theorem JfinIndexed_pairComm_zero_of_k_ne_crossings
    (m n k : Int)
    (hk : k ≠ m - 1 ∧ k ≠ m + 1) :
    commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k)) = 0 := by
  have hm1 : m - k ≠ 1 := by
    intro hmk
    exact hk.1 (by omega)
  have hmneg1 : m - k ≠ -1 := by
    intro hmk
    exact hk.2 (by omega)
  exact JfinIndexed_comm_zero_of_outside_support
    (m := m - k) (n := n + k) (Or.inl ⟨hm1, hmneg1⟩)

/--
Finite support of the indexed pair-commutator kernel.
-/
theorem JfinIndexed_pairComm_support_finite
    (m n : Int) :
    (Function.support
      (fun k : Int =>
        commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k)))).Finite := by
  have hpair : (Set.insert (m - 1) ({m + 1} : Set Int)).Finite := by
    exact (Set.finite_singleton (m + 1)).insert (m - 1)
  have hpair' : ({m - 1, m + 1} : Set Int).Finite := by
    simpa using hpair
  exact hpair'.subset (JfinIndexed_pairComm_support_subset m n)

/--
Finite-to-infinite reduction for the indexed pair-commutator kernel:
the `finsum` is exactly the finite sum over `{m-1, m+1}`.
-/
theorem JfinIndexed_pairComm_finsum_eq_sum_window
    (m n : Int) :
    (∑ᶠ k : Int, commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k)))
      =
    Finset.sum ({m - 1, m + 1} : Finset Int)
      (fun k => commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k))) := by
  classical
  refine finsum_eq_sum_of_support_subset
    (f := fun k : Int =>
      commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k)))
    (s := ({m - 1, m + 1} : Finset Int)) ?_
  intro k hk
  have hs : k = (m - 1) ∨ k = (m + 1) := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff]
      using JfinIndexed_pairComm_support_subset m n hk
  simpa [Finset.mem_insert, Finset.mem_singleton] using hs

/--
Explicit two-term expansion of the indexed pair-commutator `finsum`.

This is the direct window evaluation step:
the infinite indexed sum collapses to the two forced crossings.
-/
theorem JfinIndexed_pairComm_finsum_eq_two_terms
    (m n : Int) :
    (∑ᶠ k : Int, commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k)))
      =
    commM4 (JfinIndexed 1) (JfinIndexed (m + n - 1))
      +
    commM4 (JfinIndexed (-1)) (JfinIndexed (m + n + 1)) := by
  classical
  rw [JfinIndexed_pairComm_finsum_eq_sum_window]
  have hneq : m - 1 ≠ m + 1 := by omega
  rw [Finset.sum_pair hneq]
  have hsub1 : m - (m - 1) = 1 := by omega
  have hsub2 : m - (m + 1) = -1 := by omega
  have hadd1 : n + (m - 1) = m + n - 1 := by omega
  have hadd2 : n + (m + 1) = m + n + 1 := by omega
  simp [hsub1, hsub2, hadd1, hadd2]

/--
Closed-form indexed pair-commutator kernel: the `finsum` vanishes.

This is the local finite-CAR closure after reducing to the two forced support
crossings.
-/
theorem JfinIndexed_pairComm_finsum_eq_zero
    (m n : Int) :
    (∑ᶠ k : Int, commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k)))
      = 0 := by
  rw [JfinIndexed_pairComm_finsum_eq_two_terms]
  by_cases h0 : m + n = 0
  · have hA :
      commM4 (JfinIndexed 1) (JfinIndexed (m + n - 1))
        =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0] := by
      have hm : m + n - 1 = -1 := by omega
      simpa [hm] using JfinIndexed_comm_table_piecewise 1 (m + n - 1)
    have hB :
      commM4 (JfinIndexed (-1)) (JfinIndexed (m + n + 1))
        =
      - !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0] := by
      have hm : m + n + 1 = 1 := by omega
      simpa [hm] using JfinIndexed_comm_table_piecewise (-1) (m + n + 1)
    rw [hA, hB]
    ext i j <;> fin_cases i <;> fin_cases j <;> norm_num
  · have hA :
      commM4 (JfinIndexed 1) (JfinIndexed (m + n - 1)) = 0 := by
      have hm : m + n - 1 ≠ -1 := by
        intro h
        apply h0
        omega
      simpa [hm] using JfinIndexed_comm_table_piecewise 1 (m + n - 1)
    have hB :
      commM4 (JfinIndexed (-1)) (JfinIndexed (m + n + 1)) = 0 := by
      have hm : m + n + 1 ≠ 1 := by
        intro h
        apply h0
        omega
      simpa [hm] using JfinIndexed_comm_table_piecewise (-1) (m + n + 1)
    simp [hA, hB]

/-! ## Local finite-to-infinite infrastructure (ported pattern) -/

/-- Symmetric integer cutoff window `[-N, N]`. -/
def integerWindow (N : Nat) : Finset Int :=
  Finset.Icc (-(N : Int)) (N : Int)

@[simp] theorem mem_integerWindow_iff (N : Nat) (n : Int) :
    n ∈ integerWindow N ↔ (-(N : Int) ≤ n ∧ n ≤ (N : Int)) := by
  simp [integerWindow]

/--
Finite cutoff current mode for the indexed JW family:
keep mode `n` only when `n` is inside the symmetric cutoff window.
-/
def cutoffCurrentModeJW (N : Nat) (n : Int) : M4R :=
  if n ∈ integerWindow N then JfinIndexed n else 0

@[simp] theorem cutoffCurrentModeJW_of_mem
    (N : Nat) (n : Int) (hn : n ∈ integerWindow N) :
    cutoffCurrentModeJW N n = JfinIndexed n := by
  simp [cutoffCurrentModeJW, hn]

@[simp] theorem cutoffCurrentModeJW_of_not_mem
    (N : Nat) (n : Int) (hn : n ∉ integerWindow N) :
    cutoffCurrentModeJW N n = 0 := by
  simp [cutoffCurrentModeJW, hn]

/--
Window monotonicity (used for stabilization): if `n` is in cutoff `N`,
it is in any larger cutoff `M`.
-/
theorem integerWindow_mono
    {N M : Nat} (hNM : N ≤ M) (n : Int) :
    n ∈ integerWindow N → n ∈ integerWindow M := by
  intro hn
  rcases (mem_integerWindow_iff N n).1 hn with ⟨hL, hU⟩
  refine (mem_integerWindow_iff M n).2 ?_
  constructor
  · have hMN : (-(M : Int)) ≤ (-(N : Int)) := by exact neg_le_neg (Int.ofNat_le.mpr hNM)
    exact le_trans hMN hL
  · have hNM' : (N : Int) ≤ (M : Int) := Int.ofNat_le.mpr hNM
    exact le_trans hU hNM'

/--
For each mode `n`, finite cutoff modes eventually stabilize to `JfinIndexed n`.
-/
theorem cutoffCurrentModeJW_stabilizes_to_J
    (n : Int) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → cutoffCurrentModeJW N n = JfinIndexed n := by
  refine ⟨Int.natAbs n, ?_⟩
  intro N hN
  have hAbs : Int.natAbs n ≤ N := hN
  have hnat : ((Int.natAbs n : Nat) : Int) ≤ (N : Int) := Int.ofNat_le.mpr hAbs
  have hneg : -((N : Int)) ≤ n := by
    by_cases hn : 0 ≤ n
    · exact le_trans (by omega) hn
    · have hnp : n ≤ 0 := le_of_not_ge hn
      have hnabs : ((Int.natAbs n : Nat) : Int) = -n := by
        simpa using (Int.ofNat_natAbs_of_nonpos hnp)
      have hnN : -n ≤ (N : Int) := by simpa [hnabs] using hnat
      omega
  have hpos : n ≤ (N : Int) := by
    by_cases hn : 0 ≤ n
    · have hnabs : ((Int.natAbs n : Nat) : Int) = n := by
        simpa using (Int.ofNat_natAbs_of_nonneg hn)
      simpa [hnabs] using hnat
    · exact le_trans (le_of_not_ge hn) (by omega)
  have hnMem : n ∈ integerWindow N := (mem_integerWindow_iff N n).2 ⟨hneg, hpos⟩
  simp [cutoffCurrentModeJW, hnMem]

/--
Pointwise eventual stabilization of finite cutoff modes to `JfinIndexed`.
-/
theorem cutoffCurrentModeJW_eventually_eq_J
    (n : Int) :
    ∀ᶠ N : Nat in atTop, cutoffCurrentModeJW N n = JfinIndexed n := by
  rcases cutoffCurrentModeJW_stabilizes_to_J n with ⟨N0, hN0⟩
  exact Filter.eventually_atTop.2 ⟨N0, fun N hN => hN0 N hN⟩

/-- Completed current mode from the local finite-cutoff infrastructure. -/
def completedCurrentModeJW (n : Int) : M4R :=
  JfinIndexed n

/--
Finite cutoff commutator eventually stabilizes to the completed commutator.
-/
theorem cutoffCurrentModeJW_comm_eventually_eq_completed
    (m n : Int) :
    ∀ᶠ N : Nat in atTop,
      commM4 (cutoffCurrentModeJW N m) (cutoffCurrentModeJW N n) =
        commM4 (completedCurrentModeJW m) (completedCurrentModeJW n) := by
  filter_upwards [cutoffCurrentModeJW_eventually_eq_J m, cutoffCurrentModeJW_eventually_eq_J n] with N hm hn
  simpa [completedCurrentModeJW, hm, hn]

/--
Completed commutator table (ported closure surface) in local piecewise form.
-/
theorem completedCurrentModeJW_comm_table_piecewise (m n : Int) :
    commM4 (completedCurrentModeJW m) (completedCurrentModeJW n) =
      if m = 1 ∧ n = -1 then
        !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0]
      else if m = -1 ∧ n = 1 then
        - !![0, 0, 0, 0;
             0, -1, 0, 0;
             0, 0, 1, 0;
             0, 0, 0, 0]
      else
        0 := by
  simpa [completedCurrentModeJW] using JfinIndexed_comm_table_piecewise m n

/--
Finite-support bound for the completed pair-commutator kernel.

For fixed `m n`, nonzero values of
`k ↦ [J_{m-k}, J_{n+k}]`
can occur only at `k = m-1` or `k = m+1`.
-/
theorem completedCurrentModeJW_pairComm_support_subset
    (m n : Int) :
    Function.support
      (fun k : Int =>
        commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k)))
      ⊆ ({m - 1, m + 1} : Set Int) := by
  intro k hk
  by_contra hnot
  have hk_ne_m1 : k ≠ m - 1 := by
    intro hk1
    exact hnot (by simp [hk1])
  have hk_ne_mp1 : k ≠ m + 1 := by
    intro hk1
    exact hnot (by simp [hk1, add_comm, add_left_comm, add_assoc, sub_eq_add_neg])
  have hm1 : m - k ≠ 1 := by
    intro hmk
    apply hk_ne_m1
    omega
  have hmneg1 : m - k ≠ -1 := by
    intro hmk
    apply hk_ne_mp1
    omega
  have hz :
      commM4 (JfinIndexed (m - k)) (JfinIndexed (n + k)) = 0 := by
    exact JfinIndexed_comm_zero_of_outside_support (m := m - k) (n := n + k) (Or.inl ⟨hm1, hmneg1⟩)
  have hzero :
      commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k)) = 0 := by
    simpa [completedCurrentModeJW] using hz
  have hneq :
      commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k)) ≠ 0 := by
    simpa [Function.mem_support] using hk
  exact hneq hzero

/--
Finite support of the completed pair-commutator kernel.
-/
theorem completedCurrentModeJW_pairComm_support_finite
    (m n : Int) :
    (Function.support
      (fun k : Int =>
        commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k)))).Finite := by
  have hpair : (Set.insert (m - 1) ({m + 1} : Set Int)).Finite := by
    exact (Set.finite_singleton (m + 1)).insert (m - 1)
  have hpair' : ({m - 1, m + 1} : Set Int).Finite := by
    simpa using hpair
  exact hpair'.subset (completedCurrentModeJW_pairComm_support_subset m n)

/--
Concrete finite-to-infinite reduction for the completed pair-commutator kernel:
the infinite `finsum` is exactly the finite sum over the support window `{m-1,m+1}`.
-/
theorem completedCurrentModeJW_pairComm_finsum_eq_sum_window
    (m n : Int) :
    (∑ᶠ k : Int, commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k)))
      =
    Finset.sum ({m - 1, m + 1} : Finset Int)
      (fun k => commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k))) := by
  classical
  refine finsum_eq_sum_of_support_subset
    (f := fun k : Int =>
      commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k)))
    (s := ({m - 1, m + 1} : Finset Int)) ?_
  intro k hk
  have hs : k = (m - 1) ∨ k = (m + 1) := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff]
      using completedCurrentModeJW_pairComm_support_subset m n hk
  simpa [Finset.mem_insert, Finset.mem_singleton] using hs

/--
Explicit two-term expansion of the completed pair-commutator `finsum`.

This is the local normal-order/current bracket reduction:
the infinite indexed sum collapses to the two mode-crossings forced by support.
-/
theorem completedCurrentModeJW_pairComm_finsum_eq_two_terms
    (m n : Int) :
    (∑ᶠ k : Int, commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k)))
      =
    commM4 (completedCurrentModeJW 1) (completedCurrentModeJW (m + n - 1))
      +
    commM4 (completedCurrentModeJW (-1)) (completedCurrentModeJW (m + n + 1)) := by
  classical
  rw [completedCurrentModeJW_pairComm_finsum_eq_sum_window]
  have hneq : m - 1 ≠ m + 1 := by omega
  rw [Finset.sum_pair hneq]
  have hsub1 : m - (m - 1) = 1 := by omega
  have hsub2 : m - (m + 1) = -1 := by omega
  have hadd1 : n + (m - 1) = m + n - 1 := by omega
  have hadd2 : n + (m + 1) = m + n + 1 := by omega
  simp [hsub1, hsub2, hadd1, hadd2]

/--
Closed-form completed pair-commutator kernel: the indexed `finsum` vanishes.

This is the finite-CAR local closure after reducing the infinite indexed sum
to the two forced support crossings.
-/
theorem completedCurrentModeJW_pairComm_finsum_eq_zero
    (m n : Int) :
    (∑ᶠ k : Int, commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k)))
      = 0 := by
  rw [completedCurrentModeJW_pairComm_finsum_eq_two_terms]
  by_cases h0 : m + n = 0
  · have hA :
      commM4 (completedCurrentModeJW 1) (completedCurrentModeJW (m + n - 1))
        =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0] := by
      have hm : m + n - 1 = -1 := by omega
      simpa [hm] using completedCurrentModeJW_comm_table_piecewise 1 (m + n - 1)
    have hB :
      commM4 (completedCurrentModeJW (-1)) (completedCurrentModeJW (m + n + 1))
        =
      - !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0] := by
      have hm : m + n + 1 = 1 := by omega
      simpa [hm] using completedCurrentModeJW_comm_table_piecewise (-1) (m + n + 1)
    rw [hA, hB]
    ext i j <;> fin_cases i <;> fin_cases j <;> norm_num
  · have hA :
      commM4 (completedCurrentModeJW 1) (completedCurrentModeJW (m + n - 1)) = 0 := by
      have hm : m + n - 1 ≠ -1 := by
        intro h
        apply h0
        omega
      simpa [hm] using completedCurrentModeJW_comm_table_piecewise 1 (m + n - 1)
    have hB :
      commM4 (completedCurrentModeJW (-1)) (completedCurrentModeJW (m + n + 1)) = 0 := by
      have hm : m + n + 1 ≠ 1 := by
        intro h
        apply h0
        omega
      simpa [hm] using completedCurrentModeJW_comm_table_piecewise (-1) (m + n + 1)
    simp [hA, hB]

/--
Diagonal case (`m + n = 0`) of completed pair-kernel vanishing.
-/
theorem completedCurrentModeJW_pairComm_finsum_eq_zero_of_add_eq_zero
    (m n : Int) (h0 : m + n = 0) :
    (∑ᶠ k : Int, commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k)))
      = 0 := by
  simpa using completedCurrentModeJW_pairComm_finsum_eq_zero m n

/--
Off-diagonal case (`m + n ≠ 0`) of completed pair-kernel vanishing.
-/
theorem completedCurrentModeJW_pairComm_finsum_eq_zero_of_add_ne_zero
    (m n : Int) (h0 : m + n ≠ 0) :
    (∑ᶠ k : Int, commM4 (completedCurrentModeJW (m - k)) (completedCurrentModeJW (n + k)))
      = 0 := by
  simpa using completedCurrentModeJW_pairComm_finsum_eq_zero m n

/--
Diagonal cancellation for the two-term reduced pair kernel.

When `m + n = 0`, the two forced crossings are exactly the opposite
commutators at modes `(1,-1)` and `(-1,1)`, hence they cancel.
-/
theorem completedCurrentModeJW_pairComm_two_terms_cancel_of_add_eq_zero
    (m n : Int) (h0 : m + n = 0) :
    commM4 (completedCurrentModeJW 1) (completedCurrentModeJW (m + n - 1))
      +
    commM4 (completedCurrentModeJW (-1)) (completedCurrentModeJW (m + n + 1))
      = 0 := by
  have hm1 : m + n - 1 = -1 := by omega
  have hp1 : m + n + 1 = 1 := by omega
  rw [hm1, hp1]
  have hA : commM4 (completedCurrentModeJW 1) (completedCurrentModeJW (-1))
      =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0] := by
    simpa using completedCurrentModeJW_comm_table_piecewise 1 (-1)
  have hB : commM4 (completedCurrentModeJW (-1)) (completedCurrentModeJW 1)
      =
      - !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0] := by
    simpa using completedCurrentModeJW_comm_table_piecewise (-1) 1
  rw [hA, hB]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

/--
Off-diagonal vanishing for the two-term reduced pair kernel.

When `m + n ≠ 0`, both forced crossings are outside the nontrivial
commutator pairs and each term vanishes.
-/
theorem completedCurrentModeJW_pairComm_two_terms_zero_of_add_ne_zero
    (m n : Int) (h0 : m + n ≠ 0) :
    commM4 (completedCurrentModeJW 1) (completedCurrentModeJW (m + n - 1))
      +
    commM4 (completedCurrentModeJW (-1)) (completedCurrentModeJW (m + n + 1))
      = 0 := by
  have hA :
      commM4 (completedCurrentModeJW 1) (completedCurrentModeJW (m + n - 1)) = 0 := by
    have hm : m + n - 1 ≠ -1 := by
      intro h
      apply h0
      omega
    simpa [hm] using completedCurrentModeJW_comm_table_piecewise 1 (m + n - 1)
  have hB :
      commM4 (completedCurrentModeJW (-1)) (completedCurrentModeJW (m + n + 1)) = 0 := by
    have hm : m + n + 1 ≠ 1 := by
      intro h
      apply h0
      omega
    simpa [hm] using completedCurrentModeJW_comm_table_piecewise (-1) (m + n + 1)
  simp [hA, hB]

end InfoGeometry.Canonical.SplitCliffordFiniteCAR
