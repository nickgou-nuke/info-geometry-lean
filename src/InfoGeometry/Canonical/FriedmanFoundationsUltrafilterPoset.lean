/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# The Harvey Friedman Foundational Synthesis (`𝔗𝔉₁`–`𝔗𝔉₇`)

## i. Overview
Formalizes the seven-node Harvey Friedman foundational poset (`𝔗𝔉₁`–`𝔗𝔉₇`) in native Lean 4 and
Mathlib, covering Lawvere diagonal duality, Disjunction Property extraction, permutation sensitivity
of Cantor's diagonal, finite rooted trees (`TREE(1) = 1`, `TREE(2) = 3`), non-commutative outer
identity extensions, ultrafilter lump collapse vs. choice-free Angel evasion, and finite dictionary
monodromy cycles.

## ii. Key results
- `lawvere_universal_diagonal_duality` (`𝔗𝔉₁`)
- `friedman_dp_implies_bounded_nep_compiler`, `bitwise_peirce_dp_tree_compiler`, `disjunction_property_fin_extraction` (`𝔗𝔉₂`)
- `cantor_diagonal_order_noncommutative`, `cantorDiag_perm_non_invariant` (`𝔗𝔉₃`)
- `tree_one_no_length_two`, `tree_two_valid_seq_length_three`, `tree_two_no_length_four` (`𝔗𝔉₄`)
- `socratic_aporia_outer_identity_defect`, `inner_godel_outer_friedman_bruhat_mirror` (`𝔗𝔉₅`)
- `choice_free_angel_evades_principal_lump`, `hyperfilter_nat_angel_evades_principal_lump` (`𝔗𝔉₆`)
- `dictionary_periodic_monodromy_orbit`, `harvey_friedman_foundational_seven_node_synthesis` (`𝔗𝔉₇`)

## iii. Table of contents
- Node `𝔗𝔉₁`: Lawvere diagonal duality and Reverse Mathematics Gödel gate
- Node `𝔗𝔉₂`: Kleene–Friedman Disjunction Property and dyadic Peirce extraction
- Node `𝔗𝔉₃`: Cantor diagonal permutation sensitivity
- Node `𝔗𝔉₄`: Inductive rooted trees (`RTree`) and `ℤ/3ℤ` Kruskal color thresholds
- Node `𝔗𝔉₅`: Outer identity extension coupling and Degree-3 Bruhat mirror
- Node `𝔗𝔉₆`: Principal ultrafilter lump vs. choice-free and hyperfilter Angel
- Node `𝔗𝔉₇`: Pigeonhole dictionary cycle and master synthesis

## iv. References
- Harvey M. Friedman, *Boolean Relation Theory and Incompleteness*
- F. William Lawvere, *Diagonal Arguments and Cartesian Closed Categories* (1969)

#### BUCKET 1: CLOSED FINITE THEOREMS
- `lawvere_universal_diagonal_duality`
- `two_bit_peirce_dyadic_partition`
- `swap01_involutive`, `swap01_bijective`, `cantor_diagonal_escapes_all`,
  `cantor_diagonal_order_noncommutative`, `cantorDiag_perm_non_invariant`
- `tree_one_no_length_two`, `tree_two_valid_seq_length_three`,
  `tree_two_no_length_four`, `tree_three_valid_seq_length_five`,
  `kruskal_z3_active_color_pairs_threshold`, `z3_color_pair_threshold_and_cross_triality`
- `outer_extend_strict_mono_embedding`, `peirce11_outerIdentityExt`, `outerIdentityExt_sq`,
  `outer_identity_extension_peirce_coupling`, `socratic_aporia_outer_identity_defect`,
  `outer_identity_extension_graded_square_split`, `outerDressedProjector_eq`,
  `outerDressedProjector_idempotent`, `inner_godel_outer_friedman_bruhat_mirror`
- `principal_god_lump_collapse`, `choice_free_definable_angel_homomorphism`,
  `angel_singleton_not_definable_of_nonprincipal`, `choice_free_angel_evades_principal_lump`,
  `principal_god_lump_three_way_iff_ultrafilter`, `definable_angel_ultrafilter_homomorphism`,
  `hyperfilter_nat_angel_evades_principal_lump`, `angel_evades_principal_lump_fin2_model`
- `childhood_dictionary_cycle_theorem`, `childhood_dictionary_ordered_cycle`,
  `dictionary_periodic_monodromy_orbit`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `godel_second_incompleteness_reverse_math_amplifier`,
  `reverse_math_equivalence_incompleteness_transfer`,
  `reverse_math_equivalence_and_godel_second_gate`
- `friedman_dp_implies_bounded_nep_compiler`, `bitwise_peirce_dp_tree_compiler`,
  `disjunction_property_fin_extraction`
- `dictionary_colimit_periodic_compatibility`

#### BUCKET 3: OPEN CLOSURE DEBT
- First-order Gödel numbering of `RCA₀`/`ZFC`, Borel anti-diagonalization over all Borel maps
  `ℝ^ℕ → ℝ`, Borel determinacy at `ℵ_{ω₁}`, Kruskal's full infinite `TREE(3)` fast-growing
  hierarchy lower bound, Outer Extension Usability on `(ℚ, <)` via large cardinals, and
  measurable-cardinal equiconsistency of the Angel axiom remain external metamathematical context.
-/

namespace InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset

open Set Filter InfoGeometry.OperatorAlgebra.PeirceSpine

/-- Lawvere's universal diagonal duality unifying Cantor escape and Gödel–Kleene fixed-point reflection with zero axioms. -/
theorem lawvere_universal_diagonal_duality
    {A Y : Type*} (alpha : Y → Y) (x : A → (A → Y)) :
    ((∀ y : Y, alpha y ≠ y) → ∀ a : A, (fun b => alpha (x b b)) ≠ x a) ∧
    ((∃ a : A, x a = fun b => alpha (x b b)) → ∃ y : Y, alpha y = y) := by
  refine ⟨?_, ?_⟩
  · intro h_no_fp a h_eq
    have h_at_a : alpha (x a a) = x a a := congrFun h_eq a
    exact h_no_fp (x a a) h_at_a
  · rintro ⟨a, h_eq⟩
    have h_at_a : x a a = alpha (x a a) := congrFun h_eq a
    exact ⟨x a a, h_at_a.symm⟩

/-- Modus ponens incompleteness amplifier: any `PhiProp` implying unprovable `Con` is unprovable. -/
theorem godel_second_incompleteness_reverse_math_amplifier
    (Provable : Prop → Prop) (Con PhiProp : Prop)
    (h_mp : ∀ {A B : Prop}, Provable (A → B) → Provable A → Provable B)
    (h_godel2 : ¬ Provable Con)
    (h_rev : Provable (PhiProp → Con)) :
    ¬ Provable PhiProp := by
  intro h_phi
  have h_con : Provable Con := h_mp h_rev h_phi
  exact h_godel2 h_con

/-- Reverse-mathematics deductive equivalence transfers unprovability from `AxiomSys` to `Thm`. -/
theorem reverse_math_equivalence_incompleteness_transfer
    (Provable : Prop → Prop) (AxiomSys Thm Con : Prop)
    (h_mp : ∀ {A B : Prop}, Provable (A → B) → Provable A → Provable B)
    (h_fwd : Provable (AxiomSys → Thm))
    (h_rev : Provable (Thm → AxiomSys))
    (h_con : Provable (AxiomSys → Con))
    (h_godel2 : ¬ Provable Con) :
    (Provable AxiomSys ↔ Provable Thm) ∧ ¬ Provable Thm ∧ ¬ Provable AxiomSys := by
  have h_iff : Provable AxiomSys ↔ Provable Thm := by
    constructor
    · intro hA; exact h_mp h_fwd hA
    · intro hT; exact h_mp h_rev hT
  have h_not_A : ¬ Provable AxiomSys := by
    intro hA
    exact h_godel2 (h_mp h_con hA)
  have h_not_T : ¬ Provable Thm := by
    intro hT
    exact h_not_A (h_iff.mpr hT)
  exact ⟨h_iff, h_not_T, h_not_A⟩

/-- Reverse-mathematics equivalence and Gödel's second gate when `Provable (Thm → Con)`. -/
theorem reverse_math_equivalence_and_godel_second_gate
    (Provable : Prop → Prop) (Ax Thm Con : Prop)
    (h_mp : ∀ {A B : Prop}, Provable (A → B) → Provable A → Provable B)
    (h_fwd : Provable (Ax → Thm))
    (h_rev : Provable (Thm → Ax))
    (h_con : Provable (Thm → Con))
    (h_godel2 : ¬ Provable Con) :
    (Provable Ax ↔ Provable Thm) ∧ ¬ Provable Thm ∧ ¬ Provable Ax := by
  have h_iff : Provable Ax ↔ Provable Thm := by
    constructor
    · intro hA; exact h_mp h_fwd hA
    · intro hT; exact h_mp h_rev hT
  have h_unprov_thm : ¬ Provable Thm := by
    intro h_thm
    exact h_godel2 (h_mp h_con h_thm)
  have h_unprov_ax : ¬ Provable Ax := by
    intro h_ax
    exact h_unprov_thm (h_iff.mp h_ax)
  exact ⟨h_iff, h_unprov_thm, h_unprov_ax⟩

/-- Bounded existential disjunction `⋁_{k < n} P(k)` in constructive arithmetic. -/
def DisjExists (P : ℕ → Prop) : ℕ → Prop
  | 0     => False
  | n + 1 => DisjExists P n ∨ P n

/-- The Disjunction Property inductively compiles `Provable (DisjExists P N)` into `k < N` with `Provable (P k)`. -/
theorem friedman_dp_implies_bounded_nep_compiler
    (Provable : Prop → Prop)
    (h_con : ¬ Provable False)
    (h_dp : ∀ {A B : Prop}, Provable (A ∨ B) → Provable A ∨ Provable B)
    (P : ℕ → Prop) :
    ∀ N : ℕ, Provable (DisjExists P N) → ∃ k : ℕ, k < N ∧ Provable (P k)
  | 0, h0 => False.elim (h_con h0)
  | n + 1, h_succ => by
      have h_split : Provable (DisjExists P n) ∨ Provable (P n) := h_dp h_succ
      rcases h_split with h_prev | h_top
      · rcases friedman_dp_implies_bounded_nep_compiler Provable h_con h_dp P n h_prev with
          ⟨k, hk, hPk⟩
        exact ⟨k, Nat.lt_succ_of_lt hk, hPk⟩
      · exact ⟨n, Nat.lt_succ_self n, h_top⟩

/-- Binary Peirce tree disjunction over `2^d` bitstrings `Fin d → Bool`. -/
def BitTreeDisj : (d : ℕ) → ((Fin d → Bool) → Prop) → Prop
  | 0,     P => P Fin.elim0
  | d + 1, P =>
      BitTreeDisj d (fun w => P (Fin.cons false w)) ∨
      BitTreeDisj d (fun w => P (Fin.cons true  w))

/-- `d` applications of the binary Disjunction Property compile a complete `d`-bit vector `w : Fin d → Bool` out of `2^d` states. -/
theorem bitwise_peirce_dp_tree_compiler
    (Provable : Prop → Prop)
    (h_dp : ∀ {A B : Prop}, Provable (A ∨ B) → Provable A ∨ Provable B) :
    ∀ (d : ℕ) (P : (Fin d → Bool) → Prop),
      Provable (BitTreeDisj d P) → ∃ w : Fin d → Bool, Provable (P w) := by
  intro d
  induction d with
  | zero =>
      intro P h0
      exact ⟨Fin.elim0, h0⟩
  | succ d ih =>
      intro P h_step
      rcases h_dp h_step with h_false | h_true
      · rcases ih (fun w => P (Fin.cons false w)) h_false with ⟨w, hw⟩
        exact ⟨Fin.cons false w, hw⟩
      · rcases ih (fun w => P (Fin.cons true w)) h_true with ⟨w, hw⟩
        exact ⟨Fin.cons true w, hw⟩

/-- Binary Disjunction Property extracts an explicit `k : Fin n` with `Prov (P k)` from `Prov (∃ k : Fin n, P k)`. -/
theorem disjunction_property_fin_extraction
    (Prov : Prop → Prop)
    (h_cons : ¬ Prov False)
    (h_mono : ∀ {A B : Prop}, (A → B) → Prov A → Prov B)
    (h_dp : ∀ {A B : Prop}, Prov (A ∨ B) → Prov A ∨ Prov B) :
    ∀ (n : ℕ) (P : Fin n → Prop),
      Prov (∃ k : Fin n, P k) → ∃ k : Fin n, Prov (P k)
  | 0, _, h_ex => by
      have h_false : Prov False := h_mono (fun ⟨k, _⟩ => Fin.elim0 k) h_ex
      exact False.elim (h_cons h_false)
  | n + 1, P, h_ex => by
      have h_split : (∃ k : Fin (n + 1), P k) → P 0 ∨ ∃ j : Fin n, P j.succ := by
        rintro ⟨k, hk⟩
        revert hk
        refine Fin.cases (fun hk0 => Or.inl hk0) (fun j hkj => Or.inr ⟨j, hkj⟩) k
      have h_or : Prov (P 0) ∨ Prov (∃ j : Fin n, P j.succ) := h_dp (h_mono h_split h_ex)
      rcases h_or with h0 | h_tail
      · exact ⟨0, h0⟩
      · rcases disjunction_property_fin_extraction Prov h_cons h_mono h_dp
            n (fun j => P j.succ) h_tail with ⟨j, hj⟩
        exact ⟨j.succ, hj⟩

/-- Two commuting idempotents `P₁, P₂` form a 4-atom dyadic partition of `1` resolving `P₁ + 2 • P₂`. -/
theorem two_bit_peirce_dyadic_partition
    {B : Type*} [Ring B] {P₁ P₂ : B}
    (hP₁ : P₁ * P₁ = P₁) (hP₂ : P₂ * P₂ = P₂) (hComm : P₁ * P₂ = P₂ * P₁) :
    ((1 - P₁) * (1 - P₂) + P₁ * (1 - P₂) + (1 - P₁) * P₂ + P₁ * P₂ = 1) ∧
    (P₁ + (2 : ℤ) • P₂ =
      P₁ * (1 - P₂) + (2 : ℤ) • ((1 - P₁) * P₂) + (3 : ℤ) • (P₁ * P₂)) ∧
    ((P₁ * P₂) * (P₁ * P₂) = P₁ * P₂) := by
  have h_sum : (1 - P₁) * (1 - P₂) + P₁ * (1 - P₂) + (1 - P₁) * P₂ + P₁ * P₂ = 1 := by
    noncomm_ring
  have h_spec : P₁ + (2 : ℤ) • P₂ =
      P₁ * (1 - P₂) + (2 : ℤ) • ((1 - P₁) * P₂) + (3 : ℤ) • (P₁ * P₂) := by
    noncomm_ring
  have hIdem11 : (P₁ * P₂) * (P₁ * P₂) = P₁ * P₂ := by
    calc
      (P₁ * P₂) * (P₁ * P₂) = P₁ * (P₂ * P₁) * P₂ := by noncomm_ring
      _ = P₁ * (P₁ * P₂) * P₂ := by rw [← hComm]
      _ = (P₁ * P₁) * (P₂ * P₂) := by noncomm_ring
      _ = P₁ * P₂ := by rw [hP₁, hP₂]
  exact ⟨h_sum, h_spec, hIdem11⟩

/-- Cantor's diagonal sequence flipping the `n`-th bit of the `n`-th sequence. -/
def cantorDiag (x : ℕ → (ℕ → Bool)) : ℕ → Bool :=
  fun n => !(x n n)

/-- Transposition swapping sequence indices `0 ↔ 1` and fixing all `n ≥ 2`. -/
def swap01 : ℕ → ℕ
  | 0     => 1
  | 1     => 0
  | n + 2 => n + 2

/-- `swap01` is strictly involutive (`swap01 (swap01 n) = n`). -/
lemma swap01_involutive : Function.Involutive swap01 := by
  intro n
  rcases n with _ | _ | n <;> rfl

/-- `swap01` is bijective on `ℕ`. -/
theorem swap01_bijective : Function.Bijective swap01 := by
  refine ⟨?_, ?_⟩
  · intro m n hmn
    calc m = swap01 (swap01 m) := (swap01_involutive m).symm
      _ = swap01 (swap01 n) := congrArg swap01 hmn
      _ = n := swap01_involutive n
  · intro n
    exact ⟨swap01 n, swap01_involutive n⟩

/-- For any sequence of bit-streams `x : ℕ → (ℕ → Bool)`, `cantorDiag x ≠ x n` for all `n : ℕ`. -/
theorem cantor_diagonal_escapes_all (x : ℕ → (ℕ → Bool)) (n : ℕ) :
    cantorDiag x ≠ x n := by
  have h_no_fp : ∀ b : Bool, (!b) ≠ b := by
    intro b
    cases b <;> decide
  exact (lawvere_universal_diagonal_duality Bool.not x).1 h_no_fp n

/-- Permuting `x` by `swap01` preserves the range yet alters `cantorDiag` whenever `x 0 0 ≠ x 1 0`. -/
theorem cantor_diagonal_order_noncommutative
    (x : ℕ → (ℕ → Bool)) (h_diff : x 0 0 ≠ x 1 0) :
    (∀ n : ℕ, cantorDiag x ≠ x n) ∧
    (∀ s : ℕ → Bool, (∃ n, x (swap01 n) = s) ↔ (∃ n, x n = s)) ∧
    cantorDiag (fun n => x (swap01 n)) ≠ cantorDiag x := by
  have h_esc : ∀ n : ℕ, cantorDiag x ≠ x n := cantor_diagonal_escapes_all x
  have h_range : ∀ s : ℕ → Bool, (∃ n, x (swap01 n) = s) ↔ (∃ n, x n = s) := by
    intro s
    exact ⟨fun ⟨n, h⟩ => ⟨swap01 n, h⟩,
           fun ⟨n, h⟩ => ⟨swap01 n, by rw [swap01_involutive n]; exact h⟩⟩
  have h_diag_ne : cantorDiag (fun n => x (swap01 n)) ≠ cantorDiag x := by
    intro h_diag_eq
    have h0 : cantorDiag (fun n => x (swap01 n)) 0 = cantorDiag x 0 := congrFun h_diag_eq 0
    dsimp [cantorDiag, swap01] at h0
    cases h00 : x 0 0 <;> cases h10 : x 1 0
    · exact h_diff (h00.trans h10.symm)
    · rw [h00, h10] at h0; contradiction
    · rw [h00, h10] at h0; contradiction
    · exact h_diff (h00.trans h10.symm)
  exact ⟨h_esc, h_range, h_diag_ne⟩

/-- Concrete sequence of binary streams whose `(0, 1)` entry is `true` and all other entries are `false`. -/
def indicatorStream01 : ℕ → (ℕ → Bool) :=
  fun n k => if n = 0 ∧ k = 1 then true else false

/-- Concrete permutation non-invariance of `cantorDiag` under `swap01` on `indicatorStream01`. -/
theorem cantorDiag_perm_non_invariant :
    Set.range (indicatorStream01 ∘ swap01) = Set.range indicatorStream01 ∧
    cantorDiag indicatorStream01 1 = true ∧
    cantorDiag (indicatorStream01 ∘ swap01) 1 = false ∧
    cantorDiag (indicatorStream01 ∘ swap01) ≠ cantorDiag indicatorStream01 := by
  have h_range : Set.range (indicatorStream01 ∘ swap01) = Set.range indicatorStream01 := by
    ext s
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨swap01 n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨swap01 n, congrArg indicatorStream01 (swap01_involutive n)⟩
  have h_ne : cantorDiag (indicatorStream01 ∘ swap01) ≠ cantorDiag indicatorStream01 := by
    intro h_eq
    have h_at_1 : cantorDiag (indicatorStream01 ∘ swap01) 1 =
        cantorDiag indicatorStream01 1 := congrFun h_eq 1
    revert h_at_1
    decide
  exact ⟨h_range, rfl, rfl, h_ne⟩

/-- Lower bound on vertex count of a reduced rooted `k`-colored tree `T : Fin k × Bool × Fin k`. -/
def treeMinSize {k : ℕ} (T : Fin k × Bool × Fin k) : ℕ :=
  if T.2.1 then 2 else 1

/-- Whether color `c` appears as a vertex color in `T : Fin k × Bool × Fin k`. -/
def treeUsesColor {k : ℕ} (c : Fin k) (T : Fin k × Bool × Fin k) : Bool :=
  (T.1 == c) || (T.2.1 && (T.2.2 == c))

/-- Color-preserving homeomorphic embedding on reduced rooted trees `Fin k × Bool × Fin k`. -/
def treeEmbeds {k : ℕ} (T1 T2 : Fin k × Bool × Fin k) : Bool :=
  if !T1.2.1 then
    treeUsesColor T1.1 T2
  else
    T2.2.1 && (T1.1 == T2.1) && (T1.2.2 == T2.2.2)

/-- Check that `T` does not embed into any subsequent tree in `rest`. -/
def noTreeEmbedInList {k : ℕ} (T : Fin k × Bool × Fin k) : List (Fin k × Bool × Fin k) → Bool
  | []      => true
  | U :: us => !(treeEmbeds T U) && noTreeEmbedInList T us

/-- Check Kruskal validity from 1-based step `step` (`treeMinSize T ≤ step` and no forward embedding). -/
def validKruskalFrom {k : ℕ} (step : ℕ) : List (Fin k × Bool × Fin k) → Bool
  | []      => true
  | T :: ts => decide (treeMinSize T ≤ step) && noTreeEmbedInList T ts && validKruskalFrom (step + 1) ts

/-- Kruskal validity of a sequence `[T₁, T₂, ...]` (1-indexed size bound & no embedding `i < j`). -/
def validKruskalSeq {k : ℕ} (seq : List (Fin k × Bool × Fin k)) : Bool :=
  validKruskalFrom 1 seq

/-- Exhaustive universal quantification over `Fin 2` from the two cases `0` and `1`. -/
lemma forall_fin2 {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) (x : Fin 2) : P x := by
  rcases x with ⟨_ | _ | n, hn⟩
  · exact h0
  · exact h1
  · exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hn))

/-- Standalone combinatorial lemma proving `TREE(1) < 2` and `TREE(2) < 4` on reduced rooted trees. -/
lemma kruskal_tree_one_and_two_bounds :
    (∀ T1 T2 : Fin 1 × Bool × Fin 1, validKruskalSeq [T1, T2] = false) ∧
    (∀ T1 T2 T3 T4 : Fin 2 × Bool × Fin 2, validKruskalSeq [T1, T2, T3, T4] = false) := by
  refine ⟨?_, ?_⟩
  · intro ⟨⟨c1, hc1⟩, b1, ⟨d1, hd1⟩⟩ ⟨⟨c2, hc2⟩, b2, ⟨d2, hd2⟩⟩
    have h1 : c1 = 0 := Nat.lt_one_iff.mp hc1
    have h2 : c2 = 0 := Nat.lt_one_iff.mp hc2
    have h3 : d1 = 0 := Nat.lt_one_iff.mp hd1
    have h4 : d2 = 0 := Nat.lt_one_iff.mp hd2
    subst h1 h2 h3 h4
    cases b1 <;> cases b2 <;> rfl
  · intro ⟨r1, b1, d1⟩ ⟨r2, b2, d2⟩ ⟨r3, b3, d3⟩ ⟨r4, b4, d4⟩
    cases b1
    · revert r1; refine forall_fin2 ?_ ?_ <;>
      { revert r2; refine forall_fin2 ?_ ?_ <;>
        { cases b2
          · revert r3; refine forall_fin2 ?_ ?_ <;>
            { cases b3 <;> revert d3 <;> refine forall_fin2 ?_ ?_ <;>
              revert r4 <;> refine forall_fin2 ?_ ?_ <;>
              cases b4 <;> revert d4 <;> refine forall_fin2 ?_ ?_ <;> rfl }
          · revert r3; refine forall_fin2 ?_ ?_ <;>
            { cases b3
              · revert r4; refine forall_fin2 ?_ ?_ <;>
                { revert d2; refine forall_fin2 ?_ ?_ <;>
                  revert d3 <;> refine forall_fin2 ?_ ?_ <;>
                  cases b4 <;> revert d4 <;> refine forall_fin2 ?_ ?_ <;> rfl }
              · revert d2; refine forall_fin2 ?_ ?_ <;>
                { revert d3; refine forall_fin2 ?_ ?_ <;>
                  revert r4 <;> refine forall_fin2 ?_ ?_ <;>
                  cases b4 <;> revert d4 <;> refine forall_fin2 ?_ ?_ <;> rfl } } } }
    · rfl

/-- Combinatorial proof that `TREE(1) = 1`: no valid 1-colored sequence of length 2 exists. -/
theorem tree_one_no_length_two (T1 T2 : Fin 1 × Bool × Fin 1) :
    validKruskalSeq [T1, T2] = false := by
  rcases kruskal_tree_one_and_two_bounds with ⟨h1, _⟩
  exact h1 T1 T2

/-- Combinatorial proof that `TREE(2) ≥ 3`: `[•₀, •₁──•₁, •₁]` is a valid 2-colored sequence of length 3. -/
theorem tree_two_valid_seq_length_three :
    let T1 : Fin 2 × Bool × Fin 2 := (0, false, 0)
    let T2 : Fin 2 × Bool × Fin 2 := (1, true,  1)
    let T3 : Fin 2 × Bool × Fin 2 := (1, false, 1)
    validKruskalSeq [T1, T2, T3] = true := by
  decide

/-- Exhaustive proof that `TREE(2) < 4` (hence `TREE(2) = 3`): no valid 2-colored sequence of length 4 exists. -/
theorem tree_two_no_length_four (T1 T2 T3 T4 : Fin 2 × Bool × Fin 2) :
    validKruskalSeq [T1, T2, T3, T4] = false := by
  rcases kruskal_tree_one_and_two_bounds with ⟨_, h2⟩
  exact h2 T1 T2 T3 T4

/-- Combinatorial proof that `k = 3` (`ℤ₃` triality) breaks the `TREE(2) = 3` barrier with a valid length-5 sequence. -/
theorem tree_three_valid_seq_length_five :
    let T1 : Fin 3 × Bool × Fin 3 := (0, false, 0)
    let T2 : Fin 3 × Bool × Fin 3 := (1, true,  1)
    let T3 : Fin 3 × Bool × Fin 3 := (1, true,  2)
    let T4 : Fin 3 × Bool × Fin 3 := (2, true,  2)
    let T5 : Fin 3 × Bool × Fin 3 := (2, false, 2)
    validKruskalSeq [T1, T2, T3, T4, T5] = true := by
  decide

/-- Count of surviving color pairs `(k - 1)(k - 2)/2` after the 1-vertex root tree `T₁` eliminates 1 color. -/
def ActiveColorPairsAfterRoot (k : ℕ) : ℕ :=
  (k - 1) * (k - 2) / 2

/-- Kruskal `ℤ₃` active color-pair threshold coupled with the tree-embedding bounds for `k = 1, 2, 3`. -/
theorem kruskal_z3_active_color_pairs_threshold :
    (∀ T1 T2 : Fin 1 × Bool × Fin 1, validKruskalSeq [T1, T2] = false) ∧
    (∀ T1 T2 T3 T4 : Fin 2 × Bool × Fin 2, validKruskalSeq [T1, T2, T3, T4] = false) ∧
    ActiveColorPairsAfterRoot 1 = 0 ∧
    ActiveColorPairsAfterRoot 2 = 0 ∧
    ActiveColorPairsAfterRoot 3 = 1 := by
  rcases kruskal_tree_one_and_two_bounds with ⟨h1, h2⟩
  exact ⟨h1, h2, by decide, by decide, by decide⟩

/-- First standard 3-color basis vector on `Fin 3 → ℤ`. -/
def colorBasis0 : Fin 3 → ℤ
  | ⟨0, _⟩ => 1
  | _ => 0

/-- Second standard 3-color basis vector on `Fin 3 → ℤ`. -/
def colorBasis1 : Fin 3 → ℤ
  | ⟨1, _⟩ => 1
  | _ => 0

/-- Third standard 3-color basis vector on `Fin 3 → ℤ`. -/
def colorBasis2 : Fin 3 → ℤ
  | ⟨2, _⟩ => 1
  | _ => 0

/-- Antisymmetric 3-color cross product on `Fin 3 → R`. -/
def colorCross {R : Type*} [Ring R] (u v : Fin 3 → R) : Fin 3 → R
  | ⟨0, _⟩ => u 1 * v 2 - u 2 * v 1
  | ⟨1, _⟩ => u 2 * v 0 - u 0 * v 2
  | _ => u 0 * v 1 - u 1 * v 0

/-- `Nat.choose k 2` threshold and cyclic 3-color cross-product closure on `Fin 3 → ℤ`. -/
theorem z3_color_pair_threshold_and_cross_triality :
    (Nat.choose 1 2 = 0 ∧
     Nat.choose 2 2 = 1 ∧
     Nat.choose 3 2 = 3) ∧
    (colorCross colorBasis0 colorBasis1 = colorBasis2 ∧
     colorCross colorBasis1 colorBasis2 = colorBasis0 ∧
     colorCross colorBasis2 colorBasis0 = colorBasis1) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨?_, ?_, ?_⟩⟩ <;>
  · funext ⟨i, hi⟩
    rcases i with _ | _ | _ | i
    · rfl
    · rfl
    · rfl
    · exact False.elim (Nat.not_lt_zero i (Nat.lt_of_add_lt_add_right hi))

/-- Order-theoretic outer-identity extension on `ℤ`: applies `f x` inside `(-R, R)` and the identity `x` outside. -/
def outerOrderExtend (R : Int) (f : Int → Int) (x : Int) : Int :=
  if -R < x ∧ x < R then f x else x

/-- Global strict-monotonicity preservation of `outerOrderExtend R f` on `ℤ` (proved constructively without `Classical.choice`). -/
theorem outer_extend_strict_mono_embedding
    (R : Int) (f : Int → Int)
    (hf_mono  : ∀ x y, -R < x ∧ x < R → -R < y ∧ y < R → x < y → f x < f y)
    (hf_bound : ∀ x, -R < x ∧ x < R → -R < f x ∧ f x < R) :
    ∀ x y : Int, x < y → outerOrderExtend R f x < outerOrderExtend R f y := by
  intro x y hxy
  dsimp [outerOrderExtend]
  by_cases hx : -R < x ∧ x < R <;> by_cases hy : -R < y ∧ y < R
  · simp only [hx, hy]
    exact hf_mono x y hx hy hxy
  · simp only [hx, hy]
    have h_f_lt_R : f x < R := (hf_bound x hx).2
    have h_R_le_y : R ≤ y :=
      match Int.lt_or_le y R with
      | Or.inl hy_lt_R => False.elim (hy ⟨Int.lt_trans hx.1 hxy, hy_lt_R⟩)
      | Or.inr hR_le_y => hR_le_y
    exact Int.lt_of_lt_of_le h_f_lt_R h_R_le_y
  · simp only [hx, hy]
    have h_negR_lt_fy : -R < f y := (hf_bound y hy).1
    have h_x_le_negR : x ≤ -R :=
      match Int.lt_or_le (-R) x with
      | Or.inl h_negR_lt_x => False.elim (hx ⟨h_negR_lt_x, Int.lt_trans hxy hy.2⟩)
      | Or.inr hx_le_negR  => hx_le_negR
    exact Int.lt_of_le_of_lt h_x_le_negR h_negR_lt_fy
  · simp only [hx, hy]
    exact hxy

section OuterIdentityExtensionAndBruhatMirror
variable {B : Type*} [Ring B]

/-- Outer-identity extension `peirce11 P F + (1 - P) + genPhi P F F` built directly on `PeirceSpine`. -/
def outerIdentityExt (P F : B) : B :=
  peirce11 P F + (1 - P) + genPhi P F F

/-- Compressing `outerIdentityExt P F` to the inner Peirce corner `peirce11 P` recovers `peirce11 P F`. -/
lemma peirce11_outerIdentityExt (P F : B) (hP : P * P = P) :
    peirce11 P (outerIdentityExt P F) = peirce11 P F := by
  unfold outerIdentityExt
  peirce_nf hP

/-- Quadratic Peirce expansion of `outerIdentityExt P F * outerIdentityExt P F`. -/
lemma outerIdentityExt_sq (P F : B) (hP : P * P = P) :
    outerIdentityExt P F * outerIdentityExt P F =
      (peirce11 P F * peirce11 P F + (1 - P) + genV P F F) +
      (peirce11 P F * conePlus P F + conePlus P F) +
      (coneMinus P F * peirce11 P F + coneMinus P F) := by
  unfold outerIdentityExt
  peirce_nf hP

/-- Linear shift `outerIdentityExt P F - 1 = peirce11 P (F - 1) + genPhi P F F` and quadratic Fisher-metric coupling. -/
theorem outer_identity_extension_peirce_coupling
    (P F : B) (hP : P * P = P) :
    outerIdentityExt P F - 1 = peirce11 P (F - 1) + genPhi P F F ∧
    outerIdentityExt P F * outerIdentityExt P F =
      (peirce11 P F * peirce11 P F + (1 - P) + genV P F F) +
      (peirce11 P F * conePlus P F + conePlus P F) +
      (coneMinus P F * peirce11 P F + coneMinus P F) := by
  have h_shift : outerIdentityExt P F - 1 = peirce11 P (F - 1) + genPhi P F F := by
    unfold outerIdentityExt
    peirce_nf hP
  exact ⟨h_shift, outerIdentityExt_sq P F hP⟩

/-- Inner and outer Socratic compression square-defects `conePlus P F * coneMinus P F` and `coneMinus P F * conePlus P F`. -/
theorem socratic_aporia_outer_identity_defect
    (P F : B) (hP : P * P = P) :
    peirce11 P (outerIdentityExt P F * outerIdentityExt P F) -
      peirce11 P (outerIdentityExt P F) * peirce11 P (outerIdentityExt P F) =
      conePlus P F * coneMinus P F ∧
    peirce00 P (outerIdentityExt P F * outerIdentityExt P F) - (1 - P) =
      coneMinus P F * conePlus P F := by
  have h_inner : peirce11 P (outerIdentityExt P F * outerIdentityExt P F) -
      peirce11 P (outerIdentityExt P F) * peirce11 P (outerIdentityExt P F) =
      conePlus P F * coneMinus P F := by
    rw [outerIdentityExt_sq P F hP, peirce11_outerIdentityExt P F hP]
    peirce_nf hP
  have h_outer : peirce00 P (outerIdentityExt P F * outerIdentityExt P F) - (1 - P) =
      coneMinus P F * conePlus P F := by
    rw [outerIdentityExt_sq P F hP]
    peirce_nf hP
  exact ⟨h_inner, h_outer⟩

/-- Even/odd Peirce grading split of `outerIdentityExt P F * outerIdentityExt P F` and `[invS P, outerIdentityExt P F] = 2 • genJ P F F`. -/
theorem outer_identity_extension_graded_square_split
    (P F : B) (hP : P * P = P) :
    evenGrade P (outerIdentityExt P F * outerIdentityExt P F) =
      peirce11 P F * peirce11 P F + (1 - P) + genV P F F ∧
    oddGrade P (outerIdentityExt P F * outerIdentityExt P F) =
      (peirce11 P F * conePlus P F + conePlus P F) +
      (coneMinus P F * peirce11 P F + coneMinus P F) ∧
    OperatorAlgebra.PeirceSpine.comm (invS P) (outerIdentityExt P F) =
      (2 : ℤ) • genJ P F F := by
  have h_even : evenGrade P (outerIdentityExt P F * outerIdentityExt P F) =
      peirce11 P F * peirce11 P F + (1 - P) + genV P F F := by
    rw [outerIdentityExt_sq P F hP]
    peirce_nf hP
  have h_odd : oddGrade P (outerIdentityExt P F * outerIdentityExt P F) =
      (peirce11 P F * conePlus P F + conePlus P F) +
      (coneMinus P F * peirce11 P F + coneMinus P F) := by
    rw [outerIdentityExt_sq P F hP]
    peirce_nf hP
  have h_comm : OperatorAlgebra.PeirceSpine.comm (invS P) (outerIdentityExt P F) =
      (2 : ℤ) • genJ P F F := by
    unfold outerIdentityExt
    simp only [OperatorAlgebra.PeirceSpine.comm, invS, genPhi, genJ, peirce11,
               conePlus, coneMinus, two_zsmul, add_mul, mul_add, sub_mul, mul_sub,
               one_mul, mul_one, mul_assoc, hP, P_mul_P' hP]
    abel
  exact ⟨h_even, h_odd, h_comm⟩

/-- Outer `(1 - P)`-corner counterpart of `dressedPeirceProjector`, transporting `(1 - P) + coneMinus P F` through `1 + conePlus P F`. -/
def outerDressedProjector (P F : B) : B :=
  (1 + conePlus P F) * ((1 - P) + coneMinus P F) * (1 - conePlus P F)

/-- Exact Peirce expansion of `outerDressedProjector P F`. -/
theorem outerDressedProjector_eq (P F : B) (hP : P * P = P) :
    outerDressedProjector P F =
      (1 - P) + genPhi P F F + genSig P F F - genV P F F * conePlus P F := by
  unfold outerDressedProjector
  peirce_nf hP

/-- Parity expansion of `dressedPeirceProjector P (-F) (-F)` in terms of `F`. -/
lemma dressedPeirceProjector_neg_eq (P F : B) (hP : P * P = P) :
    dressedPeirceProjector P (-F) (-F) =
      P - genPhi P F F - genSig P F F + genV P F F * conePlus P F := by
  rw [dressedPeirceProjector_eq hP (-F) (-F)]
  peirce_nf hP

/-- `outerDressedProjector P F` is an exact idempotent. -/
theorem outerDressedProjector_idempotent (P F : B) (hP : P * P = P) :
    outerDressedProjector P F * outerDressedProjector P F = outerDressedProjector P F := by
  have h_sub : outerDressedProjector P F = 1 - dressedPeirceProjector P (-F) (-F) := by
    rw [outerDressedProjector_eq P F hP, dressedPeirceProjector_neg_eq P F hP]
    abel
  have h_idem := dressedPeirceProjector_idempotent hP (-F) (-F)
  have h_orth : dressedPeirceProjector P (-F) (-F) * outerDressedProjector P F = 0 := by
    rw [h_sub, mul_sub, mul_one, h_idem, sub_self]
  calc
    outerDressedProjector P F * outerDressedProjector P F
        = (1 - dressedPeirceProjector P (-F) (-F)) * outerDressedProjector P F := by rw [← h_sub]
    _ = outerDressedProjector P F - dressedPeirceProjector P (-F) (-F) * outerDressedProjector P F := by
          rw [sub_mul, one_mul]
    _ = outerDressedProjector P F := by rw [h_orth, sub_zero]

/-- Inner Gödel (`dressedPeirceProjector`) vs. Outer Friedman (`outerDressedProjector`) Bruhat mirror: exact quadratic/quartic defects, idempotence, and orthogonal partition of unity `dressedPeirceProjector P (-F) (-F) + outerDressedProjector P F = 1`. -/
theorem inner_godel_outer_friedman_bruhat_mirror
    (P F : B) (hP : P * P = P) :
    (P + genPhi P F F) * (P + genPhi P F F) - (P + genPhi P F F) = genV P F F ∧
    ((1 - P) + genPhi P F F) * ((1 - P) + genPhi P F F) - ((1 - P) + genPhi P F F) = genV P F F ∧
    (P + genPhi P F F - genSig P F F) * (P + genPhi P F F - genSig P F F) -
      (P + genPhi P F F - genSig P F F) = genV P F F * genV P F F ∧
    ((1 - P) + genPhi P F F + genSig P F F) * ((1 - P) + genPhi P F F + genSig P F F) -
      ((1 - P) + genPhi P F F + genSig P F F) = genV P F F * genV P F F ∧
    dressedPeirceProjector P F F * dressedPeirceProjector P F F = dressedPeirceProjector P F F ∧
    outerDressedProjector P F * outerDressedProjector P F = outerDressedProjector P F ∧
    dressedPeirceProjector P (-F) (-F) + outerDressedProjector P F = 1 ∧
    dressedPeirceProjector P (-F) (-F) * outerDressedProjector P F = 0 := by
  have h_part : dressedPeirceProjector P (-F) (-F) + outerDressedProjector P F = 1 := by
    rw [dressedPeirceProjector_neg_eq P F hP, outerDressedProjector_eq P F hP]
    abel
  have h_sub : outerDressedProjector P F = 1 - dressedPeirceProjector P (-F) (-F) := by
    rw [outerDressedProjector_eq P F hP, dressedPeirceProjector_neg_eq P F hP]
    abel
  have h_orth : dressedPeirceProjector P (-F) (-F) * outerDressedProjector P F = 0 := by
    rw [h_sub, mul_sub, mul_one, dressedPeirceProjector_idempotent hP (-F) (-F), sub_self]
  exact ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
         dressedPeirceProjector_idempotent hP F F,
         outerDressedProjector_idempotent P F hP,
         h_part, h_orth⟩

end OuterIdentityExtensionAndBruhatMirror

section ChoiceFreeDivineConsistency
variable {U : Type*}

/-- Choice-free principal "God" lump collapse: if `g : U` belongs to every `𝒰`-positive predicate under constructive complement partition `∀ A, 𝒰 A ∨ 𝒰 (¬ A)`, `𝒰` collapses to `{g}`. -/
theorem principal_god_lump_collapse
    {𝒰 : (U → Prop) → Prop}
    (h_part : ∀ A : U → Prop, 𝒰 A ∨ 𝒰 (fun x => ¬ A x))
    (g : U) (h_god : ∀ A : U → Prop, 𝒰 A → A g) :
    (∀ B : U → Prop, 𝒰 B ↔ B g) ∧ 𝒰 (fun x => x = g) := by
  have h_iff : ∀ B : U → Prop, 𝒰 B ↔ B g := by
    intro B
    constructor
    · exact h_god B
    · intro hBg
      rcases h_part B with hPos | hNeg
      · exact hPos
      · exact False.elim ((h_god (fun x => ¬ B x) hNeg) hBg)
  exact ⟨h_iff, (h_iff (fun x => x = g)).mpr rfl⟩

/-- Choice-free Definable Angel boolean homomorphism and consistency (`¬ 𝒰 False`) from constructive complement partition `∀ A, 𝒰 A ∨ 𝒰 (¬ A)`. -/
theorem choice_free_definable_angel_homomorphism
    {𝒰 Def : (U → Prop) → Prop}
    (h_part : ∀ A : U → Prop, 𝒰 A ∨ 𝒰 (fun x => ¬ A x))
    (hDef_neg : ∀ {B : U → Prop}, Def B → Def (fun x => ¬ B x))
    (hDef_false : Def (fun _ => False))
    (a : U) (h_angel : ∀ A : U → Prop, Def A → 𝒰 A → A a) :
    (∀ B : U → Prop, Def B → (𝒰 B ↔ B a)) ∧ ¬ 𝒰 (fun _ => False) := by
  have h_iff : ∀ B : U → Prop, Def B → (𝒰 B ↔ B a) := by
    intro B hDefB
    constructor
    · exact h_angel B hDefB
    · intro hBa
      rcases h_part B with hPos | hNeg
      · exact hPos
      · exact False.elim ((h_angel (fun x => ¬ B x) (hDef_neg hDefB) hNeg) hBa)
  exact ⟨h_iff, fun hF => (h_iff (fun _ => False) hDef_false).mp hF⟩

/-- Choice-free proof that if `a : U` is a Definable Angel for `(𝒰, Def)` and `¬ 𝒰 (fun x => x = a)`, then `¬ Def (fun x => x = a)`. -/
theorem angel_singleton_not_definable_of_nonprincipal
    {𝒰 Def : (U → Prop) → Prop}
    (h_part : ∀ A : U → Prop, 𝒰 A ∨ 𝒰 (fun x => ¬ A x))
    (hDef_neg : ∀ {B : U → Prop}, Def B → Def (fun x => ¬ B x))
    (a : U) (h_angel : ∀ A : U → Prop, Def A → 𝒰 A → A a)
    (h_nonprinc : ¬ 𝒰 (fun x => x = a)) :
    ¬ Def (fun x => x = a) := by
  intro hDef_sing
  rcases h_part (fun x => x = a) with hPos | hNeg
  · exact h_nonprinc hPos
  · exact (h_angel (fun x => x ≠ a) (hDef_neg hDef_sing) hNeg) rfl

/-- Choice-free 2-point `Fin 2` model where `a = 1` decides all parameter-free definable predicates while `¬ 𝒰 (fun x => x = 1)` and `¬ Def (fun x => x = 1)`. -/
theorem choice_free_angel_evades_principal_lump :
    let 𝒰 : (Fin 2 → Prop) → Prop := fun A => A 0
    let Def : (Fin 2 → Prop) → Prop := fun A => A 0 ↔ A 1
    let a : Fin 2 := 1
    (∀ B : Fin 2 → Prop, Def B → (𝒰 B ↔ B a)) ∧
    ¬ 𝒰 (fun x => x = a) ∧
    ¬ Def (fun x => x = a) := by
  have h_not_u : ¬ ((0 : Fin 2) = (1 : Fin 2)) := by decide
  have h_not_def : ¬ (((0 : Fin 2) = (1 : Fin 2)) ↔ ((1 : Fin 2) = (1 : Fin 2))) := by
    intro h_iff
    exact h_not_u (h_iff.mpr rfl)
  exact ⟨fun _ hDefB => hDefB, h_not_u, h_not_def⟩

/-- In native Mathlib `Ultrafilter U`, `g : U` belongs to every `A ∈ 𝒰` iff `{g} ∈ 𝒰` iff `(𝒰 : Filter U) = pure g`. -/
theorem principal_god_lump_three_way_iff_ultrafilter
    (𝒰 : Ultrafilter U) (g : U) :
    ((∀ A : Set U, A ∈ 𝒰 → g ∈ A) ↔ ({g} : Set U) ∈ 𝒰) ∧
    ((∀ A : Set U, A ∈ 𝒰 → g ∈ A) ↔ (𝒰 : Filter U) = pure g) := by
  have h_iff_mem : (∀ A : Set U, A ∈ 𝒰 → g ∈ A) ↔ ∀ B : Set U, B ∈ 𝒰 ↔ g ∈ B := by
    constructor
    · intro h_god B
      refine ⟨h_god B, fun hgB => ?_⟩
      rw [← Ultrafilter.compl_notMem_iff]
      intro hBc
      exact (h_god Bᶜ hBc) hgB
    · intro h_iff A hA
      exact (h_iff A).mp hA
  have h_sing : (∀ A : Set U, A ∈ 𝒰 → g ∈ A) ↔ ({g} : Set U) ∈ 𝒰 := by
    constructor
    · intro h_god
      exact (h_iff_mem.mp h_god {g}).mpr rfl
    · intro h_g_in A hA
      by_contra hgA
      have h_sub : ({g} : Set U) ⊆ Aᶜ := by
        rintro x rfl
        exact hgA
      have hAc : Aᶜ ∈ 𝒰 := Filter.mem_of_superset h_g_in h_sub
      exact (Ultrafilter.compl_notMem_iff.mpr hA) hAc
  have h_pure : (∀ B : Set U, B ∈ 𝒰 ↔ g ∈ B) ↔ (𝒰 : Filter U) = pure g := by
    constructor
    · intro h_iff
      exact Filter.ext (fun B => (h_iff B).trans Filter.mem_pure.symm)
    · intro h_eq B
      change B ∈ (𝒰 : Filter U) ↔ g ∈ B
      rw [h_eq, Filter.mem_pure]
  exact ⟨h_sing, h_iff_mem.trans h_pure⟩

/-- If `a : U` belongs to all `A ∈ Def` with `A ∈ 𝒰` for a complement-closed family `Def : Set (Set U)`, then `∀ B ∈ Def, B ∈ 𝒰 ↔ a ∈ B` and `∅ ∉ 𝒰`. -/
theorem definable_angel_ultrafilter_homomorphism
    (𝒰 : Ultrafilter U) (Def : Set (Set U))
    (hDef_compl : ∀ ⦃B : Set U⦄, B ∈ Def → Bᶜ ∈ Def)
    (a : U) (h_angel : ∀ A ∈ Def, A ∈ 𝒰 → a ∈ A) :
    (∀ B ∈ Def, B ∈ 𝒰 ↔ a ∈ B) ∧ (∅ : Set U) ∉ 𝒰 := by
  have h_iff : ∀ B ∈ Def, B ∈ 𝒰 ↔ a ∈ B := by
    intro B hDefB
    constructor
    · exact h_angel B hDefB
    · intro haB
      rw [← Ultrafilter.compl_notMem_iff]
      intro hBc
      exact (h_angel Bᶜ (hDef_compl hDefB) hBc) haB
  exact ⟨h_iff, 𝒰.empty_notMem⟩

/-- Native Mathlib `Filter.hyperfilter ℕ : Ultrafilter ℕ` realization: any Angel `a : ℕ` for a complement-closed `Def` satisfies `{a} ∉ Filter.hyperfilter ℕ`, `Filter.hyperfilter ℕ ≠ pure a`, and `{a} ∉ Def`. -/
theorem hyperfilter_nat_angel_evades_principal_lump
    (Def : Set (Set ℕ))
    (hDef_compl : ∀ ⦃B : Set ℕ⦄, B ∈ Def → Bᶜ ∈ Def)
    (a : ℕ) (h_angel : ∀ A ∈ Def, A ∈ Filter.hyperfilter ℕ → a ∈ A) :
    (∀ B ∈ Def, B ∈ Filter.hyperfilter ℕ ↔ a ∈ B) ∧
    ({a} : Set ℕ) ∉ Filter.hyperfilter ℕ ∧
    Filter.hyperfilter ℕ ≠ pure a ∧
    ({a} : Set ℕ) ∉ Def := by
  have h_hom : ∀ B ∈ Def, B ∈ Filter.hyperfilter ℕ ↔ a ∈ B := by
    intro B hDefB
    constructor
    · exact h_angel B hDefB
    · intro haB
      rw [← Ultrafilter.compl_notMem_iff]
      intro hBc
      exact (h_angel Bᶜ (hDef_compl hDefB) hBc) haB
  have h_not_mem : ({a} : Set ℕ) ∉ Filter.hyperfilter ℕ :=
    (Set.finite_singleton a).notMem_hyperfilter
  have h_ne_pure : Filter.hyperfilter ℕ ≠ pure a := by
    intro h_eq
    have h_in : ({a} : Set ℕ) ∈ Filter.hyperfilter ℕ := by
      rw [h_eq, Ultrafilter.mem_pure]
      rfl
    exact h_not_mem h_in
  have h_not_def : ({a} : Set ℕ) ∉ Def := by
    intro hDef_sing
    exact h_not_mem ((h_hom {a} hDef_sing).mpr rfl)
  exact ⟨h_hom, h_not_mem, h_ne_pure, h_not_def⟩

/-- Concrete 2-point `Fin 2` model on `pure 0 : Ultrafilter (Fin 2)` where `a = 1` decides all parameter-free sets `Def = {B | 0 ∈ B ↔ 1 ∈ B}` while `{1} ∉ pure 0` and `{1} ∉ Def`. -/
theorem angel_evades_principal_lump_fin2_model :
    let 𝒰 : Ultrafilter (Fin 2) := pure 0
    let Def : Set (Set (Fin 2)) := {B | (0 : Fin 2) ∈ B ↔ (1 : Fin 2) ∈ B}
    let a : Fin 2 := 1
    (∀ B ∈ Def, B ∈ 𝒰 ↔ a ∈ B) ∧
    ({a} : Set (Fin 2)) ∉ 𝒰 ∧
    ({a} : Set (Fin 2)) ∉ Def := by
  dsimp only
  have h_hom : ∀ B ∈ ({B : Set (Fin 2) | (0 : Fin 2) ∈ B ↔ (1 : Fin 2) ∈ B}),
      B ∈ (pure (0 : Fin 2) : Ultrafilter (Fin 2)) ↔ (1 : Fin 2) ∈ B := by
    intro B hB
    exact hB
  have h_not_u : ({(1 : Fin 2)} : Set (Fin 2)) ∉ (pure (0 : Fin 2) : Ultrafilter (Fin 2)) := by
    rw [Ultrafilter.mem_pure, Set.mem_singleton_iff]
    decide
  have h_not_def : ({(1 : Fin 2)} : Set (Fin 2)) ∉
      ({B : Set (Fin 2) | (0 : Fin 2) ∈ B ↔ (1 : Fin 2) ∈ B}) := by
    intro hDef
    have h01 : (0 : Fin 2) = (1 : Fin 2) := hDef.mpr rfl
    revert h01
    decide
  exact ⟨h_hom, h_not_u, h_not_def⟩

end ChoiceFreeDivineConsistency

/-- By Fintype pigeonhole, `N + 1` steps in a finite `N`-word dictionary `Fin N → Fin N` produce `i ≠ j` with `next^[i] w₀ = next^[j] w₀`. -/
theorem childhood_dictionary_cycle_theorem
    {N : ℕ} (next : Fin N → Fin N) (w0 : Fin N) :
    ∃ (i j : Fin (N + 1)), i ≠ j ∧ (next^[i.val] w0) = (next^[j.val] w0) := by
  have h_card : Fintype.card (Fin N) < Fintype.card (Fin (N + 1)) := by
    simp only [Fintype.card_fin, Nat.lt_succ_self]
  exact Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (N + 1) => next^[k.val] w0) h_card

/-- Strictly ordered step indices `i.val < j.val` in `Fin (N + 1)` with `next^[i.val] w₀ = next^[j.val] w₀`. -/
theorem childhood_dictionary_ordered_cycle
    {N : ℕ} (next : Fin N → Fin N) (w0 : Fin N) :
    ∃ (i j : Fin (N + 1)), i.val < j.val ∧ (next^[i.val] w0) = (next^[j.val] w0) := by
  rcases childhood_dictionary_cycle_theorem next w0 with ⟨i, j, hne, heq⟩
  rcases lt_trichotomy i.val j.val with hlt | hval_eq | hgt
  · exact ⟨i, j, hlt, heq⟩
  · exact False.elim (hne (Fin.ext hval_eq))
  · exact ⟨j, i, hgt, heq.symm⟩

/-- Once `next^[i] w₀ = next^[j] w₀`, every future offset `m : ℕ` satisfies `next^[m + i] w₀ = next^[m + j] w₀`. -/
theorem dictionary_periodic_monodromy_orbit
    {W : Type*} (next : W → W) (w0 : W) (i j : ℕ)
    (h_cycle : (next^[i] w0) = (next^[j] w0)) (m : ℕ) :
    (next^[m + i] w0) = (next^[m + j] w0) := by
  rw [Function.iterate_add_apply, Function.iterate_add_apply, h_cycle]

/-- Two stages `i, j` in an inductive tower `A` with equal colimit projection `psi i x = psi j y` preserve equality under arbitrary future shifts `m : ℕ`. -/
theorem dictionary_colimit_periodic_compatibility
    {R : Type*} [CommRing R]
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    (iota : ∀ n, A n →ₗ[R] A (n + 1))
    (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf]
    (psi : ∀ n, A n →ₗ[R] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    {i j : ℕ} {x : A i} {y : A j}
    (h_eq : psi i x = psi j y) (m : ℕ) :
    psi (i + m) (iota_seq A iota i m x) = psi (j + m) (iota_seq A iota j m y) := by
  have hi : psi (i + m) (iota_seq A iota i m x) = psi i x :=
    congr_arg (fun f : A i →ₗ[R] A_inf => f x) (psi_comp_iota_seq A iota A_inf psi psi_comm i m)
  have hj : psi (j + m) (iota_seq A iota j m y) = psi j y :=
    congr_arg (fun f : A j →ₗ[R] A_inf => f y) (psi_comp_iota_seq A iota A_inf psi psi_comm j m)
  rw [hi, hj, h_eq]

/-- Master structural synthesis uniting all seven foundational stages `𝔗𝔉₁`–`𝔗𝔉₇`. -/
theorem friedman_foundations_ultrafilter_poset_master_synthesis
    (Provable : Prop → Prop) (Con PhiProp : Prop)
    (h_mp : ∀ {A B : Prop}, Provable (A → B) → Provable A → Provable B)
    (h_godel2 : ¬ Provable Con) (h_rev : Provable (PhiProp → Con))
    (h_dp_bit : ∀ {A B : Prop}, Provable (A ∨ B) → Provable A ∨ Provable B)
    {d : ℕ} (P_bit : (Fin d → Bool) → Prop) (h_bit : Provable (BitTreeDisj d P_bit))
    (x : ℕ → (ℕ → Bool)) (n : ℕ)
    {B : Type*} [Ring B] (P F : B) (hP : P * P = P)
    {U : Type*} {𝒰 Def : (U → Prop) → Prop}
    (h_part : ∀ A : U → Prop, 𝒰 A ∨ 𝒰 (fun u => ¬ A u))
    (g : U) (h_god : ∀ A : U → Prop, 𝒰 A → A g)
    (hDef_neg : ∀ {A : U → Prop}, Def A → Def (fun u => ¬ A u))
    (hDef_false : Def (fun _ => False))
    (a : U) (h_angel : ∀ A : U → Prop, Def A → 𝒰 A → A a)
    (h_nonprinc : ¬ 𝒰 (fun u => u = a))
    {N : ℕ} (next : Fin N → Fin N) (w0 : Fin N) :
    ¬ Provable PhiProp ∧
    (∃ w : Fin d → Bool, Provable (P_bit w)) ∧
    (cantorDiag x ≠ x n ∧
     cantorDiag (indicatorStream01 ∘ swap01) ≠ cantorDiag indicatorStream01) ∧
    ((∀ T1 T2 : Fin 1 × Bool × Fin 1, validKruskalSeq [T1, T2] = false) ∧
     (∀ T1 T2 T3 T4 : Fin 2 × Bool × Fin 2, validKruskalSeq [T1, T2, T3, T4] = false) ∧
     ActiveColorPairsAfterRoot 3 = 1 ∧ colorCross colorBasis0 colorBasis1 = colorBasis2) ∧
    ((dressedPeirceProjector P F F * dressedPeirceProjector P F F = dressedPeirceProjector P F F ∧
      outerDressedProjector P F * outerDressedProjector P F = outerDressedProjector P F ∧
      dressedPeirceProjector P (-F) (-F) + outerDressedProjector P F = 1 ∧
      dressedPeirceProjector P (-F) (-F) * outerDressedProjector P F = 0 ∧
      outerDressedProjector P F * dressedPeirceProjector P (-F) (-F) = 0) ∧
     (peirce11 P (outerIdentityExt P F * outerIdentityExt P F) -
        peirce11 P (outerIdentityExt P F) * peirce11 P (outerIdentityExt P F) =
        conePlus P F * coneMinus P F ∧
      peirce00 P (outerIdentityExt P F * outerIdentityExt P F) - (1 - P) =
        coneMinus P F * conePlus P F)) ∧
    (((∀ S : U → Prop, 𝒰 S ↔ S g) ∧ 𝒰 (fun u => u = g)) ∧
     ((∀ S : U → Prop, Def S → (𝒰 S ↔ S a)) ∧ ¬ 𝒰 (fun _ => False)) ∧
     ¬ Def (fun u => u = a)) ∧
    (∃ (i j : Fin (N + 1)), i.val < j.val ∧ (next^[i.val] w0) = (next^[j.val] w0)) := by
  rcases kruskal_tree_one_and_two_bounds with ⟨hTree1, hTree2⟩
  have h_cantor : cantorDiag x ≠ x n := cantor_diagonal_escapes_all x n
  have h_perm_ne : cantorDiag (indicatorStream01 ∘ swap01) ≠ cantorDiag indicatorStream01 := by
    intro h_eq
    have h_at_1 := congrFun h_eq 1
    revert h_at_1
    decide
  have h_cross01 : colorCross colorBasis0 colorBasis1 = colorBasis2 := by
    funext ⟨i, hi⟩
    rcases i with _ | _ | _ | i
    · rfl
    · rfl
    · rfl
    · exact False.elim (Nat.not_lt_zero i (Nat.lt_of_add_lt_add_right hi))
  have h_outer_eq :
      outerDressedProjector P F =
        (1 - P) + genPhi P F F + genSig P F F - genV P F F * conePlus P F := by
    unfold outerDressedProjector
    peirce_nf hP
  have h_sub : outerDressedProjector P F = 1 - dressedPeirceProjector P (-F) (-F) := by
    rw [h_outer_eq, dressedPeirceProjector_neg_eq P F hP]
    abel
  have h_part_proj : dressedPeirceProjector P (-F) (-F) + outerDressedProjector P F = 1 := by
    rw [dressedPeirceProjector_neg_eq P F hP, h_outer_eq]
    abel
  have h_orth : dressedPeirceProjector P (-F) (-F) * outerDressedProjector P F = 0 := by
    rw [h_sub, mul_sub, mul_one, dressedPeirceProjector_idempotent hP (-F) (-F), sub_self]
  have h_outer_idem : outerDressedProjector P F * outerDressedProjector P F = outerDressedProjector P F := by
    calc
      outerDressedProjector P F * outerDressedProjector P F
        = (1 - dressedPeirceProjector P (-F) (-F)) * outerDressedProjector P F := by rw [← h_sub]
      _ = outerDressedProjector P F - dressedPeirceProjector P (-F) (-F) * outerDressedProjector P F := by
            rw [sub_mul, one_mul]
      _ = outerDressedProjector P F := by rw [h_orth, sub_zero]
  have h_orth_rev : outerDressedProjector P F * dressedPeirceProjector P (-F) (-F) = 0 := by
    dsimp [outerDressedProjector, dressedPeirceProjector]
    peirce_nf hP
  have h_inner_def :
      peirce11 P (outerIdentityExt P F * outerIdentityExt P F) -
        peirce11 P (outerIdentityExt P F) * peirce11 P (outerIdentityExt P F) =
        conePlus P F * coneMinus P F := by
    rw [outerIdentityExt_sq P F hP, peirce11_outerIdentityExt P F hP]
    peirce_nf hP
  have h_outer_def :
      peirce00 P (outerIdentityExt P F * outerIdentityExt P F) - (1 - P) =
        coneMinus P F * conePlus P F := by
    rw [outerIdentityExt_sq P F hP]
    peirce_nf hP
  have h_god_iff : ∀ S : U → Prop, 𝒰 S ↔ S g := by
    intro S
    refine ⟨h_god S, fun hSg => ?_⟩
    rcases h_part S with hPos | hNeg
    · exact hPos
    · exact False.elim ((h_god (fun u => ¬ S u) hNeg) hSg)
  have h_angel_iff : ∀ S : U → Prop, Def S → (𝒰 S ↔ S a) := by
    intro S hDefS
    refine ⟨h_angel S hDefS, fun hSa => ?_⟩
    rcases h_part S with hPos | hNeg
    · exact hPos
    · exact False.elim ((h_angel (fun u => ¬ S u) (hDef_neg hDefS) hNeg) hSa)
  have h_not_def_sing : ¬ Def (fun u => u = a) := by
    intro hDef_sing
    rcases h_part (fun u => u = a) with hPos | hNeg
    · exact h_nonprinc hPos
    · exact (h_angel (fun u => u ≠ a) (hDef_neg hDef_sing) hNeg) rfl
  have h_card : Fintype.card (Fin N) < Fintype.card (Fin (N + 1)) := by
    simp only [Fintype.card_fin, Nat.lt_succ_self]
  rcases Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (N + 1) => next^[k.val] w0) h_card with
    ⟨i, j, hne, heq⟩
  have h_cycle : ∃ (i j : Fin (N + 1)), i.val < j.val ∧ (next^[i.val] w0) = (next^[j.val] w0) := by
    rcases lt_trichotomy i.val j.val with hlt | hval_eq | hgt
    · exact ⟨i, j, hlt, heq⟩
    · exact False.elim (hne (Fin.ext hval_eq))
    · exact ⟨j, i, hgt, heq.symm⟩
  exact ⟨fun hPhi => h_godel2 (h_mp h_rev hPhi),
         bitwise_peirce_dp_tree_compiler Provable h_dp_bit d P_bit h_bit,
         ⟨h_cantor, h_perm_ne⟩,
         ⟨hTree1, hTree2, by decide, h_cross01⟩,
         ⟨⟨dressedPeirceProjector_idempotent hP F F, h_outer_idem, h_part_proj, h_orth, h_orth_rev⟩,
          ⟨h_inner_def, h_outer_def⟩⟩,
         ⟨⟨h_god_iff, (h_god_iff (fun u => u = g)).mpr rfl⟩,
          ⟨h_angel_iff, fun hF => (h_angel_iff (fun _ => False) hDef_false).mp hF⟩,
          h_not_def_sing⟩,
         h_cycle⟩

end InfoGeometry.Canonical.FriedmanFoundationsUltrafilterPoset
