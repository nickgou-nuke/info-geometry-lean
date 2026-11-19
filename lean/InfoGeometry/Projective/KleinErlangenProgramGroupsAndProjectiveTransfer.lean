/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Action
import InfoGeometry.Erlangen.InvariantGeometry
import InfoGeometry.Projective.KleinCrossRatioInvariant
import InfoGeometry.Projective.KleinQuadric
import InfoGeometry.Projective.DahmPluckerKleinCollineation
import InfoGeometry.Projective.PluckerLinearComplex
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Felix Klein's *Erlangen Program* (1872): Groups, Dualities, Cayley–Klein Subordination, & Projective Transfer

This module formalizes Archetypes `EK₁`–`EK₅` from Felix Klein's 1872 Erlangen Program
(*"A Comparative Review of Recent Researches in Geometry"*, M. W. Haskell trans., `0807.3161v1`,
Intro and §§1–5, §10.1, and Notes I–VI):

1. **`EK₁` (§1 & 1893 Footnote 8)**: Finite composition-closed transformation sets automatically
   contain the identity and inverses (`klein_fn8_finite_mul_closed_has_one_and_inv`,
   `klein_fn8_finite_perm_closed_is_subgroup`), whereas on an infinite carrier composition closure
   does not suffice (`klein_fn8_infinite_perm_countermodel`, `[countermodel_found]`).
2. **`EK₂` (§1 & §3)**: Index-2 collineation–correlation subgroup of `Equiv.Perm L`
   (`collineationSubgroup`, `collineationCorrelationSubgroup`, `mul_two_correlations_mem_collineations`,
   `correlations_not_closed_under_mul_bool`), projective point–hyperplane incidence duality, and full
   iff-characterization (`klein_sec3_principal_group_iff_spherical_absolute`) of the Euclidean
   principal group `EuclideanSimilarity n` as the projective stabilizer of the hyperplane at
   infinity `H_∞` and the spherical absolute quadric `∑ xᵢ² = 0`.
3. **`EK₃` (§2, §4, §5 & Footnote 23)**: Erlangen's subgroup-adjoining equivalence
   (`klein_sec2_stabilizer_adjoining_equiv`), `Abbildung` conjugation transfer
   (`klein_sec4_abbildung_perm_transfer`), orbit normal-core kernel theorem
   (`klein_sec5_fn23_body_kernel_eq_normalCore`), and projective center countermodel
   (`gl2_neg_one_acts_nontrivially_yet_fixes_projective_body`).
4. **`EK₄` (§4, §5 & Note V)**: Veronese rational normal conic transfer `GL(2) →* GL(3)`
   (`sym2GL2`), Hesse's principle of transference (`hessePairPoint`, `hesseDiscForm`), and
   Plücker–Klein Jacobi–Hodge correlation duality (`kleinHodgeDual_jacobi_dual`).
5. **`EK₅` (§10.1 & Note VI)**: Sharp 3-transitivity of `PGL(2, K)` on `HomPoint2 K`
   (`pgl2_three_transitive`), Note VI impossibility of any 3-point invariant on `ℙ¹(K)` or a
   nondegenerate conic (`klein_noteVI_triple_invariant_const`), cross-ratio boundary collapse
   on the quadric, and recovery of non-constant metric invariants upon adjoining a pole.
-/

noncomputable section

namespace InfoGeometry.Projective.KleinErlangenProgramGroupsAndProjectiveTransfer

open InfoGeometry.Erlangen.InvariantGeometry
open InfoGeometry.Projective.KleinCrossRatioInvariant
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.DahmPluckerKleinCollineation
open scoped Matrix LinearAlgebra.Projectivization

/-! ## 0. Non-Commutativity Ground Witness (T16) -/

/-- Closed `2 × 2` matrix non-commutativity ground witness over any nontrivial ring `R`. -/
theorem kleinErlangenGroups_mat2_not_commute
    {R : Type*} [Ring R] [Nontrivial R] :
    ∃ a b : Matrix (Fin 2) (Fin 2) R, a * b ≠ b * a := by
  refine ⟨Matrix.single 0 1 (1 : R), Matrix.single 1 0 (1 : R), ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  simp [Matrix.mul_apply, Matrix.single_apply] at h00

/-- Specialization to `ℤ` of the `2 × 2` matrix non-commutativity witness. -/
theorem kleinErlangenGroups_mat2Z_not_commute :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℤ, a * b ≠ b * a :=
  kleinErlangenGroups_mat2_not_commute

/-! ## 1. `EK₁` (§1 & Fn. 8): Finite vs. Infinite Transformation Semigroups -/

section TransformationGroupsFn8

private theorem mem_pow_succ_of_mul_closed {G : Type*} [Group G]
    (S : Set G) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {g : G} (hg : g ∈ S) :
    ∀ m : ℕ, g ^ (m + 1) ∈ S
  | 0 => by simpa using hg
  | m + 1 => by
    rw [pow_succ']
    exact hmul g hg (g ^ (m + 1)) (mem_pow_succ_of_mul_closed S hmul hg m)

private theorem exists_pow_succ_eq_one_of_finite {G : Type*} [Group G] [Finite G] (g : G) :
    ∃ m : ℕ, g ^ (m + 1) = 1 := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => g ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hpos : 0 < j - i := Nat.sub_pos_of_lt hlt
    have hk : g ^ i * g ^ (j - i) = g ^ i * 1 := by
      rw [← pow_add, Nat.add_sub_of_le hlt.le, heq, mul_one]
    have hpow : g ^ (j - i) = 1 := mul_left_cancel hk
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    refine ⟨m, ?_⟩
    rw [← Nat.succ_eq_add_one, ← hm]
    exact hpow
  · have hpos : 0 < i - j := Nat.sub_pos_of_lt hgt
    have hk : g ^ j * g ^ (i - j) = g ^ j * 1 := by
      rw [← pow_add, Nat.add_sub_of_le hgt.le, ← heq, mul_one]
    have hpow : g ^ (i - j) = 1 := mul_left_cancel hk
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    refine ⟨m, ?_⟩
    rw [← Nat.succ_eq_add_one, ← hm]
    exact hpow

/-- **Klein's 1893 Footnote 8 (Finite Case)**: in any finite ambient group `G`, a nonempty set
closed under multiplication automatically contains `1` and all inverses. -/
theorem klein_fn8_finite_mul_closed_has_one_and_inv {G : Type*} [Group G] [Finite G]
    (S : Set G) (hne : S.Nonempty) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) :
    (1 : G) ∈ S ∧ ∀ g ∈ S, g⁻¹ ∈ S := by
  have inv_of_mem : ∀ g ∈ S, (1 : G) ∈ S ∧ g⁻¹ ∈ S := fun g hg => by
    obtain ⟨m, hpow⟩ := exists_pow_succ_eq_one_of_finite g
    have hone : (1 : G) ∈ S := hpow ▸ mem_pow_succ_of_mul_closed S hmul hg m
    refine ⟨hone, ?_⟩
    cases m with
    | zero =>
      have hg1 : g = 1 := by simpa using hpow
      rw [hg1, inv_one]
      exact hone
    | succ p =>
      rw [pow_succ'] at hpow
      have hinv : g⁻¹ = g ^ (p + 1) := inv_eq_of_mul_eq_one_right hpow
      rw [hinv]
      exact mem_pow_succ_of_mul_closed S hmul hg p
  obtain ⟨g₀, hg₀⟩ := hne
  exact ⟨(inv_of_mem g₀ hg₀).1, fun g hg => (inv_of_mem g hg).2⟩

/-- Bundled `Subgroup G` extracted from a nonempty multiplication-closed subset of a finite group. -/
def finiteMulClosedSubgroup {G : Type*} [Group G] [Finite G]
    (S : Set G) (hne : S.Nonempty) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) : Subgroup G where
  carrier := S
  one_mem' := (klein_fn8_finite_mul_closed_has_one_and_inv S hne hmul).1
  mul_mem' := fun ha hb => hmul _ ha _ hb
  inv_mem' := fun hg => (klein_fn8_finite_mul_closed_has_one_and_inv S hne hmul).2 _ hg

/-- Specialization to permutations of a finite set: nonempty composition-closed subsets of
`Equiv.Perm α` form a genuine subgroup. -/
theorem klein_fn8_finite_perm_closed_is_subgroup {α : Type*} [Finite α]
    (S : Set (Equiv.Perm α)) (hne : S.Nonempty) (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S) :
    ∃ H : Subgroup (Equiv.Perm α), (H : Set (Equiv.Perm α)) = S :=
  ⟨finiteMulClosedSubgroup S hne hmul, rfl⟩

/-- Strict positive integer translations inside `Equiv.Perm ℤ`. -/
def posShiftSet : Set (Equiv.Perm ℤ) :=
  {f | ∃ n : ℤ, 0 < n ∧ f = Equiv.addRight n}

/-- **Klein's 1893 Footnote 8 — `[countermodel_found]` (Infinite Carrier)**:
on an infinite set `ℤ`, `posShiftSet` is nonempty and closed under composition, yet fails to
contain `1` and fails to contain inverses. -/
theorem klein_fn8_infinite_perm_countermodel :
    posShiftSet.Nonempty ∧
      (∀ f ∈ posShiftSet, ∀ g ∈ posShiftSet, f * g ∈ posShiftSet) ∧
      (1 : Equiv.Perm ℤ) ∉ posShiftSet ∧
      ∃ f ∈ posShiftSet, f⁻¹ ∉ posShiftSet := by
  refine ⟨⟨Equiv.addRight 1, 1, by norm_num, rfl⟩, ?_, ?_, ?_⟩
  · rintro f ⟨m, hm, rfl⟩ g ⟨n, hn, rfl⟩
    refine ⟨m + n, add_pos hm hn, ?_⟩
    ext x
    simp [Equiv.Perm.mul_apply]
    ring
  · rintro ⟨n, hn, h1⟩
    have hx := congrArg (fun e : Equiv.Perm ℤ => e 0) h1
    simp [Equiv.addRight] at hx
    omega
  · refine ⟨Equiv.addRight 1, ⟨1, by norm_num, rfl⟩, ?_⟩
    rintro ⟨n, hn, hinv⟩
    have hx := congrArg (fun e : Equiv.Perm ℤ => e 0) hinv
    have hinv_val : (Equiv.addRight (1 : ℤ))⁻¹ 0 = (-1 : ℤ) := by
      have : (Equiv.addRight (1 : ℤ))⁻¹ = Equiv.addRight (-1) := by
        ext k
        rw [Equiv.Perm.inv_def]
        rfl
      rw [this]
      simp [Equiv.addRight]
    have hx_lhs : (Equiv.addRight n) 0 = n := by simp [Equiv.addRight]
    rw [hx_lhs, hinv_val] at hx
    omega

end TransformationGroupsFn8

/-! ## 2. `EK₂` (§1 & §3): Correlations vs. Collineations & Principal Group Subordination -/

section DualisticAndPrincipalGroup

/-- Order-preserving bijection ("collineation") of a poset `L`. -/
def IsOrderCollineation {L : Type*} [PartialOrder L] (e : Equiv.Perm L) : Prop :=
  ∀ a b : L, e a ≤ e b ↔ a ≤ b

/-- Order-reversing bijection ("dualistic correlation") of a poset `L`. -/
def IsOrderCorrelation {L : Type*} [PartialOrder L] (e : Equiv.Perm L) : Prop :=
  ∀ a b : L, e a ≤ e b ↔ b ≤ a

/-- Subgroup of collineations inside `Equiv.Perm L`. -/
def collineationSubgroup (L : Type*) [PartialOrder L] : Subgroup (Equiv.Perm L) where
  carrier := {e | IsOrderCollineation e}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := fun {e₁ e₂} h₁ h₂ a b => (h₁ (e₂ a) (e₂ b)).trans (h₂ a b)
  inv_mem' := fun {e} h a b => by
    have h1 := h (e⁻¹ a) (e⁻¹ b)
    have ha : e (e⁻¹ a) = a := e.apply_symm_apply a
    have hb : e (e⁻¹ b) = b := e.apply_symm_apply b
    rw [ha, hb] at h1
    exact h1.symm

/-- Joint group generated by all collineations and correlations inside `Equiv.Perm L`. -/
def collineationCorrelationSubgroup (L : Type*) [PartialOrder L] :
    Subgroup (Equiv.Perm L) where
  carrier := {e | IsOrderCollineation e ∨ IsOrderCorrelation e}
  one_mem' := Or.inl fun _ _ => Iff.rfl
  mul_mem' := by
    rintro e₁ e₂ (h₁ | h₁) (h₂ | h₂)
    · exact Or.inl fun a b => (h₁ (e₂ a) (e₂ b)).trans (h₂ a b)
    · exact Or.inr fun a b => (h₁ (e₂ a) (e₂ b)).trans (h₂ a b)
    · exact Or.inr fun a b => (h₁ (e₂ a) (e₂ b)).trans (h₂ b a)
    · exact Or.inl fun a b => (h₁ (e₂ a) (e₂ b)).trans (h₂ b a)
  inv_mem' := by
    rintro e (h | h)
    · exact Or.inl fun a b => by
        have h1 := h (e⁻¹ a) (e⁻¹ b)
        have ha : e (e⁻¹ a) = a := e.apply_symm_apply a
        have hb : e (e⁻¹ b) = b := e.apply_symm_apply b
        rw [ha, hb] at h1
        exact h1.symm
    · exact Or.inr fun a b => by
        have h1 := h (e⁻¹ b) (e⁻¹ a)
        have ha : e (e⁻¹ a) = a := e.apply_symm_apply a
        have hb : e (e⁻¹ b) = b := e.apply_symm_apply b
        rw [ha, hb] at h1
        exact h1.symm

/-- On any non-trivially ordered poset (`∃ a b, a < b`), no bijection is both a collineation and a
correlation. -/
theorem not_both_collineation_and_correlation {L : Type*} [PartialOrder L]
    (hstrict : ∃ a b : L, a < b) (e : Equiv.Perm L) :
    ¬ (IsOrderCollineation e ∧ IsOrderCorrelation e) := by
  rintro ⟨hc, hr⟩
  obtain ⟨a, b, hab⟩ := hstrict
  have hba : b ≤ a := (hr a b).mp ((hc a b).mpr hab.le)
  exact hab.not_ge hba

/-- **Klein §1 (Dualistic Transformations)**: the composition of any two correlations is a
collineation (never a correlation when `L` has strict order `a < b`). -/
theorem mul_two_correlations_mem_collineations {L : Type*} [PartialOrder L]
    (e₁ e₂ : Equiv.Perm L) (h₁ : IsOrderCorrelation e₁) (h₂ : IsOrderCorrelation e₂) :
    e₁ * e₂ ∈ collineationSubgroup L :=
  fun a b => (h₁ (e₂ a) (e₂ b)).trans (h₂ b a)

/-- Explicit parity homomorphism into `Multiplicative (ZMod 2)` witnessing that
`collineationSubgroup L` has index ≤ 2 (and exact kernel) inside `collineationCorrelationSubgroup L`
whenever `∃ a b : L, a < b`. -/
def dualityParityHom (L : Type*) [PartialOrder L] (hstrict : ∃ a b : L, a < b) :
    collineationCorrelationSubgroup L →* Multiplicative (ZMod 2) where
  toFun e := by
    classical
    exact if IsOrderCollineation (e : Equiv.Perm L) then 1 else Multiplicative.ofAdd (1 : ZMod 2)
  map_one' := by
    classical
    have h1 : IsOrderCollineation (1 : Equiv.Perm L) := fun _ _ => Iff.rfl
    change (if IsOrderCollineation (1 : Equiv.Perm L) then (1 : Multiplicative (ZMod 2))
      else Multiplicative.ofAdd (1 : ZMod 2)) = 1
    split_ifs
    · rfl
  map_mul' e₁ e₂ := by
    classical
    have hmul : ((e₁ * e₂ : collineationCorrelationSubgroup L) : Equiv.Perm L) =
        (e₁ : Equiv.Perm L) * (e₂ : Equiv.Perm L) := rfl
    rcases e₁.2 with h1 | h1 <;> rcases e₂.2 with h2 | h2
    · have h12 : IsOrderCollineation ((e₁ : Equiv.Perm L) * (e₂ : Equiv.Perm L)) :=
        fun a b => (h1 (e₂.1 a) (e₂.1 b)).trans (h2 a b)
      simp [hmul, h1, h2, h12]
    · have h12 : IsOrderCorrelation ((e₁ : Equiv.Perm L) * (e₂ : Equiv.Perm L)) :=
        fun a b => (h1 (e₂.1 a) (e₂.1 b)).trans (h2 a b)
      have hn2 : ¬ IsOrderCollineation (e₂ : Equiv.Perm L) :=
        fun hc => not_both_collineation_and_correlation hstrict e₂ ⟨hc, h2⟩
      have hn12 : ¬ IsOrderCollineation ((e₁ : Equiv.Perm L) * (e₂ : Equiv.Perm L)) :=
        fun hc => not_both_collineation_and_correlation hstrict _ ⟨hc, h12⟩
      simp [hmul, h1, hn2, hn12]
    · have h12 : IsOrderCorrelation ((e₁ : Equiv.Perm L) * (e₂ : Equiv.Perm L)) :=
        fun a b => (h1 (e₂.1 a) (e₂.1 b)).trans (h2 b a)
      have hn1 : ¬ IsOrderCollineation (e₁ : Equiv.Perm L) :=
        fun hc => not_both_collineation_and_correlation hstrict e₁ ⟨hc, h1⟩
      have hn12 : ¬ IsOrderCollineation ((e₁ : Equiv.Perm L) * (e₂ : Equiv.Perm L)) :=
        fun hc => not_both_collineation_and_correlation hstrict _ ⟨hc, h12⟩
      simp [hmul, hn1, h2, hn12]
    · have h12 : IsOrderCollineation ((e₁ : Equiv.Perm L) * (e₂ : Equiv.Perm L)) :=
        fun a b => (h1 (e₂.1 a) (e₂.1 b)).trans (h2 b a)
      have hn1 : ¬ IsOrderCollineation (e₁ : Equiv.Perm L) :=
        fun hc => not_both_collineation_and_correlation hstrict e₁ ⟨hc, h1⟩
      have hn2 : ¬ IsOrderCollineation (e₂ : Equiv.Perm L) :=
        fun hc => not_both_collineation_and_correlation hstrict e₂ ⟨hc, h2⟩
      simp [hmul, hn1, hn2, h12]
      rfl

/-- `[countermodel_found]`: on `Bool` (`false < true`), order-reversing `Equiv.swap false true`
is a correlation whose square is `1` (strictly a collineation, not a correlation). -/
theorem correlations_not_closed_under_mul_bool :
    let τ : Equiv.Perm Bool := Equiv.swap false true
    IsOrderCorrelation τ ∧ ¬ IsOrderCorrelation (τ * τ) := by
  refine ⟨?_, ?_⟩
  · intro a b
    cases a <;> cases b <;> decide
  · intro h
    have hle : (Equiv.swap false true * Equiv.swap false true) false ≤
        (Equiv.swap false true * Equiv.swap false true) true := by decide
    have hcontra : true ≤ false := (h false true).mp hle
    exact absurd hcontra (by decide)

/-- Projective point–hyperplane incidence relation `ξ ⬝ᵥ x = 0` in `K^{n+1}`. -/
def pointHyperplaneIncident {K : Type*} [CommRing K] {n : ℕ}
    (x ξ : Fin (n + 1) → K) : Prop :=
  ξ ⬝ᵥ x = 0

/-- Contragredient collineation action `(g x, (g⁻¹)ᵀ ξ)` and point–hyperplane swap correlation
`(ξ, x)` both preserve incidence, while conjugation by swap carries `g` to `(g⁻¹)ᵀ`. -/
theorem projective_incidence_contragredient_and_swap {K : Type*} [CommRing K] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) K) (x ξ : Fin (n + 1) → K) :
    (pointHyperplaneIncident ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ x)
        (((↑g⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) K)ᵀ) *ᵥ ξ) ↔
      pointHyperplaneIncident x ξ) ∧
    (pointHyperplaneIncident ξ x ↔ pointHyperplaneIncident x ξ) := by
  have hinv : (↑g⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = 1 :=
    Units.inv_mul g
  have hdot : (((↑g⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) K)ᵀ) *ᵥ ξ) ⬝ᵥ
      ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ x) = ξ ⬝ᵥ x := by
    calc
      (((↑g⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) K)ᵀ) *ᵥ ξ) ⬝ᵥ
          ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ x) =
          (ξ ᵥ* (↑g⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) ⬝ᵥ
            ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ x) := by
        rw [Matrix.mulVec_transpose]
      _ = ξ ⬝ᵥ ((↑g⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ
            ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ x)) :=
        (Matrix.dotProduct_mulVec ξ (↑g⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
          ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ x)).symm
      _ = ξ ⬝ᵥ (((↑g⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
            (g : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec]
      _ = ξ ⬝ᵥ x := by rw [hinv, Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · simp only [pointHyperplaneIncident]
    rw [hdot]
  · simp [pointHyperplaneIncident, dotProduct_comm]

/-! ### Principal Group `EuclideanSimilarity n` & Cayley–Klein Spherical Absolute (`§3`) -/

/-- Element `(r, O, t)` of the Euclidean principal group `Sim(n)` (`r ∈ ℝˣ`, `O ∈ O(n)`,
`t ∈ ℝⁿ`), acting on `ℝⁿ` by `x ↦ r • (O *ᵥ x) + t`. -/
@[ext]
structure EuclideanSimilarity (n : ℕ) where
  scale : ℝˣ
  orth : Matrix.orthogonalGroup (Fin n) ℝ
  trans : Fin n → ℝ

instance (n : ℕ) : Inhabited (EuclideanSimilarity n) :=
  ⟨⟨1, 1, 0⟩⟩

/-- Constructive closed inhabitant witness for `EuclideanSimilarity 2`. -/
def euclideanSimilarity2Identity : EuclideanSimilarity 2 :=
  ⟨1, 1, 0⟩

instance (n : ℕ) : One (EuclideanSimilarity n) where
  one := ⟨1, 1, 0⟩

instance (n : ℕ) : Mul (EuclideanSimilarity n) where
  mul g h :=
    ⟨g.scale * h.scale, g.orth * h.orth, (g.scale : ℝ) • (g.orth.1 *ᵥ h.trans) + g.trans⟩

instance (n : ℕ) : Inv (EuclideanSimilarity n) where
  inv g := ⟨g.scale⁻¹, g.orth⁻¹, -((g.scale⁻¹ : ℝ) • (g.orth⁻¹.1 *ᵥ g.trans))⟩

instance (n : ℕ) : Group (EuclideanSimilarity n) where
  one := 1
  mul := (· * ·)
  inv := (·⁻¹)
  mul_assoc a b c := by
    apply EuclideanSimilarity.ext
    · exact mul_assoc _ _ _
    · exact mul_assoc _ _ _
    · ext i
      have hs : ∀ u v : EuclideanSimilarity n, (u * v).scale = u.scale * v.scale := fun _ _ => rfl
      have ho : ∀ u v : EuclideanSimilarity n, (u * v).orth = u.orth * v.orth := fun _ _ => rfl
      have ht : ∀ u v : EuclideanSimilarity n,
          (u * v).trans = (u.scale : ℝ) • (u.orth.1 *ᵥ v.trans) + u.trans := fun _ _ => rfl
      simp only [ht, hs, ho, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Units.val_mul,
        Submonoid.coe_mul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      ring
  one_mul a := by
    apply EuclideanSimilarity.ext
    · exact one_mul _
    · exact one_mul _
    · ext i
      change ((1 : ℝˣ) : ℝ) * ((1 : Matrix.orthogonalGroup (Fin n) ℝ).1 *ᵥ a.trans) i + 0 = a.trans i
      simp
  mul_one a := by
    apply EuclideanSimilarity.ext
    · exact mul_one _
    · exact mul_one _
    · ext i
      change (a.scale : ℝ) * (a.orth.1 *ᵥ 0) i + a.trans i = a.trans i
      simp
  inv_mul_cancel a := by
    apply EuclideanSimilarity.ext
    · exact inv_mul_cancel _
    · exact inv_mul_cancel _
    · ext i
      change ((a.scale⁻¹ : ℝˣ) : ℝ) * (a.orth⁻¹.1 *ᵥ a.trans) i +
          (-((a.scale⁻¹ : ℝ) • (a.orth⁻¹.1 *ᵥ a.trans))) i = 0
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val]
      ring

instance (n : ℕ) : MulAction (EuclideanSimilarity n) (Fin n → ℝ) where
  smul g x := (g.scale : ℝ) • (g.orth.1 *ᵥ x) + g.trans
  one_smul x := by
    ext i
    change ((1 : ℝˣ) : ℝ) * ((1 : Matrix.orthogonalGroup (Fin n) ℝ).1 *ᵥ x) i + 0 = x i
    simp
  mul_smul g h x := by
    ext i
    change ((g.scale * h.scale : ℝˣ) : ℝ) *
        ((g.orth * h.orth : Matrix.orthogonalGroup (Fin n) ℝ).1 *ᵥ x) i +
        ((g.scale : ℝ) • (g.orth.1 *ᵥ h.trans) + g.trans) i =
      (g.scale : ℝ) * (g.orth.1 *ᵥ ((h.scale : ℝ) • (h.orth.1 *ᵥ x) + h.trans)) i + g.trans i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Units.val_mul,
      Submonoid.coe_mul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    ring

/-- Squared Euclidean distance on `Fin n → ℝ`. -/
def euclidDistSq {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (x i - y i) ^ 2

private theorem orth_mulVec_sq_sum {n : ℕ} (O : Matrix.orthogonalGroup (Fin n) ℝ)
    (v : Fin n → ℝ) :
    ∑ i : Fin n, (O.1 *ᵥ v) i ^ 2 = ∑ i : Fin n, (v i) ^ 2 := by
  have hOTO : O.1ᵀ * O.1 = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp O.2
  calc
    ∑ i : Fin n, (O.1 *ᵥ v) i ^ 2 = (O.1 *ᵥ v) ⬝ᵥ (O.1 *ᵥ v) := by
      simp [dotProduct, sq]
    _ = ((O.1 *ᵥ v) ᵥ* O.1) ⬝ᵥ v := Matrix.dotProduct_mulVec (O.1 *ᵥ v) O.1 v
    _ = (O.1ᵀ *ᵥ (O.1 *ᵥ v)) ⬝ᵥ v := by rw [← Matrix.mulVec_transpose]
    _ = v ⬝ᵥ v := by rw [Matrix.mulVec_mulVec, hOTO, Matrix.one_mulVec]
    _ = ∑ i : Fin n, (v i) ^ 2 := by simp [dotProduct, sq]

/-- Every `g : EuclideanSimilarity n` scales squared Euclidean distances by `(g.scale : ℝ) ^ 2`
and strictly preserves distance ratios `d(x, y)² / d(u, v)²`. -/
theorem euclidDistSq_smul {n : ℕ} (g : EuclideanSimilarity n) (x y : Fin n → ℝ) :
    euclidDistSq (g • x) (g • y) = (g.scale : ℝ) ^ 2 * euclidDistSq x y := by
  have hsub : ∀ i : Fin n, (g • x) i - (g • y) i =
      (g.scale : ℝ) * (g.orth.1 *ᵥ (x - y)) i := fun i => by
    change ((g.scale : ℝ) * (g.orth.1 *ᵥ x) i + g.trans i) -
        ((g.scale : ℝ) * (g.orth.1 *ᵥ y) i + g.trans i) =
      (g.scale : ℝ) * (g.orth.1 *ᵥ (x - y)) i
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    ring
  calc
    euclidDistSq (g • x) (g • y) =
        ∑ i : Fin n, ((g.scale : ℝ) * (g.orth.1 *ᵥ (x - y)) i) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsub i]
    _ = (g.scale : ℝ) ^ 2 * ∑ i : Fin n, (g.orth.1 *ᵥ (x - y)) i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    _ = (g.scale : ℝ) ^ 2 * euclidDistSq x y := by
      rw [orth_mulVec_sq_sum]
      rfl

/-- Homogeneous `(n + 1) × (n + 1)` affine lift of `EuclideanSimilarity n` preserving `H_∞ : X₀ = 0`. -/
def simProjMatrix {n : ℕ} (g : EuclideanSimilarity n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Fin.cases (Fin.cons 1 0) (fun i => Fin.cons (g.trans i) (fun j => (g.scale : ℝ) * g.orth.1 i j))

private theorem simProjMatrix_zero_zero {n : ℕ} (g : EuclideanSimilarity n) :
    simProjMatrix g 0 0 = 1 := rfl

private theorem simProjMatrix_zero_succ {n : ℕ} (g : EuclideanSimilarity n) (j : Fin n) :
    simProjMatrix g 0 j.succ = 0 := by
  simp [simProjMatrix]

private theorem simProjMatrix_succ_zero {n : ℕ} (g : EuclideanSimilarity n) (i : Fin n) :
    simProjMatrix g i.succ 0 = g.trans i := by
  simp [simProjMatrix]

private theorem simProjMatrix_succ_succ {n : ℕ} (g : EuclideanSimilarity n) (i j : Fin n) :
    simProjMatrix g i.succ j.succ = (g.scale : ℝ) * g.orth.1 i j := by
  simp [simProjMatrix]

theorem simProjMatrix_one (n : ℕ) :
    simProjMatrix (1 : EuclideanSimilarity n) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [simProjMatrix]
  · simp [simProjMatrix_zero_succ, (Fin.succ_ne_zero j').symm]
  · simp [simProjMatrix_succ_zero]
    rfl
  · simp [simProjMatrix_succ_succ, Matrix.one_apply]
    change ((1 : ℝˣ) : ℝ) * (1 : Matrix.orthogonalGroup (Fin n) ℝ).1 i' j' =
      if i' = j' then 1 else 0
    simp [Matrix.one_apply]

theorem simProjMatrix_mul {n : ℕ} (g h : EuclideanSimilarity n) :
    simProjMatrix (g * h) = simProjMatrix g * simProjMatrix h := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [simProjMatrix_zero_zero, simProjMatrix_zero_succ]
  · simp [simProjMatrix_zero_zero, simProjMatrix_zero_succ]
  · simp only [simProjMatrix_succ_zero, simProjMatrix_succ_succ,
      simProjMatrix_zero_zero, mul_one]
    change ((g.scale : ℝ) • (g.orth.1 *ᵥ h.trans) + g.trans) i' =
      g.trans i' + ∑ k : Fin n, (g.scale : ℝ) * g.orth.1 i' k * h.trans k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Finset.mul_sum]
    have hcon : ∑ k : Fin n, (g.scale : ℝ) * (g.orth.1 i' k * h.trans k) =
        ∑ k : Fin n, (g.scale : ℝ) * g.orth.1 i' k * h.trans k :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [hcon, add_comm]
  · simp only [simProjMatrix_succ_succ, simProjMatrix_succ_zero,
      simProjMatrix_zero_succ, mul_zero, zero_add]
    change ((g.scale * h.scale : ℝˣ) : ℝ) * ((g.orth * h.orth).1 i' j') =
      ∑ k : Fin n, ((g.scale : ℝ) * g.orth.1 i' k) * ((h.scale : ℝ) * h.orth.1 k j')
    simp only [Units.val_mul, Submonoid.coe_mul, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- Group homomorphism `EuclideanSimilarity n →* GL(n + 1, ℝ)`. -/
def simToProjGL (n : ℕ) : EuclideanSimilarity n →* Matrix.GeneralLinearGroup (Fin (n + 1)) ℝ where
  toFun g :=
    { val := simProjMatrix g
      inv := simProjMatrix g⁻¹
      val_inv := by rw [← simProjMatrix_mul, mul_inv_cancel, simProjMatrix_one]
      inv_val := by rw [← simProjMatrix_mul, inv_mul_cancel, simProjMatrix_one] }
  map_one' := by
    apply Units.ext
    exact simProjMatrix_one n
  map_mul' g h := by
    apply Units.ext
    exact simProjMatrix_mul g h

theorem simProjMatrix_mulVec_cons {n : ℕ} (g : EuclideanSimilarity n) (x : Fin n → ℝ) :
    simProjMatrix g *ᵥ Fin.cons 1 x = Fin.cons 1 (g • x) := by
  ext i
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp [simProjMatrix_zero_zero, simProjMatrix_zero_succ]
  · simp only [Fin.cons_succ, Fin.cons_zero, simProjMatrix_succ_zero, simProjMatrix_succ_succ]
    change g.trans i' * 1 + ∑ j : Fin n, (g.scale : ℝ) * g.orth.1 i' j * x j =
      (g.scale : ℝ) * (g.orth.1 *ᵥ x) i' + g.trans i'
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by ring

/-- Cayley–Klein complexified spherical quadric on `ℂ^{n+1}` (`∑_{i=1}^n Xᵢ²`, which vanishes
on `H_∞` along the imaginary spherical circle/sphere at infinity). -/
def sphericalInfinityQuadricC {n : ℕ} (X : Fin (n + 1) → ℂ) : ℂ :=
  ∑ i : Fin n, (X i.succ) ^ 2

/-- Real matrix action on `ℂ^{n+1}`. -/
def mulVecRealOnC {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (X : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  M.map Complex.ofReal *ᵥ X

theorem simProjMatrix_preserves_H_inf_and_sphericalQuadric {n : ℕ}
    (g : EuclideanSimilarity n) (X : Fin (n + 1) → ℂ) (hinf : X 0 = 0) :
    mulVecRealOnC (simProjMatrix g) X 0 = 0 ∧
      sphericalInfinityQuadricC (mulVecRealOnC (simProjMatrix g) X) =
        (g.scale : ℂ) ^ 2 * sphericalInfinityQuadricC X := by
  have h0 : mulVecRealOnC (simProjMatrix g) X 0 = 0 := by
    simp only [mulVecRealOnC, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.map_apply, simProjMatrix_zero_zero, simProjMatrix_zero_succ,
      Complex.ofReal_one, Complex.ofReal_zero, hinf, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
  refine ⟨h0, ?_⟩
  have hsucc : ∀ i : Fin n, mulVecRealOnC (simProjMatrix g) X i.succ =
      (g.scale : ℂ) * ∑ j : Fin n, (g.orth.1 i j : ℂ) * X j.succ := fun i => by
    simp only [mulVecRealOnC, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.map_apply, simProjMatrix_succ_zero, simProjMatrix_succ_succ,
      hinf, mul_zero, zero_add, Complex.ofReal_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hO := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp g.orth.2
  calc
    sphericalInfinityQuadricC (mulVecRealOnC (simProjMatrix g) X) =
        ∑ i : Fin n, ((g.scale : ℂ) * ∑ j : Fin n, (g.orth.1 i j : ℂ) * X j.succ) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsucc i]
    _ = (g.scale : ℂ) ^ 2 * ∑ i : Fin n, (∑ j : Fin n, (g.orth.1 i j : ℂ) * X j.succ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    _ = (g.scale : ℂ) ^ 2 * sphericalInfinityQuadricC X := by
      congr 1
      have hcomm : ∑ i : Fin n, (∑ j : Fin n, (g.orth.1 i j : ℂ) * X j.succ) ^ 2 =
          ∑ j : Fin n, ∑ k : Fin n,
            ((∑ i : Fin n, g.orth.1 i j * g.orth.1 i k : ℝ) : ℂ) * (X j.succ * X k.succ) := by
        calc
          ∑ i : Fin n, (∑ j : Fin n, (g.orth.1 i j : ℂ) * X j.succ) ^ 2 =
              ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                ((g.orth.1 i j : ℂ) * X j.succ) * ((g.orth.1 i k : ℂ) * X k.succ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
          _ = ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n,
                ((g.orth.1 i j : ℂ) * X j.succ) * ((g.orth.1 i k : ℂ) * X k.succ) :=
            Finset.sum_comm
          _ = ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
                ((g.orth.1 i j : ℂ) * X j.succ) * ((g.orth.1 i k : ℂ) * X k.succ) :=
            Finset.sum_congr rfl fun j _ => Finset.sum_comm
          _ = ∑ j : Fin n, ∑ k : Fin n,
                ((∑ i : Fin n, g.orth.1 i j * g.orth.1 i k : ℝ) : ℂ) * (X j.succ * X k.succ) := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
            push_cast
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => by ring
      rw [hcomm]
      have hcol : ∀ j k : Fin n, ∑ i : Fin n, g.orth.1 i j * g.orth.1 i k =
          if j = k then 1 else 0 := fun j k => by
        have hjk := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j k) hO
        simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hjk
      have hterm : ∑ j : Fin n, ∑ k : Fin n,
            ((∑ i : Fin n, g.orth.1 i j * g.orth.1 i k : ℝ) : ℂ) * (X j.succ * X k.succ) =
          ∑ j : Fin n, ∑ k : Fin n,
            (if j = k then (1 : ℂ) else 0) * (X j.succ * X k.succ) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [hcol j k]
        split_ifs <;> simp
      rw [hterm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Finset.sum_ite_eq, Finset.mem_univ, sq]

private theorem orth_of_norm_preserving {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hnorm : ∀ v : Fin n → ℝ, ∑ i : Fin n, (O *ᵥ v) i ^ 2 = ∑ i : Fin n, (v i) ^ 2) :
    O ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply]
  have htr : ∀ j : Fin n, Oᵀ p j = O j p := fun _ => rfl
  simp only [htr]
  have hp := hnorm (Pi.single p (1 : ℝ))
  have hp_eval : ∑ i : Fin n, O i p ^ 2 = 1 := by
    have hlhs : ∑ i : Fin n, (O *ᵥ (Pi.single p (1 : ℝ) : Fin n → ℝ)) i ^ 2 =
        ∑ i : Fin n, O i p ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.mulVec_single, Matrix.col_apply]
    have hrhs : ∑ i : Fin n, ((Pi.single p (1 : ℝ) : Fin n → ℝ) i) ^ 2 = 1 := by
      simp [Pi.single_apply]
    linarith
  by_cases hpq : p = q
  · subst hpq
    simpa [sq] using hp_eval
  · have hq := hnorm (Pi.single q (1 : ℝ))
    have hq_eval : ∑ i : Fin n, O i q ^ 2 = 1 := by
      have hlhs : ∑ i : Fin n, (O *ᵥ (Pi.single q (1 : ℝ) : Fin n → ℝ)) i ^ 2 =
          ∑ i : Fin n, O i q ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Matrix.mulVec_single, Matrix.col_apply]
      have hrhs : ∑ i : Fin n, ((Pi.single q (1 : ℝ) : Fin n → ℝ) i) ^ 2 = 1 := by
        simp [Pi.single_apply]
      linarith
    have hpq_sum := hnorm ((Pi.single p (1 : ℝ) : Fin n → ℝ) + (Pi.single q (1 : ℝ) : Fin n → ℝ))
    have hlhs : ∑ i : Fin n, (O *ᵥ ((Pi.single p (1 : ℝ) : Fin n → ℝ) +
          (Pi.single q (1 : ℝ) : Fin n → ℝ))) i ^ 2 =
        ∑ i : Fin n, O i p ^ 2 + 2 * ∑ i : Fin n, O i p * O i q + ∑ i : Fin n, O i q ^ 2 := by
      have hpt : ∀ i : Fin n, (O *ᵥ ((Pi.single p (1 : ℝ) : Fin n → ℝ) +
            (Pi.single q (1 : ℝ) : Fin n → ℝ))) i ^ 2 =
          O i p ^ 2 + 2 * (O i p * O i q) + O i q ^ 2 := fun i => by
        rw [Matrix.mulVec_add, Pi.add_apply, Matrix.mulVec_single, Matrix.mulVec_single]
        simp only [MulOpposite.op_one, one_smul, Matrix.col_apply]
        ring
      calc
        ∑ i : Fin n, (O *ᵥ ((Pi.single p (1 : ℝ) : Fin n → ℝ) +
            (Pi.single q (1 : ℝ) : Fin n → ℝ))) i ^ 2 =
            ∑ i : Fin n, (O i p ^ 2 + 2 * (O i p * O i q) + O i q ^ 2) :=
          Finset.sum_congr rfl fun i _ => hpt i
        _ = ∑ i : Fin n, O i p ^ 2 + 2 * ∑ i : Fin n, O i p * O i q +
              ∑ i : Fin n, O i q ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
    have hrhs : ∑ i : Fin n, ((Pi.single p (1 : ℝ) : Fin n → ℝ) i +
          (Pi.single q (1 : ℝ) : Fin n → ℝ) i) ^ 2 = 2 := by
      have hpt : ∀ i : Fin n, ((Pi.single p (1 : ℝ) : Fin n → ℝ) i +
            (Pi.single q (1 : ℝ) : Fin n → ℝ) i) ^ 2 =
          ((Pi.single p (1 : ℝ) : Fin n → ℝ) i) ^ 2 + ((Pi.single q (1 : ℝ) : Fin n → ℝ) i) ^ 2 :=
        fun i => by
          by_cases hip : i = p
          · subst hip; simp [hpq]
          · simp [hip]
      calc
        ∑ i : Fin n, ((Pi.single p (1 : ℝ) : Fin n → ℝ) i +
            (Pi.single q (1 : ℝ) : Fin n → ℝ) i) ^ 2 =
            ∑ i : Fin n, (((Pi.single p (1 : ℝ) : Fin n → ℝ) i) ^ 2 +
              ((Pi.single q (1 : ℝ) : Fin n → ℝ) i) ^ 2) :=
          Finset.sum_congr rfl fun i _ => hpt i
        _ = (∑ i : Fin n, ((Pi.single p (1 : ℝ) : Fin n → ℝ) i) ^ 2) +
              (∑ i : Fin n, ((Pi.single q (1 : ℝ) : Fin n → ℝ) i) ^ 2) := Finset.sum_add_distrib
        _ = 1 + 1 := by simp [Pi.single_apply]
        _ = 2 := by norm_num
    have hrhs' : ∑ i : Fin n, (((Pi.single p (1 : ℝ) : Fin n → ℝ) +
        (Pi.single q (1 : ℝ) : Fin n → ℝ)) i) ^ 2 = 2 := by
      simpa only [Pi.add_apply] using hrhs
    rw [if_neg_helper hpq]
    rw [hlhs, hrhs'] at hpq_sum
    linarith
where
  if_neg_helper {a b : Fin n} (h : a ≠ b) : (if a = b then (1 : ℝ) else 0) = 0 := by
    split_ifs with hab
    · exact (h hab).elim
    · rfl

/-- **Klein §3 Complete Cayley–Klein Subordination Theorem (Converse + Forward)**:
a projective matrix `M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ` fixes the hyperplane at infinity
`H_∞` (`M 0 j.succ = 0`, `M 0 0 ≠ 0`) and preserves the spherical quadric `∑ xᵢ² = 0` inside `H_∞`
with real multiplier `(r : ℝ) ^ 2` (`r ∈ ℝˣ`) IF AND ONLY IF there exists `g : EuclideanSimilarity n`
such that `∀ x : Fin n → ℝ, M *ᵥ Fin.cons 1 x = M 0 0 • Fin.cons 1 (g • x)`. -/
theorem klein_sec3_principal_group_iff_spherical_absolute {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ha : M 0 0 ≠ 0) :
    ((∀ j : Fin n, M 0 j.succ = 0) ∧
      ∃ r : ℝˣ, ∀ v : Fin n → ℝ,
        ∑ i : Fin n, (M *ᵥ Fin.cons (0 : ℝ) v) i.succ ^ 2 =
          (r : ℝ) ^ 2 * ∑ i : Fin n, (v i) ^ 2) ↔
    ∃ g : EuclideanSimilarity n, ∀ x : Fin n → ℝ,
      M *ᵥ Fin.cons (1 : ℝ) x = M 0 0 • Fin.cons (1 : ℝ) (g • x) := by
  constructor
  · rintro ⟨hinf, r, hsph⟩
    let Omat : Matrix (Fin n) (Fin n) ℝ := fun i j => M i.succ j.succ / (r : ℝ)
    have hO_norm : ∀ v : Fin n → ℝ, ∑ i : Fin n, (Omat *ᵥ v) i ^ 2 = ∑ i : Fin n, (v i) ^ 2 :=
      fun v => by
        have hMv : ∀ i : Fin n, (Omat *ᵥ v) i = (M *ᵥ Fin.cons (0 : ℝ) v) i.succ / (r : ℝ) :=
          fun i => by
            rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, Omat, Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ => by ring
        have hsum : ∑ i : Fin n, (Omat *ᵥ v) i ^ 2 =
            (∑ i : Fin n, (M *ᵥ Fin.cons (0 : ℝ) v) i.succ ^ 2) / (r : ℝ) ^ 2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => by rw [hMv i, div_pow]
        rw [hsum, hsph v]
        have hr2 : (r : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 r.ne_zero
        field_simp [hr2]
    let g : EuclideanSimilarity n :=
      { scale := Units.mk0 ((r : ℝ) / M 0 0) (div_ne_zero r.ne_zero ha)
        orth := ⟨Omat, orth_of_norm_preserving Omat hO_norm⟩
        trans := fun i => M i.succ 0 / M 0 0 }
    refine ⟨g, fun x => ?_⟩
    ext k
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, mul_one]
      have hzero : ∑ j : Fin n, M 0 j.succ * x j = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hinf j, zero_mul]
      rw [hzero, add_zero]
    · simp only [Fin.cons_succ, Fin.cons_zero, mul_one, Pi.smul_apply, smul_eq_mul]
      change M i.succ 0 + ∑ j : Fin n, M i.succ j.succ * x j =
        M 0 0 * ((g.scale : ℝ) * (Omat *ᵥ x) i + g.trans i)
      have hsc : M 0 0 * ((g.scale : ℝ) * (Omat *ᵥ x) i + g.trans i) =
          (r : ℝ) * (Omat *ᵥ x) i + M i.succ 0 := by
        have hg1 : M 0 0 * (g.scale : ℝ) = (r : ℝ) := by
          simp only [g, Units.val_mk0]
          field_simp [ha]
        have hg2 : M 0 0 * g.trans i = M i.succ 0 := by
          simp only [g]
          field_simp [ha]
        calc
          M 0 0 * ((g.scale : ℝ) * (Omat *ᵥ x) i + g.trans i) =
              (M 0 0 * (g.scale : ℝ)) * (Omat *ᵥ x) i + M 0 0 * g.trans i := by ring
          _ = (r : ℝ) * (Omat *ᵥ x) i + M i.succ 0 := by rw [hg1, hg2]
      rw [hsc, Matrix.mulVec, dotProduct, Finset.mul_sum]
      have hsum : (∑ j : Fin n, (r : ℝ) * (Omat i j * x j)) =
          ∑ j : Fin n, M i.succ j.succ * x j :=
        Finset.sum_congr rfl fun j _ => by
          dsimp [Omat]
          field_simp [r.ne_zero]
      rw [hsum, add_comm]
  · rintro ⟨g, hg⟩
    have hinf : ∀ j : Fin n, M 0 j.succ = 0 := fun j => by
      have h0 := congrArg (fun u => u 0) (hg 0)
      have hj := congrArg (fun u => u 0) (hg (Pi.single j (1 : ℝ)))
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, mul_one,
        Pi.smul_apply, smul_eq_mul] at h0 hj
      have hsum : ∑ k : Fin n, M 0 k.succ * (Pi.single j (1 : ℝ) : Fin n → ℝ) k = M 0 j.succ := by
        rw [Finset.sum_eq_single j (fun k _ hkj => by simp [hkj])
          (fun h => (h (Finset.mem_univ j)).elim)]
        simp
      rw [hsum] at hj
      linarith
    refine ⟨hinf, Units.mk0 (M 0 0 * (g.scale : ℝ)) (mul_ne_zero ha g.scale.ne_zero), fun v => ?_⟩
    have hdiff : ∀ i : Fin n, (M *ᵥ Fin.cons 0 v) i.succ =
        M 0 0 * (g.scale : ℝ) * (g.orth.1 *ᵥ v) i := fun i => by
      have hv := congrArg (fun u => u i.succ) (hg v)
      have h0 := congrArg (fun u => u i.succ) (hg 0)
      have hlhs : (M *ᵥ Fin.cons 1 v) i.succ - (M *ᵥ Fin.cons 1 0) i.succ =
          (M *ᵥ Fin.cons 0 v) i.succ := by
        rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          add_zero, mul_one, zero_add]
        ring
      have hrhs : (M 0 0 • Fin.cons 1 (g • v)) i.succ - (M 0 0 • Fin.cons 1 (g • 0)) i.succ =
          M 0 0 * (g.scale : ℝ) * (g.orth.1 *ᵥ v) i := by
        simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul]
        change M 0 0 * ((g.scale : ℝ) * (g.orth.1 *ᵥ v) i + g.trans i) -
            M 0 0 * ((g.scale : ℝ) * (g.orth.1 *ᵥ 0) i + g.trans i) =
          M 0 0 * (g.scale : ℝ) * (g.orth.1 *ᵥ v) i
        rw [Matrix.mulVec_zero]
        simp only [Pi.zero_apply, mul_zero, zero_add]
        ring
      rw [← hlhs, hv, h0, hrhs]
    calc
      ∑ i : Fin n, (M *ᵥ Fin.cons 0 v) i.succ ^ 2 =
          ∑ i : Fin n, (M 0 0 * (g.scale : ℝ) * (g.orth.1 *ᵥ v) i) ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [hdiff i]
      _ = ((Units.mk0 (M 0 0 * (g.scale : ℝ)) (mul_ne_zero ha g.scale.ne_zero) : ℝˣ) : ℝ) ^ 2 *
            ∑ i : Fin n, (g.orth.1 *ᵥ v) i ^ 2 := by
        simp only [Units.val_mk0, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      _ = ((Units.mk0 (M 0 0 * (g.scale : ℝ)) (mul_ne_zero ha g.scale.ne_zero) : ℝˣ) : ℝ) ^ 2 *
            ∑ i : Fin n, (v i) ^ 2 := by rw [orth_mulVec_sq_sum]

end DualisticAndPrincipalGroup

/-! ## 3. `EK₃` (§2, §4, §5 & Fn. 23): Subgroup Adjoining, `Abbildung`, & Body Kernel -/

section ErlangenPrinciplesSec2_4_5

/-- **Klein §2 Subgroup Adjoining Principle**: studying a configuration `y : Y` together with an
evolving reference object `x : orbit G x₀` under `G` is in canonical bijection with studying `y`
alone under `MulAction.stabilizer G x₀`. -/
def klein_sec2_stabilizer_adjoining_equiv {G X Y β : Type*} [Group G] [MulAction G X]
    [MulAction G Y] (x₀ : X) :
    {F : Y × MulAction.orbit G x₀ → β // IsInvariantReadout G (Y × MulAction.orbit G x₀) F} ≃
      {f : Y → β // IsInvariantReadout (MulAction.stabilizer G x₀) Y f} where
  toFun F :=
    ⟨fun y => F.1 (y, ⟨x₀, MulAction.mem_orbit_self x₀⟩), fun h y => by
      have hfix : (h : G) • (⟨x₀, MulAction.mem_orbit_self x₀⟩ : MulAction.orbit G x₀) =
          ⟨x₀, MulAction.mem_orbit_self x₀⟩ := Subtype.ext h.2
      have := F.2 (h : G) (y, ⟨x₀, MulAction.mem_orbit_self x₀⟩)
      change F.1 ((h : G) • y, (h : G) • ⟨x₀, MulAction.mem_orbit_self x₀⟩) =
          F.1 (y, ⟨x₀, MulAction.mem_orbit_self x₀⟩) at this
      rw [hfix] at this
      exact this⟩
  invFun f :=
    ⟨fun ⟨y, x⟩ => f.1 ((Classical.choose x.2)⁻¹ • y), fun g ⟨y, x⟩ => by
      have hx1 : (Classical.choose (g • x).2 : G) • x₀ = g • x.1 :=
        (Classical.choose_spec (g • x).2)
      have hx0 : (Classical.choose x.2 : G) • x₀ = x.1 := (Classical.choose_spec x.2)
      have hstab : (Classical.choose (g • x).2)⁻¹ * (g * Classical.choose x.2) ∈
          MulAction.stabilizer G x₀ := by
        change ((Classical.choose (g • x).2)⁻¹ * (g * Classical.choose x.2)) • x₀ = x₀
        rw [mul_smul, mul_smul, hx0, ← hx1, inv_smul_smul]
      have hf := f.2 ⟨(Classical.choose (g • x).2)⁻¹ * (g * Classical.choose x.2), hstab⟩
        ((Classical.choose x.2)⁻¹ • y)
      change f.1 (((Classical.choose (g • x).2)⁻¹ * (g * Classical.choose x.2)) •
          ((Classical.choose x.2)⁻¹ • y)) = f.1 ((Classical.choose x.2)⁻¹ • y) at hf
      have hact : ((Classical.choose (g • x).2)⁻¹ * (g * Classical.choose x.2)) •
          ((Classical.choose x.2)⁻¹ • y) = (Classical.choose (g • x).2)⁻¹ • (g • y) := by
        rw [mul_smul, mul_smul, smul_inv_smul]
      rw [hact] at hf
      exact hf⟩
  left_inv F := by
    apply Subtype.ext
    funext ⟨y, x⟩
    have hx : (Classical.choose x.2 : G) • x₀ = x.1 := Classical.choose_spec x.2
    have horb : (Classical.choose x.2 : G) •
        (⟨x₀, MulAction.mem_orbit_self x₀⟩ : MulAction.orbit G x₀) = x :=
      Subtype.ext hx
    have hinv := F.2 (Classical.choose x.2) ((Classical.choose x.2)⁻¹ • y,
      ⟨x₀, MulAction.mem_orbit_self x₀⟩)
    change F.1 ((Classical.choose x.2 : G) • ((Classical.choose x.2)⁻¹ • y),
        (Classical.choose x.2 : G) • ⟨x₀, MulAction.mem_orbit_self x₀⟩) =
      F.1 ((Classical.choose x.2)⁻¹ • y, ⟨x₀, MulAction.mem_orbit_self x₀⟩) at hinv
    rw [smul_inv_smul, horb] at hinv
    exact hinv.symm
  right_inv f := by
    apply Subtype.ext
    funext y
    have hx0 : (Classical.choose (MulAction.mem_orbit_self x₀ :
        x₀ ∈ MulAction.orbit G x₀) : G) • x₀ = x₀ :=
      Classical.choose_spec (MulAction.mem_orbit_self x₀)
    have hinv_stab : (Classical.choose (MulAction.mem_orbit_self x₀ :
        x₀ ∈ MulAction.orbit G x₀))⁻¹ ∈ MulAction.stabilizer G x₀ :=
      Subgroup.inv_mem _ hx0
    exact f.2 ⟨_, hinv_stab⟩ y

/-- **Klein §4 Transfer by Representation (`Abbildung`)**: a bijection `φ : A ≃ A'` yields the
group isomorphism `Equiv.permCongrHom φ : Equiv.Perm A ≃* Equiv.Perm A'` transporting invariant
readouts between `A` and `A'`. -/
theorem klein_sec4_abbildung_perm_transfer {A A' β : Type*} (φ : A ≃ A')
    (G : Subgroup (Equiv.Perm A)) (f : A → β) :
    (∀ g ∈ G, ∀ x : A, f (g x) = f x) ↔
      (∀ g' ∈ Subgroup.map (Equiv.permCongrHom φ).toMonoidHom G, ∀ y : A', f (φ.symm (g' y)) =
        f (φ.symm y)) := by
  constructor
  · rintro hf _ ⟨g, hg, rfl⟩ y
    change f (φ.symm (φ (g (φ.symm y)))) = f (φ.symm y)
    rw [Equiv.symm_apply_apply]
    exact hf g hg (φ.symm y)
  · intro hf g hg x
    have hmem : Equiv.permCongrHom φ g ∈ Subgroup.map (Equiv.permCongrHom φ).toMonoidHom G :=
      ⟨g, hg, rfl⟩
    have h := hf (Equiv.permCongrHom φ g) hmem (φ x)
    change f (φ.symm (φ (g (φ.symm (φ x))))) = f (φ.symm (φ x)) at h
    simpa [Equiv.symm_apply_apply] using h

/-- **Klein §5 & Footnote 23 (Orbit Body Faithfulness Kernel = Normal Core)**:
on the body `MulAction.orbit G x₀`, the kernel of the permutation representation `G →* Perm(orbit)`
equals the normal core `(MulAction.stabilizer G x₀).normalCore`. In particular, any normal
subgroup `N ◁ G` fixing `x₀` fixes every element of the entire body. -/
theorem klein_sec5_fn23_body_kernel_eq_normalCore {G X : Type*} [Group G] [MulAction G X] (x₀ : X) :
    (MulAction.toPermHom G (MulAction.orbit G x₀)).ker =
        (MulAction.stabilizer G x₀).normalCore ∧
      ∀ (N : Subgroup G) [N.Normal], N ≤ MulAction.stabilizer G x₀ →
        N ≤ (MulAction.toPermHom G (MulAction.orbit G x₀)).ker := by
  have hker : (MulAction.toPermHom G (MulAction.orbit G x₀)).ker =
      (MulAction.stabilizer G x₀).normalCore := by
    rw [(MulAction.stabilizer G x₀).normalCore_eq_ker]
    ext g
    simp only [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
    constructor
    · intro hg q
      induction q using QuotientGroup.induction_on with
      | H h =>
        change g • (QuotientGroup.mk h : G ⧸ MulAction.stabilizer G x₀) =
          QuotientGroup.mk h
        rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
        have hpt := congrArg Subtype.val (hg ⟨h • x₀, h, rfl⟩)
        change g • (h • x₀) = h • x₀ at hpt
        have hinv_mem : h⁻¹ * (g * h) ∈ MulAction.stabilizer G x₀ := by
          change (h⁻¹ * (g * h)) • x₀ = x₀
          rw [mul_smul, mul_smul, hpt, inv_smul_smul]
        have hmem := (MulAction.stabilizer G x₀).inv_mem hinv_mem
        simpa [mul_inv_rev, mul_assoc] using hmem
    · intro hg ⟨_, h, rfl⟩
      apply Subtype.ext
      have hq := hg (QuotientGroup.mk h)
      change g • (QuotientGroup.mk h : G ⧸ MulAction.stabilizer G x₀) =
        QuotientGroup.mk h at hq
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hq
      have hmem : h⁻¹ * (g * h) ∈ MulAction.stabilizer G x₀ := by
        simpa [mul_inv_rev, mul_assoc] using (MulAction.stabilizer G x₀).inv_mem hq
      have hstab : (h⁻¹ * (g * h)) • x₀ = x₀ := hmem
      change g • (h • x₀) = h • x₀
      have := congrArg (fun z => h • z) hstab
      simpa [mul_smul, smul_inv_smul] using this
  refine ⟨hker, fun N hN hle => ?_⟩
  rw [hker]
  exact Subgroup.normal_le_normalCore.mpr hle

/-- **Projective Body Unfaithfulness (`[countermodel_found]`)**: `-1 : GL(2, ℚ)` acts nontrivially
on `Fin 2 → ℚ` yet lies in the kernel of `GL(2, ℚ)` acting on `ℙ ℚ (Fin 2 → ℚ)`. -/
theorem gl2_neg_one_acts_nontrivially_yet_fixes_projective_body :
    ((-1 : Matrix.GeneralLinearGroup (Fin 2) ℚ) • (![1, 0] : Fin 2 → ℚ) ≠
        (![1, 0] : Fin 2 → ℚ)) ∧
      ∀ p : ℙ ℚ (Fin 2 → ℚ), (-1 : Matrix.GeneralLinearGroup (Fin 2) ℚ) • p = p := by
  refine ⟨?_, fun p => ?_⟩
  · intro h
    have h0 := congrArg (fun v : Fin 2 → ℚ => v 0) h
    norm_num at h0
  · induction p using Projectivization.ind with
    | h v hv =>
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
      refine ⟨-1, ?_⟩
      ext i
      simp [Units.smul_def]

end ErlangenPrinciplesSec2_4_5

/-! ## 4. `EK₄` (§4, §5 & Note V): Veronese Conic, Hesse Transference, & Plücker–Klein Duality -/

section VeroneseHesseJacobiDuality

section CommRing

variable {R : Type*} [CommRing R]

/-- Veronese embedding `[u : v] ↦ [u² : u v : v²]` onto the rational normal conic in `R³`. -/
def veroneseVec (u v : R) : Fin 3 → R :=
  ![u ^ 2, u * v, v ^ 2]

/-- Rational normal conic quadratic form `X₀ X₂ - X₁²` vanishing on `veroneseVec`. -/
def conicForm (X : Fin 3 → R) : R :=
  X 0 * X 2 - (X 1) ^ 2

theorem conicForm_veroneseVec (u v : R) : conicForm (veroneseVec u v) = 0 := by
  dsimp [conicForm, veroneseVec]
  ring

/-- Induced symmetric-square matrix `Sym²(A)` on `(u², u v, v²)` for `A : Matrix (Fin 2) (Fin 2) R`. -/
def sym2Mat (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  ![![A 0 0 ^ 2, 2 * A 0 0 * A 0 1, A 0 1 ^ 2],
    ![A 0 0 * A 1 0, A 0 0 * A 1 1 + A 0 1 * A 1 0, A 0 1 * A 1 1],
    ![A 1 0 ^ 2, 2 * A 1 0 * A 1 1, A 1 1 ^ 2]]

theorem sym2Mat_one : sym2Mat (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym2Mat]

theorem sym2Mat_mul (A B : Matrix (Fin 2) (Fin 2) R) :
    sym2Mat (A * B) = sym2Mat A * sym2Mat B := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [sym2Mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sym2Mat_det (A : Matrix (Fin 2) (Fin 2) R) :
    (sym2Mat A).det = A.det ^ 3 := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [sym2Mat]
  ring

theorem sym2Mat_mulVec_veronese (A : Matrix (Fin 2) (Fin 2) R) (u v : R) :
    sym2Mat A *ᵥ veroneseVec u v =
      veroneseVec (A 0 0 * u + A 0 1 * v) (A 1 0 * u + A 1 1 * v) := by
  ext i
  fin_cases i <;>
    simp [sym2Mat, veroneseVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem conicForm_sym2Mat (A : Matrix (Fin 2) (Fin 2) R) (X : Fin 3 → R) :
    conicForm (sym2Mat A *ᵥ X) = A.det ^ 2 * conicForm X := by
  rw [Matrix.det_fin_two]
  simp only [conicForm, sym2Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Group homomorphism `GL(2, R) →* GL(3, R)` realizing the Erlangen conic transfer `§4`. -/
def sym2GL2 (R : Type*) [CommRing R] :
    Matrix.GeneralLinearGroup (Fin 2) R →* Matrix.GeneralLinearGroup (Fin 3) R where
  toFun g :=
    { val := sym2Mat g.1
      inv := sym2Mat g⁻¹.1
      val_inv := by rw [← sym2Mat_mul, Units.mul_inv, sym2Mat_one]
      inv_val := by rw [← sym2Mat_mul, Units.inv_mul, sym2Mat_one] }
  map_one' := by
    apply Units.ext
    exact sym2Mat_one
  map_mul' g h := by
    apply Units.ext
    exact sym2Mat_mul g.1 h.1

/-- **Hesse's Principle of Transference (`§5`)**: unordered point-pair `(u₁, v₁), (u₂, v₂)`
encoded by elementary symmetric coefficients `(u₁ u₂, u₁ v₂ + u₂ v₁, v₁ v₂) ∈ R³`. -/
def hessePairPoint (u₁ v₁ u₂ v₂ : R) : Fin 3 → R :=
  ![u₁ * u₂, u₁ * v₂ + u₂ * v₁, v₁ * v₂]

/-- Discriminant quadratic form `4 P₀ P₂ - P₁²` for Hesse transference. -/
def hesseDiscForm (P : Fin 3 → R) : R :=
  4 * P 0 * P 2 - (P 1) ^ 2

/-- Dual symmetric-square matrix transforming `hessePairPoint` equivariantly under `GL(2, R)`. -/
def hesseMat (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  ![![A 0 0 ^ 2, A 0 0 * A 0 1, A 0 1 ^ 2],
    ![2 * A 0 0 * A 1 0, A 0 0 * A 1 1 + A 0 1 * A 1 0, 2 * A 0 1 * A 1 1],
    ![A 1 0 ^ 2, A 1 0 * A 1 1, A 1 1 ^ 2]]

theorem hesse_transference_theorems (A : Matrix (Fin 2) (Fin 2) R) (u₁ v₁ u₂ v₂ s t : R) :
    hessePairPoint u₁ v₁ u₂ v₂ = hessePairPoint u₂ v₂ u₁ v₁ ∧
      hesseMat A *ᵥ hessePairPoint u₁ v₁ u₂ v₂ =
        hessePairPoint (A 0 0 * u₁ + A 0 1 * v₁) (A 1 0 * u₁ + A 1 1 * v₁)
          (A 0 0 * u₂ + A 0 1 * v₂) (A 1 0 * u₂ + A 1 1 * v₂) ∧
      hesseDiscForm (hessePairPoint u₁ v₁ u₂ v₂) = -(u₁ * v₂ - u₂ * v₁) ^ 2 ∧
      (t ^ 2 * (hessePairPoint u₁ v₁ u₂ v₂) 0 - s * t * (hessePairPoint u₁ v₁ u₂ v₂) 1 +
          s ^ 2 * (hessePairPoint u₁ v₁ u₂ v₂) 2 =
        (s * v₁ - t * u₁) * (s * v₂ - t * u₂)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [hessePairPoint] <;> ring
  · ext i
    fin_cases i <;> simp [hesseMat, hessePairPoint, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      ring
  · dsimp [hesseDiscForm, hessePairPoint]
    ring
  · dsimp [hessePairPoint]
    ring

/-- **Plücker–Klein Hodge Correlation Duality (`§5`)**: involutive map on `Plucker6 R` representing
a dualistic projective correlation `u ∧ v ↦ *(u ∧ v)` preserving the Klein quadric. -/
def kleinHodgeDual (P : Plucker6 R) : Plucker6 R where
  p01 := P.p23
  p02 := -P.p13
  p03 := P.p12
  p12 := P.p03
  p13 := -P.p02
  p23 := P.p01

theorem kleinHodgeDual_theorems (A : Matrix (Fin 4) (Fin 4) R) (P : Plucker6 R) :
    kleinHodgeDual (kleinHodgeDual P) = P ∧
      Plucker6.kleinQ (kleinHodgeDual P) = Plucker6.kleinQ P ∧
      kleinHodgeDual (compound Aᵀ (kleinHodgeDual (compound A P))) = Plucker6.scale A.det P := by
  refine ⟨?_, ?_, ?_⟩
  · rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
    apply Plucker6.ext <;> simp [kleinHodgeDual]
  · rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
    dsimp [kleinHodgeDual, Plucker6.kleinQ]
    ring
  · rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
    have hdet := DahmPluckerKleinCollineation.det_fin_four A
    apply Plucker6.ext <;>
      simp only [kleinHodgeDual, compound, compoundRow, minor2, Matrix.transpose_apply,
        Plucker6.scale, hdet] <;> ring

end CommRing

end VeroneseHesseJacobiDuality

/-! ## 5. `EK₅` (§10.1 & Note VI): Sharp 3-Transitivity of `PGL(2, K)` & Boundary Collapse -/

section SharpThreeTransitivityAndNoteVI

variable {K : Type*} [Field K]

/-- Explicit `2 × 2` matrix over `K` mapping `(1,0), (0,1), (1,1)` projectively to any three
pairwise-distinct points `P₁, P₂, P₃ : HomPoint2 K`. -/
def pgl2FrameMatrix (P₁ P₂ P₃ : HomPoint2 K) : Matrix (Fin 2) (Fin 2) K :=
  let α := HomPoint2.bracket P₃ P₂
  let β := HomPoint2.bracket P₁ P₃
  ![![α * P₁.x, β * P₂.x], ![α * P₁.y, β * P₂.y]]

/-- **Sharp 3-Transitivity of `PGL(2, K)`**: for any three pairwise projectively distinct points
`P₁, P₂, P₃ : HomPoint2 K` (non-vanishing pairwise brackets), `pgl2FrameMatrix P₁ P₂ P₃` has nonzero
determinant and sends `(1,0), (0,1), (1,1)` to nonzero scalar multiples of `P₁, P₂, P₃`. Moreover,
any invertible `M` fixing `(1,0), (0,1), (1,1)` projectively is a nonzero scalar multiple of `1`. -/
theorem pgl2_three_transitive (P₁ P₂ P₃ : HomPoint2 K)
    (h12 : HomPoint2.bracket P₁ P₂ ≠ 0)
    (h23 : HomPoint2.bracket P₂ P₃ ≠ 0)
    (h31 : HomPoint2.bracket P₃ P₁ ≠ 0) :
    (pgl2FrameMatrix P₁ P₂ P₃).det ≠ 0 ∧
      HomPoint2.lin (pgl2FrameMatrix P₁ P₂ P₃ 0 0) (pgl2FrameMatrix P₁ P₂ P₃ 0 1)
          (pgl2FrameMatrix P₁ P₂ P₃ 1 0) (pgl2FrameMatrix P₁ P₂ P₃ 1 1) ⟨1, 0⟩ =
        HomPoint2.scale (HomPoint2.bracket P₃ P₂) P₁ ∧
      HomPoint2.lin (pgl2FrameMatrix P₁ P₂ P₃ 0 0) (pgl2FrameMatrix P₁ P₂ P₃ 0 1)
          (pgl2FrameMatrix P₁ P₂ P₃ 1 0) (pgl2FrameMatrix P₁ P₂ P₃ 1 1) ⟨0, 1⟩ =
        HomPoint2.scale (HomPoint2.bracket P₁ P₃) P₂ ∧
      HomPoint2.lin (pgl2FrameMatrix P₁ P₂ P₃ 0 0) (pgl2FrameMatrix P₁ P₂ P₃ 0 1)
          (pgl2FrameMatrix P₁ P₂ P₃ 1 0) (pgl2FrameMatrix P₁ P₂ P₃ 1 1) ⟨1, 1⟩ =
        HomPoint2.scale (HomPoint2.bracket P₁ P₂) P₃ := by
  have h32 : HomPoint2.bracket P₃ P₂ ≠ 0 := by
    intro h
    apply h23
    have hswap : HomPoint2.bracket P₂ P₃ = -HomPoint2.bracket P₃ P₂ := by
      dsimp [HomPoint2.bracket]; ring
    rw [hswap, h, neg_zero]
  have h13 : HomPoint2.bracket P₁ P₃ ≠ 0 := by
    intro h
    apply h31
    have hswap : HomPoint2.bracket P₃ P₁ = -HomPoint2.bracket P₁ P₃ := by
      dsimp [HomPoint2.bracket]; ring
    rw [hswap, h, neg_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hdet : (pgl2FrameMatrix P₁ P₂ P₃).det =
        HomPoint2.bracket P₃ P₂ * HomPoint2.bracket P₁ P₃ * HomPoint2.bracket P₁ P₂ := by
      rw [Matrix.det_fin_two]
      dsimp [pgl2FrameMatrix, HomPoint2.bracket]
      ring
    rw [hdet]
    exact mul_ne_zero (mul_ne_zero h32 h13) h12
  · simp [HomPoint2.lin, HomPoint2.scale, pgl2FrameMatrix]
  · simp [HomPoint2.lin, HomPoint2.scale, pgl2FrameMatrix]
  · have hx : (pgl2FrameMatrix P₁ P₂ P₃ 0 0 * 1 + pgl2FrameMatrix P₁ P₂ P₃ 0 1 * 1) =
        HomPoint2.bracket P₁ P₂ * P₃.x := by
      dsimp [pgl2FrameMatrix, HomPoint2.bracket]
      ring
    have hy : (pgl2FrameMatrix P₁ P₂ P₃ 1 0 * 1 + pgl2FrameMatrix P₁ P₂ P₃ 1 1 * 1) =
        HomPoint2.bracket P₁ P₂ * P₃.y := by
      dsimp [pgl2FrameMatrix, HomPoint2.bracket]
      ring
    change ({ x := _, y := _ } : HomPoint2 K) = HomPoint2.scale (HomPoint2.bracket P₁ P₂) P₃
    rw [hx, hy]
    rfl

theorem pgl2_fix_three_basepoints_is_scalar (a b c d c₁ c₂ c₃ : K)
    (hc₃ : c₃ ≠ 0)
    (h10 : HomPoint2.lin a b c d ⟨1, 0⟩ = HomPoint2.scale c₁ ⟨1, 0⟩)
    (h01 : HomPoint2.lin a b c d ⟨0, 1⟩ = HomPoint2.scale c₂ ⟨0, 1⟩)
    (h11 : HomPoint2.lin a b c d ⟨1, 1⟩ = HomPoint2.scale c₃ ⟨1, 1⟩) :
    a = c₃ ∧ b = 0 ∧ c = 0 ∧ d = c₃ ∧ c₁ = c₃ ∧ c₂ = c₃ ∧ c₃ ≠ 0 := by
  have ha_mul : a = c₁ := by simpa [HomPoint2.lin, HomPoint2.scale] using congrArg HomPoint2.x h10
  have hc0 : c = 0 := by simpa [HomPoint2.lin, HomPoint2.scale] using congrArg HomPoint2.y h10
  have hb0 : b = 0 := by simpa [HomPoint2.lin, HomPoint2.scale] using congrArg HomPoint2.x h01
  have hd_mul : d = c₂ := by simpa [HomPoint2.lin, HomPoint2.scale] using congrArg HomPoint2.y h01
  have hx11 := congrArg HomPoint2.x h11
  have hy11 := congrArg HomPoint2.y h11
  simp only [HomPoint2.lin, HomPoint2.scale, mul_one, hb0, add_zero, hc0, zero_add] at hx11 hy11
  exact ⟨hx11, hb0, hc0, hy11, ha_mul.symm.trans hx11, hd_mul.symm.trans hy11, hc₃⟩

/-- **Klein Note VI Impossibility Theorem (`pp. 24–25`)**: any projective (`GL(2, K)`- and
scale-invariant) invariant `I` of three pairwise distinct points on `ℙ¹(K)` (and equivalently on a
rational normal conic) is globally constant. Furthermore, the four-point cross-ratio collapses on
the quadric diagonal `P₃ = P₁`, whereas adjoining an auxiliary quadratic pole `u₁ u₂ + κ v₁ v₂`
restores a genuine non-constant two-point invariant for `κ ≠ 0`. -/
theorem klein_noteVI_triple_invariant_const {β : Type*}
    (I : HomPoint2 K → HomPoint2 K → HomPoint2 K → β)
    (hscale : ∀ (l₁ l₂ l₃ : K), l₁ ≠ 0 → l₂ ≠ 0 → l₃ ≠ 0 →
      ∀ P₁ P₂ P₃ : HomPoint2 K,
        I (HomPoint2.scale l₁ P₁) (HomPoint2.scale l₂ P₂) (HomPoint2.scale l₃ P₃) = I P₁ P₂ P₃)
    (hgl : ∀ (a b c d : K), a * d - b * c ≠ 0 → ∀ P₁ P₂ P₃ : HomPoint2 K,
      I (HomPoint2.lin a b c d P₁) (HomPoint2.lin a b c d P₂) (HomPoint2.lin a b c d P₃) =
        I P₁ P₂ P₃)
    (P₁ P₂ P₃ : HomPoint2 K)
    (h12 : HomPoint2.bracket P₁ P₂ ≠ 0)
    (h23 : HomPoint2.bracket P₂ P₃ ≠ 0)
    (h31 : HomPoint2.bracket P₃ P₁ ≠ 0) :
    I P₁ P₂ P₃ = I ⟨1, 0⟩ ⟨0, 1⟩ ⟨1, 1⟩ := by
  have ht := pgl2_three_transitive P₁ P₂ P₃ h12 h23 h31
  let M := pgl2FrameMatrix P₁ P₂ P₃
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
    rw [← Matrix.det_fin_two]
    exact ht.1
  have hlhs := hgl (M 0 0) (M 0 1) (M 1 0) (M 1 1) hdet ⟨1, 0⟩ ⟨0, 1⟩ ⟨1, 1⟩
  rw [ht.2.1, ht.2.2.1, ht.2.2.2] at hlhs
  have h32 : HomPoint2.bracket P₃ P₂ ≠ 0 := fun h => by
    apply h23
    have hsw : HomPoint2.bracket P₂ P₃ = -HomPoint2.bracket P₃ P₂ := by
      dsimp [HomPoint2.bracket]; ring
    rw [hsw, h, neg_zero]
  have h13 : HomPoint2.bracket P₁ P₃ ≠ 0 := fun h => by
    apply h31
    have hsw : HomPoint2.bracket P₃ P₁ = -HomPoint2.bracket P₁ P₃ := by
      dsimp [HomPoint2.bracket]; ring
    rw [hsw, h, neg_zero]
  rw [hscale _ _ _ h32 h13 h12 P₁ P₂ P₃] at hlhs
  exact hlhs

theorem klein_noteVI_boundary_collapse_and_pole_metric
    (P₁ P₂ P₄ : HomPoint2 K) :
    HomPoint2.crossNum P₁ P₂ P₁ P₄ = 0 ∧
      ((∃ u₁ v₁ u₂ v₂ : ℚ,
        (u₁ * u₂ + v₁ * v₂) ^ 2 / ((u₁ ^ 2 + v₁ ^ 2) * (u₂ ^ 2 + v₂ ^ 2)) ≠
          (u₁ * 1 + v₁ * 0) ^ 2 / ((u₁ ^ 2 + v₁ ^ 2) * (1 ^ 2 + 0 ^ 2)))) := by
  refine ⟨?_, ?_⟩
  · unfold HomPoint2.crossNum HomPoint2.bracket
    ring
  · refine ⟨1, 2, 0, 1, ?_⟩
    norm_num

end SharpThreeTransitivityAndNoteVI

end InfoGeometry.Projective.KleinErlangenProgramGroupsAndProjectiveTransfer
