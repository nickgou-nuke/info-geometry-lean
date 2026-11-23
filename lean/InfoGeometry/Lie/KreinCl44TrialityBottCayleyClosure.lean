/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
import InfoGeometry.Clifford.SplitQ44
import InfoGeometry.Clifford.Cl44Witt

/-!
# Krein Cl(4,4) Triality, Real Bott-0 Closure, Cayley 4-Form, and Turn 14 Poset

## i. Overview

This module establishes the five closure targets `M1b-T14-C1` through `M1b-T14-C5`
built directly on the `Cl(4,4)` Krein-spinor representation in
`InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis` and the split quadratic form
`InfoGeometry.Clifford.splitQ44`:
real Bott-0 periodicity `Cl(4,4) ≃ₐ[ℝ] M₁₆(ℝ)` with chiral `Γ_{4,4}` even splitting into
`M₈(ℝ) × M₈(ℝ)`, the strict uncalibrated matrix derivation ladder `14 < 28 < 120 < 255`,
intrinsic Cartan `S₃` outer triality automorphisms on `cl44BivectorLieSubalgebra` isolating
`g_{2(2)}` as the 14-dimensional fixed Lie subalgebra, generic Cartan eigen-grading commutativity
together with the `G_{2(2)}`-invariant Cayley 4-form in `Cl⁽⁴⁾(4,4)`, and the exact Turn 14
15-node, 28-edge graded Hasse poset.

## ii. Key results

- `cl44AlgEquivMat16`, `gamma44CommutantEquivProdMat8`, `gamma44_commutant_finrank`:
  real Bott-0 isomorphism `Cl(4,4) ≃ₐ[ℝ] M₁₆(ℝ)` and `128`-dimensional chiral even
  commutant splitting `M₈(ℝ) × M₈(ℝ)` (`M1b-T14-C1`).
- `derivation_dimension_ladder_strict`: strict inclusion and `Module.finrank` ladder
  `14 < 28 < 120 < 255` from `g2Submodule` to `sl16Subalgebra` (`M1b-T14-C2`).
- `trialitySigma3`, `trialityTau3`, `triality_s3_relations`,
  `trialityFixedEquivG2LieSubalgebra`: intrinsic `S₃` outer Lie automorphisms on
  `cl44BivectorLieSubalgebra` with 14-dimensional fixed subalgebra `≃ₗ⁅ℝ⁆ g2LieSubalgebra`
  (`M1b-T14-C3`).
- `simultaneous_eigen_grading_commutator_annihilates`, `centerless_cartan_commutes`,
  `finrank_cl44Grade4Span`, `cayleyFourFormCl44_properties`: Cartan commutativity from
  simultaneous eigen-grading and the `G_{2(2)}`-invariant Cayley 4-form (`M1b-T14-C4`).
- `Turn14KreinPosetNode`, `turn14_covers_transitively_reduced_and_isLUB`: exact 15-node,
  28-edge Turn 14 Hasse poset with transitive reduction and `{H, E}` supremum `XiTop`
  (`M1b-T14-C5`).

## iii. Table of contents

1. Real Bott-0 Isomorphism `Cl(4,4) ≃ₐ[ℝ] M₁₆(ℝ)` and Even Splitting (`M1b-T14-C1`).
2. Uncalibrated Derivation Dimension Ladder in `M₁₆(ℝ)` (`M1b-T14-C2`).
3. Intrinsic Cartan `S₃` Outer Triality on `cl44BivectorLieSubalgebra` (`M1b-T14-C3`).
4. Generic Cartan Eigen-Grading and `G_{2(2)}`-Invariant Cayley 4-Form (`M1b-T14-C4`).
5. Exact Turn 14 28-Edge 15-Node Hasse Poset Alignment (`M1b-T14-C5`).

## iv. References

- `InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis`
- `InfoGeometry.Clifford.SplitQ44`
- `InfoGeometry.Clifford.Cl44Witt`
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Lie.KreinCl44TrialityBottCayleyClosure

open InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### 1. Real Bott-0 Isomorphism `Cl(4,4) ≃ₐ[ℝ] M₁₆(ℝ)` and Even Splitting (`M1b-T14-C1`) -/

/-- The centralizer of `gamma44` inside `M₁₆(ℝ)`, representing the chiral even subalgebra. -/
def gamma44CommutantSubalgebra : Subalgebra ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Subalgebra.centralizer ℝ ({gamma44} : Set (Matrix Krein16Idx Krein16Idx ℝ))

/-- Trace orthogonality `Tr(η̂_{8,8} · Γ_{4,4}) = 0` distinguishing the Krein metric
from the chiral grading operator. -/
lemma kreinMetric88_mul_gamma44_trace_zero :
    Matrix.trace (kreinMetric88 * gamma44) = 0 := by
  unfold kreinMetric88 gamma44
  rw [tensor4_mul, cl11Pos_mul_cl11Grad, cl11Neg_mul_cl11Grad, tensor4_trace,
    cl11Neg_trace, cl11Pos_trace]
  norm_num

/-- Recursive Clifford monomial ordered by ascending generator index `k..7` for any
family of Clifford generators `g : Fin 8 → A`. -/
def clMonomialGenFrom {A : Type*} [Ring A] (g : Fin 8 → A) (k : ℕ) (m : Fin 8 → Bool) : A :=
  if hk : k < 8 then
    (if m ⟨k, hk⟩ then g ⟨k, hk⟩ else 1) * clMonomialGenFrom g (k + 1) m
  else 1
termination_by 8 - k

/-- Explicit `Cl(4,4)` basis monomial in `M₁₆(ℝ)` indexed by `m : Fin 8 → Bool`. -/
def clMonomial (m : Fin 8 → Bool) : Matrix Krein16Idx Krein16Idx ℝ :=
  clMonomialGenFrom cl44Gen 0 m

private lemma clMonomialGenFrom_ge {A : Type*} [Ring A] (g : Fin 8 → A) (k : ℕ)
    (hk : 8 ≤ k) (m : Fin 8 → Bool) : clMonomialGenFrom g k m = 1 := by
  unfold clMonomialGenFrom
  simp [Nat.not_lt.mpr hk]

private lemma clMonomialGenFrom_step {A : Type*} [Ring A] (g : Fin 8 → A) (k : ℕ)
    (hk : k < 8) (m : Fin 8 → Bool) :
    clMonomialGenFrom g k m =
      (if m ⟨k, hk⟩ then g ⟨k, hk⟩ else 1) * clMonomialGenFrom g (k + 1) m := by
  conv_lhs => unfold clMonomialGenFrom
  simp [hk]

private lemma clMonomialGenFrom_congr {A : Type*} [Ring A] (g : Fin 8 → A)
    {k : ℕ} {m₁ m₂ : Fin 8 → Bool}
    (h : ∀ j : Fin 8, k ≤ j.val → m₁ j = m₂ j) :
    clMonomialGenFrom g k m₁ = clMonomialGenFrom g k m₂ := by
  induction hk_rem : 8 - k generalizing k with
  | zero =>
      have hk : 8 ≤ k := by omega
      rw [clMonomialGenFrom_ge g k hk, clMonomialGenFrom_ge g k hk]
  | succ d ih =>
      have hk : k < 8 := by omega
      rw [clMonomialGenFrom_step g k hk m₁, clMonomialGenFrom_step g k hk m₂]
      rw [h ⟨k, hk⟩ (le_refl k)]
      congr 1
      apply ih (k := k + 1) (fun j hj => h j (by omega))
      omega

private lemma clMonomialGenFrom_map {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    (F : A →ₐ[ℝ] B) (g : Fin 8 → A) (k : ℕ) (m : Fin 8 → Bool) :
    F (clMonomialGenFrom g k m) = clMonomialGenFrom (fun i => F (g i)) k m := by
  induction hk_rem : 8 - k generalizing k with
  | zero =>
      have hk : 8 ≤ k := by omega
      rw [clMonomialGenFrom_ge g k hk, clMonomialGenFrom_ge _ k hk, map_one]
  | succ d ih =>
      have hk : k < 8 := by omega
      rw [clMonomialGenFrom_step g k hk m, clMonomialGenFrom_step _ k hk m, map_mul]
      have hhead : F (if m ⟨k, hk⟩ then g ⟨k, hk⟩ else 1) =
          if m ⟨k, hk⟩ then F (g ⟨k, hk⟩) else 1 := by
        by_cases hm : m ⟨k, hk⟩ <;> simp [hm]
      rw [hhead, ih (k := k + 1) (by omega)]

private lemma clMonomialGenFrom_mul_gen {A : Type*} [Ring A] [Algebra ℝ A]
    (g : Fin 8 → A)
    (hsq : ∀ a : Fin 8, g a * g a = if a.val < 4 then 1 else -1)
    (hanti : ∀ {a b : Fin 8}, a ≠ b → g a * g b + g b * g a = 0)
    (i : Fin 8) (k : ℕ) (hk : k ≤ i.val) (m : Fin 8 → Bool) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      g i * clMonomialGenFrom g k m =
        s • clMonomialGenFrom g k (Function.update m i (!m i)) := by
  induction hd : i.val - k generalizing k with
  | zero =>
      have hki : k = i.val := le_antisymm hk (Nat.le_of_sub_eq_zero hd)
      have hk8 : k < 8 := lt_of_le_of_lt hk i.isLt
      have hidx : (⟨k, hk8⟩ : Fin 8) = i := Fin.ext hki
      have htail : clMonomialGenFrom g (k + 1) (Function.update m i (!m i)) =
          clMonomialGenFrom g (k + 1) m := by
        apply clMonomialGenFrom_congr
        intro j hj
        have hji : j ≠ i := by
          intro h
          subst h
          omega
        simp [Function.update_of_ne hji]
      rw [clMonomialGenFrom_step g k hk8 m,
        clMonomialGenFrom_step g k hk8 (Function.update m i (!m i)), hidx, htail]
      by_cases hmi : m i
      · have hsq' : g i * g i = (if i.val < 4 then (1 : ℝ) else -1) • (1 : A) := by
          rw [hsq i]
          split_ifs <;> simp
        refine ⟨if i.val < 4 then 1 else -1, by split_ifs <;> simp, ?_⟩
        simp only [hmi, ↓reduceIte, Function.update_self, Bool.not_true, Bool.false_eq_true,
          one_mul]
        rw [← mul_assoc, hsq', smul_mul_assoc, one_mul]
      · have hmi' : m i = false := Bool.eq_false_iff.mpr hmi
        refine ⟨1, Or.inl rfl, ?_⟩
        simp [hmi', Function.update_self]
  | succ d ih =>
      have hk8 : k < 8 := by omega
      have hki : (⟨k, hk8⟩ : Fin 8) ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        dsimp at hv
        omega
      rcases ih (k + 1) (by omega) (by omega) with ⟨s, hs, hrec⟩
      rw [clMonomialGenFrom_step g k hk8 m,
        clMonomialGenFrom_step g k hk8 (Function.update m i (!m i)),
        Function.update_of_ne hki]
      by_cases hmk : m ⟨k, hk8⟩
      · have hcomm : g i * g ⟨k, hk8⟩ = (-1 : ℝ) • (g ⟨k, hk8⟩ * g i) := by
          have ha := eq_neg_of_add_eq_zero_left (hanti hki.symm)
          rw [ha, neg_one_smul]
        refine ⟨-s, by rcases hs with rfl | rfl <;> simp, ?_⟩
        simp only [hmk, ↓reduceIte]
        calc
          g i * (g ⟨k, hk8⟩ * clMonomialGenFrom g (k + 1) m)
              = (g i * g ⟨k, hk8⟩) * clMonomialGenFrom g (k + 1) m := by rw [mul_assoc]
          _ = ((-1 : ℝ) • (g ⟨k, hk8⟩ * g i)) * clMonomialGenFrom g (k + 1) m := by rw [hcomm]
          _ = (-1 : ℝ) • (g ⟨k, hk8⟩ * (g i * clMonomialGenFrom g (k + 1) m)) := by
                rw [smul_mul_assoc, mul_assoc]
          _ = (-1 : ℝ) • (g ⟨k, hk8⟩ * (s • clMonomialGenFrom g (k + 1)
                (Function.update m i (!m i)))) := by rw [hrec]
          _ = (-s) • (g ⟨k, hk8⟩ * clMonomialGenFrom g (k + 1)
                (Function.update m i (!m i))) := by
                rw [Algebra.mul_smul_comm, smul_smul, neg_one_mul]
      · have hmk' : m ⟨k, hk8⟩ = false := Bool.eq_false_iff.mpr hmk
        refine ⟨s, hs, ?_⟩
        simp only [hmk', Bool.false_eq_true, ↓reduceIte, one_mul]
        exact hrec

private lemma clMonomialGenFrom_mul_monomial {A : Type*} [Ring A] [Algebra ℝ A]
    (g : Fin 8 → A)
    (hsq : ∀ a : Fin 8, g a * g a = if a.val < 4 then 1 else -1)
    (hanti : ∀ {a b : Fin 8}, a ≠ b → g a * g b + g b * g a = 0)
    (k : ℕ) (m m' : Fin 8 → Bool) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      clMonomialGenFrom g k m * clMonomialGenFrom g 0 m' =
        s • clMonomialGenFrom g 0 (fun j => xor (if k ≤ j.val then m j else false) (m' j)) := by
  induction hd : 8 - k generalizing k m' with
  | zero =>
      have hk : 8 ≤ k := by omega
      rw [clMonomialGenFrom_ge g k hk, one_mul]
      refine ⟨1, Or.inl rfl, ?_⟩
      rw [one_smul]
      congr 1
      funext j
      have hj : ¬ k ≤ j.val := by omega
      simp [hj]
  | succ d ih =>
      have hk : k < 8 := by omega
      rcases ih (k + 1) m' (by omega) with ⟨s₁, hs₁, hrec⟩
      rw [clMonomialGenFrom_step g k hk m, mul_assoc, hrec]
      by_cases hmk : m ⟨k, hk⟩
      · simp only [hmk, ↓reduceIte]
        rcases clMonomialGenFrom_mul_gen g hsq hanti ⟨k, hk⟩ 0 (Nat.zero_le _)
            (fun j => xor (if k + 1 ≤ j.val then m j else false) (m' j)) with
          ⟨s₂, hs₂, hmul⟩
        refine ⟨s₁ * s₂, ?_, ?_⟩
        · rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> simp
        · rw [Algebra.mul_smul_comm, hmul, smul_smul]
          congr 2
          funext j
          by_cases hjk : j = ⟨k, hk⟩
          · subst hjk
            simp [hmk]
          · have hne : j.val ≠ k := fun h => hjk (Fin.ext h)
            have hle : (k ≤ j.val) ↔ (k + 1 ≤ j.val) := by omega
            simp [Function.update_of_ne hjk, hle]
      · have hmk' : m ⟨k, hk⟩ = false := Bool.eq_false_iff.mpr hmk
        refine ⟨s₁, hs₁, ?_⟩
        simp only [hmk', Bool.false_eq_true, ↓reduceIte, one_mul]
        congr 2
        funext j
        by_cases hjk : j = ⟨k, hk⟩
        · subst hjk
          simp [hmk']
        · have hne : j.val ≠ k := fun h => hjk (Fin.ext h)
          have hle : (k ≤ j.val) ↔ (k + 1 ≤ j.val) := by omega
          simp [hle]

private lemma cl44Gen_mul_clMonomial (i : Fin 8) (m : Fin 8 → Bool) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      cl44Gen i * clMonomial m = s • clMonomial (Function.update m i (!m i)) :=
  clMonomialGenFrom_mul_gen cl44Gen cl44Gen_sq (fun h => cl44Gen_anticomm h) i 0
    (Nat.zero_le _) m

private lemma clMonomial_mul (m m' : Fin 8 → Bool) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      clMonomial m * clMonomial m' = s • clMonomial (fun j => xor (m j) (m' j)) := by
  simpa [clMonomial] using
    clMonomialGenFrom_mul_monomial cl44Gen cl44Gen_sq (fun h => cl44Gen_anticomm h) 0 m m'

private lemma odd_parity_ite (n : ℕ) :
    -(if n % 2 = 0 then (1 : ℝ) else -1) = if (n + 1) % 2 = 0 then 1 else -1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, Nat.add_mod]

private lemma clMonomial_mul_gamma44_tail (k : ℕ) (m : Fin 8 → Bool) :
    let c := (Finset.univ.filter (fun j : Fin 8 => k ≤ j.val ∧ m j = true)).card
    clMonomialGenFrom cl44Gen k m * gamma44 =
      (if c % 2 = 0 then (1 : ℝ) else -1) • (gamma44 * clMonomialGenFrom cl44Gen k m) := by
  induction hd : 8 - k generalizing k with
  | zero =>
      have hk : 8 ≤ k := by omega
      have hcard : (Finset.univ.filter (fun j : Fin 8 => k ≤ j.val ∧ m j = true)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _
        omega
      simp [clMonomialGenFrom_ge cl44Gen k hk, hcard]
  | succ d ih =>
      have hk : k < 8 := by omega
      have hrec := ih (k + 1) (by omega)
      dsimp only at hrec ⊢
      rw [clMonomialGenFrom_step cl44Gen k hk m]
      by_cases hmk : m ⟨k, hk⟩
      · have hS₀ :
            Finset.univ.filter (fun j : Fin 8 => k ≤ j.val ∧ m j = true) =
              insert ⟨k, hk⟩
                (Finset.univ.filter (fun j : Fin 8 => k + 1 ≤ j.val ∧ m j = true)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_insert, true_and]
          constructor
          · rintro ⟨hkj, hmj⟩
            by_cases hje : j = ⟨k, hk⟩
            · exact Or.inl hje
            · exact Or.inr ⟨by have : j.val ≠ k := fun h => hje (Fin.ext h); omega, hmj⟩
          · rintro (rfl | ⟨hkj, hmj⟩)
            · exact ⟨le_refl _, hmk⟩
            · exact ⟨by omega, hmj⟩
        have hnot : (⟨k, hk⟩ : Fin 8) ∉
            Finset.univ.filter (fun j : Fin 8 => k + 1 ≤ j.val ∧ m j = true) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
          intro h
          omega
        have hcard :
            (Finset.univ.filter (fun j : Fin 8 => k ≤ j.val ∧ m j = true)).card =
              (Finset.univ.filter (fun j : Fin 8 => k + 1 ≤ j.val ∧ m j = true)).card + 1 := by
          rw [hS₀, Finset.card_insert_of_notMem hnot]
        have hanti : cl44Gen ⟨k, hk⟩ * gamma44 = -(gamma44 * cl44Gen ⟨k, hk⟩) :=
          eq_neg_of_add_eq_zero_left (gamma44_properties.2.2.2 ⟨k, hk⟩)
        simp only [hmk, ↓reduceIte]
        rw [Matrix.mul_assoc, hrec, Algebra.mul_smul_comm, ← Matrix.mul_assoc, hanti,
          Matrix.neg_mul, Matrix.mul_assoc, smul_neg, ← neg_smul]
        congr 1
        rw [hcard, odd_parity_ite]
      · have hmk' : m ⟨k, hk⟩ = false := Bool.eq_false_iff.mpr hmk
        have hS₀ :
            Finset.univ.filter (fun j : Fin 8 => k ≤ j.val ∧ m j = true) =
              Finset.univ.filter (fun j : Fin 8 => k + 1 ≤ j.val ∧ m j = true) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hkj, hmj⟩
            have hne : j ≠ ⟨k, hk⟩ := by
              intro h
              subst h
              simp [hmk'] at hmj
            have hnv : j.val ≠ k := fun h => hne (Fin.ext h)
            exact ⟨by omega, hmj⟩
          · rintro ⟨hkj, hmj⟩
            exact ⟨by omega, hmj⟩
        simp only [hmk', Bool.false_eq_true, ↓reduceIte, one_mul]
        rw [hS₀]
        exact hrec

private lemma clMonomial_tail_comm_gen (i : Fin 8) (k : ℕ) (hk : i.val < k) (m : Fin 8 → Bool) :
    let c := (Finset.univ.filter (fun j : Fin 8 => k ≤ j.val ∧ m j = true)).card
    clMonomialGenFrom cl44Gen k m * cl44Gen i =
      (if c % 2 = 0 then (1 : ℝ) else -1) • (cl44Gen i * clMonomialGenFrom cl44Gen k m) := by
  induction hd : 8 - k generalizing k with
  | zero =>
      have hk8 : 8 ≤ k := by omega
      have hcard : (Finset.univ.filter (fun j : Fin 8 => k ≤ j.val ∧ m j = true)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _
        omega
      simp [clMonomialGenFrom_ge cl44Gen k hk8, hcard]
  | succ d ih =>
      have hk8 : k < 8 := by omega
      have hrec := ih (k + 1) (by omega) (by omega)
      dsimp only at hrec ⊢
      rw [clMonomialGenFrom_step cl44Gen k hk8 m]
      by_cases hmk : m ⟨k, hk8⟩
      · have hS₀ :
            Finset.univ.filter (fun j : Fin 8 => k ≤ j.val ∧ m j = true) =
              insert ⟨k, hk8⟩
                (Finset.univ.filter (fun j : Fin 8 => k + 1 ≤ j.val ∧ m j = true)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_insert, true_and]
          constructor
          · rintro ⟨hkj, hmj⟩
            by_cases hje : j = ⟨k, hk8⟩
            · exact Or.inl hje
            · exact Or.inr ⟨by have : j.val ≠ k := fun h => hje (Fin.ext h); omega, hmj⟩
          · rintro (rfl | ⟨hkj, hmj⟩)
            · exact ⟨le_refl _, hmk⟩
            · exact ⟨by omega, hmj⟩
        have hnot : (⟨k, hk8⟩ : Fin 8) ∉
            Finset.univ.filter (fun j : Fin 8 => k + 1 ≤ j.val ∧ m j = true) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
          intro h
          omega
        have hcard :
            (Finset.univ.filter (fun j : Fin 8 => k ≤ j.val ∧ m j = true)).card =
              (Finset.univ.filter (fun j : Fin 8 => k + 1 ≤ j.val ∧ m j = true)).card + 1 := by
          rw [hS₀, Finset.card_insert_of_notMem hnot]
        have hne : (⟨k, hk8⟩ : Fin 8) ≠ i := Fin.ne_of_val_ne (ne_of_gt hk)
        have hanti : cl44Gen ⟨k, hk8⟩ * cl44Gen i = -(cl44Gen i * cl44Gen ⟨k, hk8⟩) :=
          eq_neg_of_add_eq_zero_left (cl44Gen_anticomm hne)
        simp only [hmk, ↓reduceIte]
        rw [Matrix.mul_assoc, hrec, Algebra.mul_smul_comm, ← Matrix.mul_assoc, hanti,
          Matrix.neg_mul, Matrix.mul_assoc, smul_neg, ← neg_smul]
        congr 1
        rw [hcard, odd_parity_ite]
      · have hmk' : m ⟨k, hk8⟩ = false := Bool.eq_false_iff.mpr hmk
        have hS₀ :
            Finset.univ.filter (fun j : Fin 8 => k ≤ j.val ∧ m j = true) =
              Finset.univ.filter (fun j : Fin 8 => k + 1 ≤ j.val ∧ m j = true) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hkj, hmj⟩
            have hne : j ≠ ⟨k, hk8⟩ := by
              intro h
              subst h
              simp [hmk'] at hmj
            have hnv : j.val ≠ k := fun h => hne (Fin.ext h)
            exact ⟨by omega, hmj⟩
          · rintro ⟨hkj, hmj⟩
            exact ⟨by omega, hmj⟩
        simp only [hmk', Bool.false_eq_true, ↓reduceIte, one_mul]
        rw [hS₀]
        exact hrec

private lemma clMonomial_head_factor (k : ℕ) (hk : k < 8) (m : Fin 8 → Bool)
    (hbefore : ∀ j : Fin 8, j.val < k → m j = false) :
    clMonomialGenFrom cl44Gen 0 m = clMonomialGenFrom cl44Gen k m := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk0 : k < 8 := Nat.lt_of_succ_lt hk
      have hprev := ih hk0 (fun j hj => hbefore j (by omega))
      rw [hprev, clMonomialGenFrom_step cl44Gen k hk0 m]
      have hmk : m ⟨k, hk0⟩ = false := hbefore ⟨k, hk0⟩ (by simp)
      simp [hmk]

private lemma trace_clMonomial (m : Fin 8 → Bool) :
    Matrix.trace (clMonomial m) = if m = (fun _ => false) then 16 else 0 := by
  by_cases hm : m = fun _ => false
  · subst hm
    have h1 : clMonomial (fun _ => false) = 1 := by
      unfold clMonomial
      suffices h : ∀ k : ℕ, clMonomialGenFrom cl44Gen k (fun _ => false) = 1 from h 0
      intro k
      induction hd : 8 - k generalizing k with
      | zero => exact clMonomialGenFrom_ge cl44Gen k (by omega) _
      | succ d ih =>
          have hk : k < 8 := by omega
          rw [clMonomialGenFrom_step cl44Gen k hk, ih (k + 1) (by omega)]
          simp
    simp only [↓reduceIte]
    rw [h1, Matrix.trace_one, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_prod, Fintype.card_fin]
    norm_num
  · simp only [hm, ↓reduceIte]
    let S := Finset.univ.filter (fun j : Fin 8 => m j = true)
    have hSne : S.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hm
      funext j
      by_contra htrue
      have hj : j ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Bool.eq_true_of_not_eq_false htrue
      rw [hempty] at hj
      exact Finset.notMem_empty j hj
    by_cases hpar : S.card % 2 = 0
    · let i₀ : Fin 8 := S.min' hSne
      have hi₀_mem : i₀ ∈ S := Finset.min'_mem S hSne
      have hi₀_true : m i₀ = true := (Finset.mem_filter.mp hi₀_mem).2
      have hi₀_min : ∀ j : Fin 8, j.val < i₀.val → m j = false := by
        intro j hj
        by_contra hnt
        have hjt : j ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Bool.eq_true_of_not_eq_false hnt
        have hle : i₀ ≤ j := Finset.min'_le S j hjt
        exact Nat.not_lt.mpr hle hj
      have hsplit : clMonomial m = cl44Gen i₀ * clMonomialGenFrom cl44Gen (i₀.val + 1) m := by
        unfold clMonomial
        rw [clMonomial_head_factor i₀.val i₀.isLt m hi₀_min,
          clMonomialGenFrom_step cl44Gen i₀.val i₀.isLt m]
        have : (⟨i₀.val, i₀.isLt⟩ : Fin 8) = i₀ := Fin.ext rfl
        rw [this, hi₀_true]
        simp
      let S₁ := Finset.univ.filter (fun j : Fin 8 => i₀.val + 1 ≤ j.val ∧ m j = true)
      have hS_split : S = insert i₀ S₁ := by
        ext j
        simp only [S, S₁, Finset.mem_filter, Finset.mem_univ, Finset.mem_insert, true_and]
        constructor
        · intro hmj
          by_cases hje : j = i₀
          · exact Or.inl hje
          · have hle : i₀ ≤ j := Finset.min'_le S j (by simp [S, hmj])
            have hlt : i₀.val < j.val := lt_of_le_of_ne hle (fun h => hje (Fin.ext h.symm))
            exact Or.inr ⟨hlt, hmj⟩
        · rintro (rfl | ⟨_, hmj⟩)
          · exact hi₀_true
          · exact hmj
      have hi₀_not : i₀ ∉ S₁ := by
        simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h
        omega
      have hcard1 : S₁.card % 2 ≠ 0 := by
        have hc : S.card = S₁.card + 1 := by rw [hS_split, Finset.card_insert_of_notMem hi₀_not]
        omega
      have hcomm := clMonomial_tail_comm_gen i₀ (i₀.val + 1) (Nat.lt_succ_self _) m
      dsimp only at hcomm
      have hS₁_eq :
          (Finset.univ.filter (fun j : Fin 8 => i₀.val + 1 ≤ j.val ∧ m j = true)).card =
            S₁.card := rfl
      rw [hS₁_eq] at hcomm
      simp only [hcard1, ↓reduceIte, neg_one_smul] at hcomm
      have htr_comm : Matrix.trace (clMonomial m) = -Matrix.trace (clMonomial m) := by
        conv_lhs => rw [hsplit, Matrix.trace_mul_comm, hcomm, ← hsplit, Matrix.trace_neg]
      linarith
    · have hcomm := clMonomial_mul_gamma44_tail 0 m
      dsimp only at hcomm
      have hS0 : (Finset.univ.filter (fun j : Fin 8 => 0 ≤ j.val ∧ m j = true)).card = S.card := by
        congr 1
        ext j
        simp [S]
      rw [hS0] at hcomm
      simp only [hpar, ↓reduceIte, neg_one_smul] at hcomm
      change clMonomial m * gamma44 = -(gamma44 * clMonomial m) at hcomm
      have hconj : gamma44 * (clMonomial m * gamma44) = -clMonomial m := by
        rw [hcomm, Matrix.mul_neg, ← Matrix.mul_assoc, gamma44_properties.2.1, Matrix.one_mul]
      have htr : Matrix.trace (clMonomial m) = -Matrix.trace (clMonomial m) := by
        calc
          Matrix.trace (clMonomial m)
              = Matrix.trace (clMonomial m * (gamma44 * gamma44)) := by
                  rw [gamma44_properties.2.1, Matrix.mul_one]
          _ = Matrix.trace (gamma44 * (clMonomial m * gamma44)) := by
                  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
          _ = Matrix.trace (-clMonomial m) := by rw [hconj]
          _ = -Matrix.trace (clMonomial m) := Matrix.trace_neg _
      linarith

/-- Linear independence of all `256` Clifford basis monomials `clMonomial m` in `M₁₆(ℝ)`. -/
lemma clMonomial_linearIndependent : LinearIndependent ℝ clMonomial := by
  rw [Fintype.linearIndependent_iff]
  intro c hc m
  have hmul := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ => clMonomial m * M) hc
  rw [Matrix.mul_zero, Matrix.mul_sum] at hmul
  have htr := congrArg Matrix.trace hmul
  rw [Matrix.trace_zero, Matrix.trace_sum] at htr
  have hterm : ∀ m' : Fin 8 → Bool,
      Matrix.trace (clMonomial m * (c m' • clMonomial m')) =
        if m' = m then c m * Matrix.trace (clMonomial m * clMonomial m) else 0 := by
    intro m'
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    by_cases h : m' = m
    · subst h
      simp
    · rcases clMonomial_mul m m' with ⟨s, _, hprod⟩
      rw [hprod, Matrix.trace_smul, smul_eq_mul, trace_clMonomial]
      have hne : (fun j => xor (m j) (m' j)) ≠ (fun _ => false) := by
        intro heq
        apply h
        funext j
        have hj := congrFun heq j
        cases hm : m j <;> cases hm' : m' j <;> simp_all
      simp [hne, h]
  simp_rw [hterm] at htr
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at htr
  rcases clMonomial_mul m m with ⟨s, hs, hsq⟩
  have hx0 : (fun j => xor (m j) (m j)) = (fun _ => false) := by
    funext j
    cases m j <;> rfl
  rw [hsq, hx0, Matrix.trace_smul, smul_eq_mul, trace_clMonomial] at htr
  simp only [↓reduceIte] at htr
  have hs0 : s * 16 ≠ 0 := by
    rcases hs with rfl | rfl <;> norm_num
  exact (mul_eq_zero.mp htr).resolve_right hs0

private lemma tensor4_single_mem_cl44MatrixSubalgebra :
    (∀ b : Matrix (Fin 2) (Fin 2) ℝ,
      b ∈ ({1, cl11Pos, cl11Neg, cl11Grad} : Set (Matrix (Fin 2) (Fin 2) ℝ)) →
      tensor4 b 1 1 1 ∈ cl44MatrixSubalgebra ∧
      tensor4 1 b 1 1 ∈ cl44MatrixSubalgebra ∧
      tensor4 1 1 b 1 ∈ cl44MatrixSubalgebra ∧
      tensor4 1 1 1 b ∈ cl44MatrixSubalgebra) := by
  have hg : ∀ i : Fin 8, cl44Gen i ∈ cl44MatrixSubalgebra :=
    fun i => Algebra.subset_adjoin (Set.mem_range_self i)
  have h10 : tensor4 (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 1 ∈ cl44MatrixSubalgebra := by
    rw [tensor4_one]
    exact Subalgebra.one_mem _
  have hp0 : tensor4 cl11Pos 1 1 1 ∈ cl44MatrixSubalgebra := hg 0
  have hn0 : tensor4 cl11Neg 1 1 1 ∈ cl44MatrixSubalgebra := hg 4
  have hg0 : tensor4 cl11Grad 1 1 1 ∈ cl44MatrixSubalgebra := by
    have h : tensor4 cl11Grad 1 1 1 = cl44Gen 0 * cl44Gen 4 := by
      unfold cl44Gen
      simp [tensor4_mul, cl11Pos_mul_cl11Neg]
    rw [h]
    exact Subalgebra.mul_mem _ (hg 0) (hg 4)
  have hp1 : tensor4 1 cl11Pos 1 1 ∈ cl44MatrixSubalgebra := by
    have h : tensor4 1 cl11Pos 1 1 = tensor4 cl11Grad 1 1 1 * cl44Gen 1 := by
      unfold cl44Gen
      simp [tensor4_mul, cl11Grad_sq]
    rw [h]
    exact Subalgebra.mul_mem _ hg0 (hg 1)
  have hn1 : tensor4 1 cl11Neg 1 1 ∈ cl44MatrixSubalgebra := by
    have h : tensor4 1 cl11Neg 1 1 = tensor4 cl11Grad 1 1 1 * cl44Gen 5 := by
      unfold cl44Gen
      simp [tensor4_mul, cl11Grad_sq]
    rw [h]
    exact Subalgebra.mul_mem _ hg0 (hg 5)
  have hg1 : tensor4 1 cl11Grad 1 1 ∈ cl44MatrixSubalgebra := by
    have h : tensor4 1 cl11Grad 1 1 = cl44Gen 1 * cl44Gen 5 := by
      unfold cl44Gen
      simp [tensor4_mul, cl11Grad_sq, cl11Pos_mul_cl11Neg]
    rw [h]
    exact Subalgebra.mul_mem _ (hg 1) (hg 5)
  have hg01 : tensor4 cl11Grad cl11Grad 1 1 ∈ cl44MatrixSubalgebra := by
    have h : tensor4 cl11Grad cl11Grad 1 1 = tensor4 cl11Grad 1 1 1 * tensor4 1 cl11Grad 1 1 := by
      simp [tensor4_mul]
    rw [h]
    exact Subalgebra.mul_mem _ hg0 hg1
  have hp2 : tensor4 1 1 cl11Pos 1 ∈ cl44MatrixSubalgebra := by
    have h : tensor4 1 1 cl11Pos 1 = tensor4 cl11Grad cl11Grad 1 1 * cl44Gen 2 := by
      unfold cl44Gen
      simp [tensor4_mul, cl11Grad_sq]
    rw [h]
    exact Subalgebra.mul_mem _ hg01 (hg 2)
  have hn2 : tensor4 1 1 cl11Neg 1 ∈ cl44MatrixSubalgebra := by
    have h : tensor4 1 1 cl11Neg 1 = tensor4 cl11Grad cl11Grad 1 1 * cl44Gen 6 := by
      unfold cl44Gen
      simp [tensor4_mul, cl11Grad_sq]
    rw [h]
    exact Subalgebra.mul_mem _ hg01 (hg 6)
  have hg2 : tensor4 1 1 cl11Grad 1 ∈ cl44MatrixSubalgebra := by
    have h : tensor4 1 1 cl11Grad 1 = cl44Gen 2 * cl44Gen 6 := by
      unfold cl44Gen
      simp [tensor4_mul, cl11Grad_sq, cl11Pos_mul_cl11Neg]
    rw [h]
    exact Subalgebra.mul_mem _ (hg 2) (hg 6)
  have hg012 : tensor4 cl11Grad cl11Grad cl11Grad 1 ∈ cl44MatrixSubalgebra := by
    have h : tensor4 cl11Grad cl11Grad cl11Grad 1 =
        tensor4 cl11Grad cl11Grad 1 1 * tensor4 1 1 cl11Grad 1 := by
      simp [tensor4_mul]
    rw [h]
    exact Subalgebra.mul_mem _ hg01 hg2
  have hp3 : tensor4 1 1 1 cl11Pos ∈ cl44MatrixSubalgebra := by
    have h : tensor4 1 1 1 cl11Pos = tensor4 cl11Grad cl11Grad cl11Grad 1 * cl44Gen 3 := by
      unfold cl44Gen
      simp [tensor4_mul, cl11Grad_sq]
    rw [h]
    exact Subalgebra.mul_mem _ hg012 (hg 3)
  have hn3 : tensor4 1 1 1 cl11Neg ∈ cl44MatrixSubalgebra := by
    have h : tensor4 1 1 1 cl11Neg = tensor4 cl11Grad cl11Grad cl11Grad 1 * cl44Gen 7 := by
      unfold cl44Gen
      simp [tensor4_mul, cl11Grad_sq]
    rw [h]
    exact Subalgebra.mul_mem _ hg012 (hg 7)
  have hg3 : tensor4 1 1 1 cl11Grad ∈ cl44MatrixSubalgebra := by
    have h : tensor4 1 1 1 cl11Grad = cl44Gen 3 * cl44Gen 7 := by
      unfold cl44Gen
      simp [tensor4_mul, cl11Grad_sq, cl11Pos_mul_cl11Neg]
    rw [h]
    exact Subalgebra.mul_mem _ (hg 3) (hg 7)
  intro b hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨h10, h10, h10, h10⟩
  · exact ⟨hp0, hp1, hp2, hp3⟩
  · exact ⟨hn0, hn1, hn2, hn3⟩
  · exact ⟨hg0, hg1, hg2, hg3⟩

private def mat2Unit (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  if i = 0 then (if j = 0 then cl11P0 else cl11Up)
  else (if j = 0 then cl11Down else cl11P1)

private lemma mat2Unit_apply (i j a b : Fin 2) :
    mat2Unit i j a b = if a = i ∧ b = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [mat2Unit, cl11P0, cl11P1, cl11Up, cl11Down]

private lemma mat2Unit_eq_comb (i j : Fin 2) :
    (mat2Unit i j = (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) + cl11Grad) ∨
     mat2Unit i j = (1 / 2 : ℝ) • (cl11Pos - cl11Neg) ∨
     mat2Unit i j = (1 / 2 : ℝ) • (cl11Pos + cl11Neg) ∨
     mat2Unit i j = (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) - cl11Grad)) := by
  fin_cases i <;> fin_cases j
  · left; ext a b; (fin_cases a <;> fin_cases b <;> simp [mat2Unit, cl11P0, cl11Grad]); norm_num
  · right; left; ext a b
    (fin_cases a <;> fin_cases b <;> simp [mat2Unit, cl11Up, cl11Pos, cl11Neg]); norm_num
  · right; right; left; ext a b
    (fin_cases a <;> fin_cases b <;> simp [mat2Unit, cl11Down, cl11Pos, cl11Neg]); norm_num
  · right; right; right; ext a b
    (fin_cases a <;> fin_cases b <;> simp [mat2Unit, cl11P1, cl11Grad]); norm_num

private lemma tensor4_mat2Unit_mem_cl44MatrixSubalgebra (i j : Krein16Idx) :
    tensor4 (mat2Unit i.1 j.1) (mat2Unit i.2.1 j.2.1)
      (mat2Unit i.2.2.1 j.2.2.1) (mat2Unit i.2.2.2 j.2.2.2) ∈ cl44MatrixSubalgebra := by
  have hslot0 : ∀ a b : Fin 2, tensor4 (mat2Unit a b) 1 1 1 ∈ cl44MatrixSubalgebra := by
    intro a b
    rcases mat2Unit_eq_comb a b with h | h | h | h <;> rw [h, ← tensor4_smul_all]
    · rw [tensor4_add_0]
      exact Subalgebra.smul_mem _ (Subalgebra.add_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).1) _
    · rw [tensor4_sub_0]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).1) _
    · rw [tensor4_add_0]
      exact Subalgebra.smul_mem _ (Subalgebra.add_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).1) _
    · rw [tensor4_sub_0]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).1) _
  have hslot1 : ∀ a b : Fin 2, tensor4 1 (mat2Unit a b) 1 1 ∈ cl44MatrixSubalgebra := by
    intro a b
    have hsm : ∀ r : ℝ, ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
        tensor4 1 (r • A) 1 1 = r • tensor4 1 A 1 1 := by
      intro r A; ext x y; simp only [tensor4, Matrix.smul_apply, smul_eq_mul]; ring
    rcases mat2Unit_eq_comb a b with h | h | h | h <;> rw [h, hsm]
    · rw [tensor4_add_1]
      exact Subalgebra.smul_mem _ (Subalgebra.add_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.1) _
    · rw [tensor4_sub_1]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.1) _
    · rw [tensor4_add_1]
      exact Subalgebra.smul_mem _ (Subalgebra.add_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.1) _
    · rw [tensor4_sub_1]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.1) _
  have hslot2 : ∀ a b : Fin 2, tensor4 1 1 (mat2Unit a b) 1 ∈ cl44MatrixSubalgebra := by
    intro a b
    have hsm : ∀ r : ℝ, ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
        tensor4 1 1 (r • A) 1 = r • tensor4 1 1 A 1 := by
      intro r A; ext x y; simp only [tensor4, Matrix.smul_apply, smul_eq_mul]; ring
    rcases mat2Unit_eq_comb a b with h | h | h | h <;> rw [h, hsm]
    · rw [tensor4_add_2]
      exact Subalgebra.smul_mem _ (Subalgebra.add_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.1) _
    · rw [tensor4_sub_2]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.1) _
    · rw [tensor4_add_2]
      exact Subalgebra.smul_mem _ (Subalgebra.add_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.1) _
    · rw [tensor4_sub_2]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.1
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.1) _
  have hslot3 : ∀ a b : Fin 2, tensor4 1 1 1 (mat2Unit a b) ∈ cl44MatrixSubalgebra := by
    intro a b
    have hsm : ∀ r : ℝ, ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
        tensor4 1 1 1 (r • A) = r • tensor4 1 1 1 A := by
      intro r A; ext x y; simp only [tensor4, Matrix.smul_apply, smul_eq_mul]; ring
    rcases mat2Unit_eq_comb a b with h | h | h | h <;> rw [h, hsm]
    · rw [tensor4_add_3]
      exact Subalgebra.smul_mem _ (Subalgebra.add_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.2
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.2) _
    · rw [tensor4_sub_3]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.2
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.2) _
    · rw [tensor4_add_3]
      exact Subalgebra.smul_mem _ (Subalgebra.add_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.2
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.2) _
    · rw [tensor4_sub_3]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.2
        (tensor4_single_mem_cl44MatrixSubalgebra _ (by simp)).2.2.2) _
  have hprod :
      tensor4 (mat2Unit i.1 j.1) (mat2Unit i.2.1 j.2.1)
          (mat2Unit i.2.2.1 j.2.2.1) (mat2Unit i.2.2.2 j.2.2.2) =
        tensor4 (mat2Unit i.1 j.1) 1 1 1 * tensor4 1 (mat2Unit i.2.1 j.2.1) 1 1 *
          tensor4 1 1 (mat2Unit i.2.2.1 j.2.2.1) 1 *
          tensor4 1 1 1 (mat2Unit i.2.2.2 j.2.2.2) := by
    rw [tensor4_mul, tensor4_mul, tensor4_mul]
    simp
  rw [hprod]
  exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (hslot0 i.1 j.1) (hslot1 i.2.1 j.2.1)) (hslot2 i.2.2.1 j.2.2.1)) (hslot3 i.2.2.2 j.2.2.2)

private lemma ite_one_zero_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1 : ℝ) else 0) * (if Q then 1 else 0) =
      if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

private lemma tensor4_mat2Unit_apply (i j a b : Krein16Idx) :
    tensor4 (mat2Unit i.1 j.1) (mat2Unit i.2.1 j.2.1)
      (mat2Unit i.2.2.1 j.2.2.1) (mat2Unit i.2.2.2 j.2.2.2) a b =
      if i = a ∧ j = b then 1 else 0 := by
  rcases i with ⟨i0, i1, i2, i3⟩
  rcases j with ⟨j0, j1, j2, j3⟩
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp only [tensor4, mat2Unit_apply]
  rw [ite_one_zero_mul, ite_one_zero_mul, ite_one_zero_mul]
  congr 1
  ext
  simp only [Prod.ext_iff]
  tauto

/-- The 8 Clifford generators generate the full `16 × 16` real matrix algebra:
`cl44MatrixSubalgebra = ⊤`. -/
lemma cl44MatrixSubalgebra_eq_top : cl44MatrixSubalgebra = ⊤ := by
  rw [eq_top_iff]
  intro M _
  have hdecomp : M = ∑ i : Krein16Idx, ∑ j : Krein16Idx, M i j •
      tensor4 (mat2Unit i.1 j.1) (mat2Unit i.2.1 j.2.1)
        (mat2Unit i.2.2.1 j.2.2.1) (mat2Unit i.2.2.2 j.2.2.2) := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, tensor4_mat2Unit_apply]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro j _ hjb
        simp [hjb]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    · intro i _ hia
      rw [Finset.sum_eq_zero]
      intro j _
      simp [hia]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  rw [hdecomp]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (tensor4_mat2Unit_mem_cl44MatrixSubalgebra i j) (M i j)

private def clGenAlg (i : Fin 8) : CliffordAlgebra InfoGeometry.Clifford.splitQ44 :=
  CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 (Pi.single i 1)

private lemma clGenAlg_sq (i : Fin 8) :
    clGenAlg i * clGenAlg i = if i.val < 4 then 1 else -1 := by
  unfold clGenAlg
  rw [CliffordAlgebra.ι_sq_scalar, InfoGeometry.Clifford.splitQ44_apply]
  fin_cases i <;> simp

private lemma clGenAlg_anticomm {i j : Fin 8} (hij : i ≠ j) :
    clGenAlg i * clGenAlg j + clGenAlg j * clGenAlg i = 0 := by
  unfold clGenAlg
  rw [CliffordAlgebra.ι_mul_ι_add_swap]
  have hpol : QuadraticMap.polar InfoGeometry.Clifford.splitQ44
      (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) = 0 := by
    unfold QuadraticMap.polar
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | (simp [InfoGeometry.Clifford.splitQ44_apply]; try norm_num)
  rw [hpol, map_zero]

/-- Explicit non-commutativity witness for `CliffordAlgebra InfoGeometry.Clifford.splitQ44`. -/
lemma cl44_clifford_noncommutative :
    clGenAlg 0 * clGenAlg 1 + clGenAlg 1 * clGenAlg 0 = 0 :=
  clGenAlg_anticomm (by decide)

private def cl44VecToMat : (Fin 8 → ℝ) →ₗ[ℝ] Matrix Krein16Idx Krein16Idx ℝ where
  toFun x := ∑ i : Fin 8, x i • cl44Gen i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

private lemma splitQ44_double_sum_scalar (x : Fin 8 → ℝ) :
    ∑ i : Fin 8, 2 * (if i.val < 4 then (1 : ℝ) else -1) * (x i * x i) =
      2 * (x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 -
        (x 4 * x 4 + x 5 * x 5 + x 6 * x 6 + x 7 * x 7)) := by
  simp only [Fin.sum_univ_eight, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  ring

private lemma cl44VecToMat_sq (x : Fin 8 → ℝ) :
    cl44VecToMat x * cl44VecToMat x =
      algebraMap ℝ (Matrix Krein16Idx Krein16Idx ℝ) (InfoGeometry.Clifford.splitQ44 x) := by
  have h2 : (2 : ℝ) • (cl44VecToMat x * cl44VecToMat x) =
      (2 : ℝ) • algebraMap ℝ (Matrix Krein16Idx Krein16Idx ℝ)
        (InfoGeometry.Clifford.splitQ44 x) := by
    have hsum : (2 : ℝ) • (cl44VecToMat x * cl44VecToMat x) =
        ∑ i : Fin 8, ∑ j : Fin 8,
          (x i * x j) • (cl44Gen i * cl44Gen j + cl44Gen j * cl44Gen i) := by
      have hcomm : (∑ i : Fin 8, ∑ j : Fin 8, (x i * x j) • (cl44Gen i * cl44Gen j)) =
          ∑ i : Fin 8, ∑ j : Fin 8, (x i * x j) • (cl44Gen j * cl44Gen i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm (x i) (x j)]
      have hLHS : cl44VecToMat x * cl44VecToMat x =
          ∑ i : Fin 8, ∑ j : Fin 8, (x i * x j) • (cl44Gen i * cl44Gen j) := by
        rw [cl44VecToMat]
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [Matrix.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hRHS : cl44VecToMat x * cl44VecToMat x =
          ∑ i : Fin 8, ∑ j : Fin 8, (x i * x j) • (cl44Gen j * cl44Gen i) :=
        hLHS.trans hcomm
      rw [two_smul]
      conv_lhs =>
        arg 1
        rw [hLHS]
      conv_lhs =>
        arg 2
        rw [hRHS]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_add]
    rw [hsum]
    have hdiag : ∀ i : Fin 8,
        (∑ j : Fin 8, (x i * x j) • (cl44Gen i * cl44Gen j + cl44Gen j * cl44Gen i)) =
          (2 * (if i.val < 4 then (1 : ℝ) else -1) * (x i * x i)) •
            (1 : Matrix Krein16Idx Krein16Idx ℝ) := by
      intro i
      rw [Finset.sum_eq_single i]
      · rw [← two_smul ℝ (cl44Gen i * cl44Gen i), cl44Gen_sq i, smul_smul]
        split_ifs <;> simp [mul_comm, mul_assoc]
      · intro j _ hji
        rw [cl44Gen_anticomm hji.symm, smul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    simp_rw [hdiag, ← Finset.sum_smul, InfoGeometry.Clifford.splitQ44_apply,
      Algebra.algebraMap_eq_smul_one, smul_smul, splitQ44_double_sum_scalar]
  have hsub : (2 : ℝ) • (cl44VecToMat x * cl44VecToMat x -
      algebraMap ℝ (Matrix Krein16Idx Krein16Idx ℝ) (InfoGeometry.Clifford.splitQ44 x)) = 0 := by
    rw [smul_sub, h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_left (by norm_num))

private def cl44Lift :
    CliffordAlgebra InfoGeometry.Clifford.splitQ44 →ₐ[ℝ] Matrix Krein16Idx Krein16Idx ℝ :=
  CliffordAlgebra.lift InfoGeometry.Clifford.splitQ44 ⟨cl44VecToMat, cl44VecToMat_sq⟩

private lemma cl44Lift_clGenAlg (i : Fin 8) : cl44Lift (clGenAlg i) = cl44Gen i := by
  unfold cl44Lift clGenAlg
  rw [CliffordAlgebra.lift_ι_apply]
  change (∑ j : Fin 8, (Pi.single i (1 : ℝ) : Fin 8 → ℝ) j • cl44Gen j) = cl44Gen i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private def clAlgMonomial (m : Fin 8 → Bool) : CliffordAlgebra InfoGeometry.Clifford.splitQ44 :=
  clMonomialGenFrom clGenAlg 0 m

private lemma clAlgMonomial_span_eq_top :
    Submodule.span ℝ (Set.range clAlgMonomial) = ⊤ := by
  let S : Submodule ℝ (CliffordAlgebra InfoGeometry.Clifford.splitQ44) :=
    Submodule.span ℝ (Set.range clAlgMonomial)
  have h1 : (1 : CliffordAlgebra InfoGeometry.Clifford.splitQ44) ∈ S := by
    have h0 : clAlgMonomial (fun _ => false) = 1 := by
      unfold clAlgMonomial
      suffices h : ∀ k : ℕ, clMonomialGenFrom clGenAlg k (fun _ => false) = 1 from h 0
      intro k
      induction hd : 8 - k generalizing k with
      | zero => exact clMonomialGenFrom_ge clGenAlg k (by omega) _
      | succ d ih =>
          have hk : k < 8 := by omega
          rw [clMonomialGenFrom_step clGenAlg k hk, ih (k + 1) (by omega)]
          simp
    rw [← h0]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hmul_gen : ∀ (i : Fin 8) (y : CliffordAlgebra InfoGeometry.Clifford.splitQ44),
      y ∈ S → clGenAlg i * y ∈ S := by
    intro i y hy
    refine Submodule.span_induction (hx := hy) ?_ ?_ ?_ ?_
    · rintro _ ⟨m, rfl⟩
      rcases clMonomialGenFrom_mul_gen clGenAlg clGenAlg_sq
          (fun h => clGenAlg_anticomm h) i 0 (Nat.zero_le _) m with ⟨s, _, hm⟩
      rw [show clAlgMonomial m = clMonomialGenFrom clGenAlg 0 m from rfl, hm]
      exact Submodule.smul_mem _ s (Submodule.subset_span ⟨_, rfl⟩)
    · rw [mul_zero]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
    · intro r a _ ha
      rw [Algebra.mul_smul_comm]
      exact Submodule.smul_mem _ r ha
  have hmul_ι : ∀ (x : Fin 8 → ℝ) (y : CliffordAlgebra InfoGeometry.Clifford.splitQ44),
      y ∈ S → CliffordAlgebra.ι InfoGeometry.Clifford.splitQ44 x * y ∈ S := by
    intro x y hy
    have hx : x = ∑ i : Fin 8, x i • Pi.single i (1 : ℝ) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij.symm]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hx, map_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, smul_mul_assoc]
    exact Submodule.smul_mem _ (x i) (hmul_gen i y hy)
  have hmul_left : ∀ a b : CliffordAlgebra InfoGeometry.Clifford.splitQ44,
      (∀ y ∈ S, a * y ∈ S) → (∀ y ∈ S, b * y ∈ S) → ∀ y ∈ S, (a * b) * y ∈ S := by
    intro a b ha hb y hy
    rw [mul_assoc]
    exact ha (b * y) (hb y hy)
  have hclosed : ∀ a : CliffordAlgebra InfoGeometry.Clifford.splitQ44, ∀ y ∈ S, a * y ∈ S := by
    intro a
    induction a using CliffordAlgebra.induction with
    | algebraMap r =>
        intro y hy
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
        exact Submodule.smul_mem _ r hy
    | ι x => exact hmul_ι x
    | mul a b ha hb => exact hmul_left a b ha hb
    | add a b ha hb =>
        intro y hy
        rw [add_mul]
        exact Submodule.add_mem _ (ha y hy) (hb y hy)
  rw [eq_top_iff]
  intro a _
  simpa using hclosed a 1 h1

/-- Real Bott-0 algebra isomorphism `Cl(4,4) ≃ₐ[ℝ] M₁₆(ℝ)`. -/
noncomputable def cl44AlgEquivMat16 :
    CliffordAlgebra InfoGeometry.Clifford.splitQ44 ≃ₐ[ℝ]
      Matrix Krein16Idx Krein16Idx ℝ := by
  have hsurj : Function.Surjective cl44Lift := by
    intro M
    have hrange : cl44Lift.range = ⊤ := by
      rw [← top_le_iff, ← cl44MatrixSubalgebra_eq_top]
      unfold cl44MatrixSubalgebra
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact ⟨clGenAlg i, cl44Lift_clGenAlg i⟩
    have hm : M ∈ cl44Lift.range := hrange ▸ Algebra.mem_top
    exact hm
  have hinj : Function.Injective cl44Lift := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx_mem : x ∈ Submodule.span ℝ (Set.range clAlgMonomial) := by
      rw [clAlgMonomial_span_eq_top]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx_mem
    have hmap : ∑ m : Fin 8 → Bool, c m • clMonomial m = 0 := by
      calc
        ∑ m : Fin 8 → Bool, c m • clMonomial m
            = ∑ m : Fin 8 → Bool, c m • cl44Lift (clAlgMonomial m) := by
                refine Finset.sum_congr rfl fun m _ => ?_
                congr 1
                unfold clAlgMonomial clMonomial
                rw [clMonomialGenFrom_map]
                simp [cl44Lift_clGenAlg]
        _ = cl44Lift (∑ m : Fin 8 → Bool, c m • clAlgMonomial m) := by
                rw [map_sum]
                refine Finset.sum_congr rfl fun m _ => ?_
                rw [map_smul]
        _ = cl44Lift x := by rw [hc]
        _ = 0 := hx
    have hc0 := Fintype.linearIndependent_iff.mp clMonomial_linearIndependent c hmap
    rw [← hc]
    simp [hc0]
  exact AlgEquiv.ofBijective cl44Lift ⟨hinj, hsurj⟩

private def krein16ToParity (i : Krein16Idx) : Fin 8 ⊕ Fin 8 :=
  let idx : Fin 8 := ⟨4 * i.2.1.val + 2 * i.2.2.1.val + i.2.2.2.val, by omega⟩
  if (i.1.val + i.2.1.val + i.2.2.1.val + i.2.2.2.val) % 2 = 0 then Sum.inl idx
  else Sum.inr idx

private def parityToKrein16 : Fin 8 ⊕ Fin 8 → Krein16Idx
  | Sum.inl k =>
      let b1 : Fin 2 := ⟨k.val / 4, by omega⟩
      let b2 : Fin 2 := ⟨(k.val / 2) % 2, by omega⟩
      let b3 : Fin 2 := ⟨k.val % 2, by omega⟩
      let b0 : Fin 2 := ⟨(b1.val + b2.val + b3.val) % 2, by omega⟩
      (b0, b1, b2, b3)
  | Sum.inr k =>
      let b1 : Fin 2 := ⟨k.val / 4, by omega⟩
      let b2 : Fin 2 := ⟨(k.val / 2) % 2, by omega⟩
      let b3 : Fin 2 := ⟨k.val % 2, by omega⟩
      let b0 : Fin 2 := ⟨(b1.val + b2.val + b3.val + 1) % 2, by omega⟩
      (b0, b1, b2, b3)

private def krein16ParityEquiv : Krein16Idx ≃ Fin 8 ⊕ Fin 8 where
  toFun := krein16ToParity
  invFun := parityToKrein16
  left_inv i := by
    rcases i with ⟨b0, b1, b2, b3⟩
    fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> rfl
  right_inv x := by
    rcases x with k | k <;> fin_cases k <;> rfl

private lemma reindex_gamma44_eq_fromBlocks :
    Matrix.reindexAlgEquiv ℝ ℝ krein16ParityEquiv gamma44 =
      Matrix.fromBlocks (1 : Matrix (Fin 8) (Fin 8) ℝ) 0 0 (-1) := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindexAlgEquiv, gamma44, tensor4, cl11Grad, krein16ParityEquiv,
      parityToKrein16]

/-- Even-splitting algebra equivalence between the `gamma44` commutant inside `M₁₆(ℝ)`
and the direct product `M₈(ℝ) × M₈(ℝ)`. -/
noncomputable def gamma44CommutantEquivProdMat8 :
    gamma44CommutantSubalgebra ≃ₐ[ℝ]
      Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ :=
  let e : Matrix Krein16Idx Krein16Idx ℝ ≃ₐ[ℝ] Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ :=
    Matrix.reindexAlgEquiv ℝ ℝ krein16ParityEquiv
  let hgam : e gamma44 = Matrix.fromBlocks (1 : Matrix (Fin 8) (Fin 8) ℝ) 0 0 (-1) :=
    reindex_gamma44_eq_fromBlocks
  have hoff : ∀ M : gamma44CommutantSubalgebra,
      (e M.1).toBlocks₁₂ = 0 ∧ (e M.1).toBlocks₂₁ = 0 := by
    intro M
    have hcomm : M.1 * gamma44 = gamma44 * M.1 := by
      have hm : ∀ g ∈ ({gamma44} : Set (Matrix Krein16Idx Krein16Idx ℝ)), g * M.1 = M.1 * g := M.2
      exact (hm gamma44 (Set.mem_singleton gamma44)).symm
    have hblk := congrArg e hcomm
    rw [map_mul, map_mul, hgam] at hblk
    conv_lhs at hblk => rw [← Matrix.fromBlocks_toBlocks (e M.1)]
    conv_rhs at hblk => rw [← Matrix.fromBlocks_toBlocks (e M.1)]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, Matrix.one_mul,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul] at hblk
    have h12 : -(e M.1).toBlocks₁₂ = (e M.1).toBlocks₁₂ :=
      congrArg Matrix.toBlocks₁₂ hblk
    have h21 : (e M.1).toBlocks₂₁ = -(e M.1).toBlocks₂₁ :=
      congrArg Matrix.toBlocks₂₁ hblk
    have h12' : (e M.1).toBlocks₁₂ = 0 := by
      ext i j
      have hij := congrArg (fun X : Matrix (Fin 8) (Fin 8) ℝ => X i j) h12
      simp only [Matrix.neg_apply, Matrix.zero_apply] at hij ⊢
      linarith
    have h21' : (e M.1).toBlocks₂₁ = 0 := by
      ext i j
      have hij := congrArg (fun X : Matrix (Fin 8) (Fin 8) ℝ => X i j) h21
      simp only [Matrix.neg_apply, Matrix.zero_apply] at hij ⊢
      linarith
    exact ⟨h12', h21'⟩
  { toFun := fun M => ((e M.1).toBlocks₁₁, (e M.1).toBlocks₂₂)
    invFun := fun p =>
      ⟨e.symm (Matrix.fromBlocks p.1 0 0 p.2), by
        change ∀ g ∈ ({gamma44} : Set (Matrix Krein16Idx Krein16Idx ℝ)),
          g * e.symm (Matrix.fromBlocks p.1 0 0 p.2) =
            e.symm (Matrix.fromBlocks p.1 0 0 p.2) * g
        intro g hg
        rw [Set.mem_singleton_iff.mp hg]
        apply e.injective
        rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, hgam]
        simp [Matrix.fromBlocks_multiply]⟩
    left_inv := fun M => by
      apply Subtype.ext
      apply e.injective
      rw [AlgEquiv.apply_symm_apply]
      rcases hoff M with ⟨h12, h21⟩
      have hfb : Matrix.fromBlocks (e M.1).toBlocks₁₁ 0 0 (e M.1).toBlocks₂₂ = e M.1 := by
        conv_rhs => rw [← Matrix.fromBlocks_toBlocks (e M.1), h12, h21]
      exact hfb
    right_inv := fun p => by
      ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]
    map_mul' := fun A B => by
      rcases hoff A with ⟨hA12, hA21⟩
      rcases hoff B with ⟨hB12, hB21⟩
      have hmul : e (A.1 * B.1) = Matrix.fromBlocks
          ((e A.1).toBlocks₁₁ * (e B.1).toBlocks₁₁) 0 0
          ((e A.1).toBlocks₂₂ * (e B.1).toBlocks₂₂) := by
        rw [map_mul]
        conv_lhs =>
          arg 1; rw [← Matrix.fromBlocks_toBlocks (e A.1), hA12, hA21]
        conv_lhs =>
          arg 2; rw [← Matrix.fromBlocks_toBlocks (e B.1), hB12, hB21]
        simp [Matrix.fromBlocks_multiply]
      ext i j <;> simp [hmul]
    map_add' := fun A B => by
      ext i j <;> simp [map_add, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]
    commutes' := fun r => by
      have h1 : e (algebraMap ℝ (Matrix Krein16Idx Krein16Idx ℝ) r) =
          Matrix.fromBlocks (algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ) r) 0 0
            (algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ) r) := by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, ← Matrix.fromBlocks_one,
          Matrix.fromBlocks_smul, smul_zero, ← Algebra.algebraMap_eq_smul_one]
      have h11 : (e (algebraMap ℝ (Matrix Krein16Idx Krein16Idx ℝ) r)).toBlocks₁₁ =
          algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ) r := by
        rw [h1]; rfl
      have h22 : (e (algebraMap ℝ (Matrix Krein16Idx Krein16Idx ℝ) r)).toBlocks₂₂ =
          algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ) r := by
        rw [h1]; rfl
      exact Prod.ext h11 h22 }

/-- Dimension of the chiral even `gamma44` commutant subalgebra is `128 = 8² + 8²`. -/
lemma gamma44_commutant_finrank :
    Module.finrank ℝ gamma44CommutantSubalgebra = 128 := by
  rw [gamma44CommutantEquivProdMat8.toLinearEquiv.finrank_eq, Module.finrank_prod,
    Module.finrank_matrix, Fintype.card_fin]
  simp only [Module.finrank_self]

/-! ### 2. Uncalibrated Derivation Dimension Ladder in `M₁₆(ℝ)` (`M1b-T14-C2`) -/

/-- Traceless Lie subalgebra `sl₁₆(ℝ) ⊂ M₁₆(ℝ)` of dimension `255`. -/
def sl16Subalgebra : LieSubalgebra ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  { toSubmodule := LinearMap.ker (Matrix.traceLinearMap Krein16Idx ℝ ℝ)
    lie_mem' := by
      intro A B _ _
      show Matrix.trace (A * B - B * A) = 0
      rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self] }

/-- Krein-skew Lie subalgebra `so(8,8) ⊂ M₁₆(ℝ)` preserving `kreinMetric88` of dimension `120`. -/
def so88KreinSubalgebra : LieSubalgebra ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  { toSubmodule :=
      { carrier := {M | Mᵀ * kreinMetric88 + kreinMetric88 * M = 0}
        add_mem' := by
          intro A B hA hB
          change (A + B)ᵀ * kreinMetric88 + kreinMetric88 * (A + B) = 0
          rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add,
            add_add_add_comm, hA, hB, add_zero]
        zero_mem' := by simp
        smul_mem' := by
          intro c A hA
          change (c • A)ᵀ * kreinMetric88 + kreinMetric88 * (c • A) = 0
          rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
            ← smul_add, hA, smul_zero] }
    lie_mem' := by
      intro A B hA hB
      change (A * B - B * A)ᵀ * kreinMetric88 + kreinMetric88 * (A * B - B * A) = 0
      have hA' : Aᵀ * kreinMetric88 = -(kreinMetric88 * A) := eq_neg_of_add_eq_zero_left hA
      have hB' : Bᵀ * kreinMetric88 = -(kreinMetric88 * B) := eq_neg_of_add_eq_zero_left hB
      have h1 : Bᵀ * (Aᵀ * kreinMetric88) = kreinMetric88 * (B * A) := by
        rw [hA', Matrix.mul_neg, ← Matrix.mul_assoc, hB', neg_mul, neg_neg, Matrix.mul_assoc]
      have h2 : Aᵀ * (Bᵀ * kreinMetric88) = kreinMetric88 * (A * B) := by
        rw [hB', Matrix.mul_neg, ← Matrix.mul_assoc, hA', neg_mul, neg_neg, Matrix.mul_assoc]
      rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
          Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc, h1, h2]
      abel }

/-- `Module.finrank ℝ sl16Subalgebra = 255`. -/
lemma finrank_sl16Subalgebra : Module.finrank ℝ sl16Subalgebra = 255 := by
  let tr : Matrix Krein16Idx Krein16Idx ℝ →ₗ[ℝ] ℝ := Matrix.traceLinearMap Krein16Idx ℝ ℝ
  have hsurj : Function.Surjective tr := by
    intro r
    refine ⟨(r / 16 : ℝ) • (1 : Matrix Krein16Idx Krein16Idx ℝ), ?_⟩
    simp only [tr, Matrix.traceLinearMap_apply, Matrix.trace_smul, Matrix.trace_one,
      card_krein16Idx, smul_eq_mul]
    norm_num
  have hrk := tr.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, finrank_mat16] at hrk
  change 1 + Module.finrank ℝ sl16Subalgebra = 256 at hrk
  omega

private def krein16ToFin16 (i : Krein16Idx) : Fin 16 :=
  ⟨8 * i.1.val + 4 * i.2.1.val + 2 * i.2.2.1.val + i.2.2.2.val, by omega⟩

private def fin16ToKrein16 (k : Fin 16) : Krein16Idx :=
  (⟨k.val / 8, by omega⟩, ⟨(k.val / 4) % 2, by omega⟩,
   ⟨(k.val / 2) % 2, by omega⟩, ⟨k.val % 2, by omega⟩)

private def krein16Fin16Equiv : Krein16Idx ≃ Fin 16 where
  toFun := krein16ToFin16
  invFun := fin16ToKrein16
  left_inv i := by
    rcases i with ⟨b0, b1, b2, b3⟩
    fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> rfl
  right_inv k := by
    fin_cases k <;> rfl

private def skew16 (f : {p : Fin 16 × Fin 16 // p.1 < p.2} → ℝ) :
    Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun i j =>
    if h : i < j then f ⟨(i, j), h⟩
    else if h' : j < i then -f ⟨(j, i), h'⟩ else 0

private lemma skew16_transpose_add (f : {p : Fin 16 × Fin 16 // p.1 < p.2} → ℝ) :
    (skew16 f)ᵀ + skew16 f = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply, skew16,
    Matrix.of_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hji : ¬ j < i := Nat.not_lt.mpr (le_of_lt hij)
    simp [hij, hji]
  · simp
  · have hji : ¬ i < j := Nat.not_lt.mpr (le_of_lt hij)
    simp [hij, hji]

/-- `Module.finrank ℝ so88KreinSubalgebra = 120`. -/
lemma finrank_so88KreinSubalgebra : Module.finrank ℝ so88KreinSubalgebra = 120 := by
  let Pair16 := {p : Fin 16 × Fin 16 // p.1 < p.2}
  let reidx : Matrix Krein16Idx Krein16Idx ℝ ≃ₗ[ℝ] Matrix (Fin 16) (Fin 16) ℝ :=
    Matrix.reindexLinearEquiv ℝ ℝ krein16Fin16Equiv krein16Fin16Equiv
  let ePair : Pair16 ≃ Σ i : Fin 16, Fin (15 - i.val) :=
    { toFun := fun p =>
        ⟨p.1.1, ⟨p.1.2.val - p.1.1.val - 1, by
          have h1 : p.1.1.val < p.1.2.val := p.2
          have h2 : p.1.2.val < 16 := p.1.2.isLt
          omega⟩⟩
      invFun := fun q =>
        ⟨(q.1, ⟨q.1.val + q.2.val + 1, by
          have hq : q.2.val < 15 - q.1.val := q.2.isLt
          omega⟩), by simp [Fin.lt_def]⟩
      left_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Fin.ext
          have hp : p.1.1.val < p.1.2.val := p.2
          dsimp
          omega
      right_inv := fun q => by
        rcases q with ⟨i, j⟩
        refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
        dsimp
        omega }
  have hcard : Fintype.card Pair16 = 120 := by
    rw [Fintype.card_congr ePair, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    decide
  have heta_sq : kreinMetric88 * kreinMetric88 = 1 := kreinMetric88_properties.2.2.1
  have heta_sym : kreinMetric88ᵀ = kreinMetric88 := kreinMetric88_properties.2.1
  let e : so88KreinSubalgebra.toSubmodule ≃ₗ[ℝ] (Pair16 → ℝ) :=
    { toFun := fun M p => (reidx (kreinMetric88 * M.1)) p.1.1 p.1.2
      invFun := fun f =>
        ⟨kreinMetric88 * reidx.symm (skew16 f), by
          have hNskew : (reidx.symm (skew16 f))ᵀ + reidx.symm (skew16 f) = 0 := by
            have hT : (reidx.symm (skew16 f))ᵀ = reidx.symm ((skew16 f)ᵀ) := rfl
            rw [hT, ← reidx.symm.map_add, skew16_transpose_add, reidx.symm.map_zero]
          change (kreinMetric88 * reidx.symm (skew16 f))ᵀ * kreinMetric88 +
              kreinMetric88 * (kreinMetric88 * reidx.symm (skew16 f)) = 0
          rw [Matrix.transpose_mul, heta_sym, Matrix.mul_assoc, heta_sq, Matrix.mul_one,
            ← Matrix.mul_assoc, heta_sq, Matrix.one_mul]
          exact hNskew⟩
      left_inv := fun M => by
        apply Subtype.ext
        have hNskew : (reidx (kreinMetric88 * M.1))ᵀ + reidx (kreinMetric88 * M.1) = 0 := by
          have hT : (reidx (kreinMetric88 * M.1))ᵀ =
              reidx ((kreinMetric88 * M.1)ᵀ) := rfl
          rw [hT, ← reidx.map_add]
          have hM : (kreinMetric88 * M.1)ᵀ + kreinMetric88 * M.1 = 0 := by
            have hm := M.2
            change M.1ᵀ * kreinMetric88 + kreinMetric88 * M.1 = 0 at hm
            rw [Matrix.transpose_mul, heta_sym]
            exact hm
          rw [hM, reidx.map_zero]
        have hmat : skew16 (fun p => (reidx (kreinMetric88 * M.1)) p.1.1 p.1.2) =
            reidx (kreinMetric88 * M.1) := by
          ext i j
          simp only [skew16, Matrix.of_apply]
          have hij_eq := congrArg (fun X : Matrix (Fin 16) (Fin 16) ℝ => X i j) hNskew
          simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at hij_eq
          rcases lt_trichotomy i j with hij | rfl | hij
          · simp [hij]
          · simp only [lt_self_iff_false, ↓reduceDIte]
            linarith
          · have hni : ¬ i < j := Nat.not_lt.mpr (le_of_lt hij)
            simp only [hni, ↓reduceDIte, hij]
            linarith
        change kreinMetric88 * reidx.symm
          (skew16 (fun p => (reidx (kreinMetric88 * M.1)) p.1.1 p.1.2)) = M.1
        rw [hmat, reidx.symm_apply_apply, ← Matrix.mul_assoc, heta_sq, Matrix.one_mul]
      right_inv := fun f => by
        funext p
        change reidx (kreinMetric88 * (kreinMetric88 * reidx.symm (skew16 f))) p.1.1 p.1.2 = f p
        rw [← Matrix.mul_assoc, heta_sq, Matrix.one_mul, reidx.apply_symm_apply]
        simp [skew16, p.2]
      map_add' := fun A B => by
        funext p
        simp [Matrix.mul_add, map_add]
      map_smul' := fun r A => by
        funext p
        simp [map_smul] }
  change Module.finrank ℝ so88KreinSubalgebra.toSubmodule = 120
  rw [e.finrank_eq, Module.finrank_pi, hcard]

private def bivBlockPair : Fin 7 → Fin 4 → Fin 8 × Fin 8
  | 0, 0 => (0, 1) | 0, 1 => (2, 3) | 0, 2 => (4, 5) | 0, 3 => (6, 7)
  | 1, 0 => (0, 2) | 1, 1 => (1, 3) | 1, 2 => (4, 6) | 1, 3 => (5, 7)
  | 2, 0 => (0, 3) | 2, 1 => (1, 2) | 2, 2 => (4, 7) | 2, 3 => (5, 6)
  | 3, 0 => (0, 4) | 3, 1 => (1, 5) | 3, 2 => (2, 6) | 3, 3 => (3, 7)
  | 4, 0 => (0, 5) | 4, 1 => (1, 4) | 4, 2 => (2, 7) | 4, 3 => (3, 6)
  | 5, 0 => (0, 6) | 5, 1 => (1, 7) | 5, 2 => (2, 4) | 5, 3 => (3, 5)
  | 6, 0 => (0, 7) | 6, 1 => (1, 6) | 6, 2 => (2, 5) | 6, 3 => (3, 4)

private lemma bivBlockPair_lt (i : Fin 7) (j : Fin 4) :
    (bivBlockPair i j).1 < (bivBlockPair i j).2 := by
  fin_cases i <;> fin_cases j <;> decide

private def bivBasis (p : Fin 7 × Fin 4) : Matrix Krein16Idx Krein16Idx ℝ :=
  cl44Bivector (bivBlockPair p.1 p.2).1 (bivBlockPair p.1 p.2).2

private lemma bivBasis_linearIndependent : LinearIndependent ℝ bivBasis := by
  let mask : Fin 7 × Fin 4 → (Fin 8 → Bool) :=
    fun p k => decide (k = (bivBlockPair p.1 p.2).1 ∨ k = (bivBlockPair p.1 p.2).2)
  have hmask_inj : Function.Injective mask := by
    intro p q hpq
    have hfin : ∀ p₁ p₂ : Fin 7 × Fin 4,
        mask p₁ = mask p₂ → p₁ = p₂ := by
      intro p₁ p₂ hp
      fin_cases p₁ <;> fin_cases p₂ <;> first | rfl | exact absurd hp (by decide)
    exact hfin p q hpq
  have hcl : ∀ p : Fin 7 × Fin 4, bivBasis p = clMonomial (mask p) := by
    intro p
    let a := (bivBlockPair p.1 p.2).1
    let b := (bivBlockPair p.1 p.2).2
    have hab : a < b := bivBlockPair_lt p.1 p.2
    have hstep : ∀ k : ℕ, k ≤ 8 →
        clMonomialGenFrom cl44Gen k (mask p) =
          (if k ≤ a.val then cl44Gen a else 1) * (if k ≤ b.val then cl44Gen b else 1) := by
      intro k hk
      induction hd : 8 - k generalizing k with
      | zero =>
          have hk8 : k = 8 := by omega
          subst hk8
          rw [clMonomialGenFrom_ge cl44Gen 8 (le_refl _)]
          have ha8 : ¬ (8 ≤ a.val) := by omega
          have hb8 : ¬ (8 ≤ b.val) := by omega
          simp [ha8, hb8]
      | succ d ih =>
          have hklt : k < 8 := by omega
          rw [clMonomialGenFrom_step cl44Gen k hklt, ih (k + 1) (by omega) (by omega)]
          have hka : (⟨k, hklt⟩ : Fin 8) = a ↔ k = a.val := by
            simp [Fin.ext_iff]
          have hkb : (⟨k, hklt⟩ : Fin 8) = b ↔ k = b.val := by
            simp [Fin.ext_iff]
          have hm : mask p ⟨k, hklt⟩ = decide (k = a.val ∨ k = b.val) := by
            simp [mask, a, b, hka, hkb]
          rw [hm]
          have hab_ne : a.val ≠ b.val := ne_of_lt hab
          have hab_le : a.val ≤ b.val := le_of_lt hab
          by_cases h1 : k = a.val
          · subst h1
            have h2 : a.val + 1 ≤ b.val := hab
            simp [hab_ne, hab_le, h2]
          · by_cases h2 : k = b.val
            · subst h2
              have hna : ¬ (b.val ≤ a.val) := Nat.not_le.mpr hab
              have hna1 : ¬ (b.val + 1 ≤ a.val) := by omega
              simp [h1, hna, hna1]
            · have ha_iff : k ≤ a.val ↔ k + 1 ≤ a.val := by omega
              have hb_iff : k ≤ b.val ↔ k + 1 ≤ b.val := by omega
              simp [h1, h2, ha_iff, hb_iff]
    change cl44Bivector a b = clMonomialGenFrom cl44Gen 0 (mask p)
    rw [hstep 0 (Nat.zero_le _)]
    simp [cl44Bivector]
  have heq : bivBasis = fun p => clMonomial (mask p) := funext hcl
  rw [heq]
  exact clMonomial_linearIndependent.comp mask hmask_inj

private lemma cl44Bivector_mem_span_bivBasis {a b : Fin 8} (hab : a ≠ b) :
    cl44Bivector a b ∈ Submodule.span ℝ (Set.range bivBasis) := by
  have hlt : ∀ u v : Fin 8, u < v → ∃ p : Fin 7 × Fin 4, bivBlockPair p.1 p.2 = (u, v) := by
    intro u v huv
    fin_cases u <;> fin_cases v
    all_goals first
      | exact absurd huv (by decide)
      | exact ⟨(0, 0), rfl⟩ | exact ⟨(0, 1), rfl⟩ | exact ⟨(0, 2), rfl⟩ | exact ⟨(0, 3), rfl⟩
      | exact ⟨(1, 0), rfl⟩ | exact ⟨(1, 1), rfl⟩ | exact ⟨(1, 2), rfl⟩ | exact ⟨(1, 3), rfl⟩
      | exact ⟨(2, 0), rfl⟩ | exact ⟨(2, 1), rfl⟩ | exact ⟨(2, 2), rfl⟩ | exact ⟨(2, 3), rfl⟩
      | exact ⟨(3, 0), rfl⟩ | exact ⟨(3, 1), rfl⟩ | exact ⟨(3, 2), rfl⟩ | exact ⟨(3, 3), rfl⟩
      | exact ⟨(4, 0), rfl⟩ | exact ⟨(4, 1), rfl⟩ | exact ⟨(4, 2), rfl⟩ | exact ⟨(4, 3), rfl⟩
      | exact ⟨(5, 0), rfl⟩ | exact ⟨(5, 1), rfl⟩ | exact ⟨(5, 2), rfl⟩ | exact ⟨(5, 3), rfl⟩
      | exact ⟨(6, 0), rfl⟩ | exact ⟨(6, 1), rfl⟩ | exact ⟨(6, 2), rfl⟩ | exact ⟨(6, 3), rfl⟩
  rcases lt_or_gt_of_ne hab with h | h
  · rcases hlt a b h with ⟨p, hp⟩
    have hEq : cl44Bivector a b = bivBasis p := by
      unfold bivBasis
      rw [hp]
    rw [hEq]
    exact Submodule.subset_span ⟨p, rfl⟩
  · rcases hlt b a h with ⟨p, hp⟩
    have hswap : cl44Bivector a b = -cl44Bivector b a := by
      unfold cl44Bivector
      exact eq_neg_of_add_eq_zero_left (cl44Gen_anticomm hab)
    have hEq : cl44Bivector a b = -bivBasis p := by
      rw [hswap]
      unfold bivBasis
      rw [hp]
    rw [hEq]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨p, rfl⟩)

private lemma span_bivBasis_eq_cl44BivectorSpan :
    Submodule.span ℝ (Set.range bivBasis) = cl44BivectorSpan := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact Submodule.subset_span ⟨(bivBlockPair p.1 p.2).1, (bivBlockPair p.1 p.2).2,
      ne_of_lt (bivBlockPair_lt p.1 p.2), rfl⟩
  · rw [cl44BivectorSpan, Submodule.span_le]
    rintro _ ⟨a, b, hab, rfl⟩
    exact cl44Bivector_mem_span_bivBasis hab

/-- `Module.finrank ℝ cl44BivectorSpan = 28`. -/
lemma finrank_cl44BivectorSpan : Module.finrank ℝ cl44BivectorSpan = 28 := by
  rw [← span_bivBasis_eq_cl44BivectorSpan, finrank_span_eq_card bivBasis_linearIndependent,
    Fintype.card_prod, Fintype.card_fin]
  norm_num

/-- Strict derivation dimension ladder `14 < 28 < 120 < 255` inside `M₁₆(ℝ)`:
`g2Submodule ≤ cl44BivectorSpan ≤ so88KreinSubalgebra ≤ sl16Subalgebra`. -/
lemma derivation_dimension_ladder_strict :
    g2Submodule ≤ cl44BivectorSpan ∧
    cl44BivectorSpan ≤ so88KreinSubalgebra.toSubmodule ∧
    so88KreinSubalgebra.toSubmodule ≤ sl16Subalgebra.toSubmodule ∧
    Module.finrank ℝ g2Submodule = 14 ∧
    Module.finrank ℝ cl44BivectorSpan = 28 ∧
    Module.finrank ℝ so88KreinSubalgebra = 120 ∧
    Module.finrank ℝ sl16Subalgebra = 255 := by
  have h2_so : cl44BivectorSpan ≤ so88KreinSubalgebra.toSubmodule := by
    rw [cl44BivectorSpan, Submodule.span_le]
    rintro _ ⟨a, b, hab, rfl⟩
    exact (cl44Bivector_chiral_even_and_krein_skew hab).2
  have hso_sl : so88KreinSubalgebra.toSubmodule ≤ sl16Subalgebra.toSubmodule := by
    intro M hM
    change Mᵀ * kreinMetric88 + kreinMetric88 * M = 0 at hM
    have hM' : kreinMetric88 * M = -(Mᵀ * kreinMetric88) := eq_neg_of_add_eq_zero_right hM
    have hM'' : M = -(kreinMetric88 * Mᵀ * kreinMetric88) := by
      calc
        M = (kreinMetric88 * kreinMetric88) * M := by
              rw [kreinMetric88_properties.2.2.1, Matrix.one_mul]
        _ = kreinMetric88 * (kreinMetric88 * M) := Matrix.mul_assoc _ _ _
        _ = kreinMetric88 * (-(Mᵀ * kreinMetric88)) := by rw [hM']
        _ = -(kreinMetric88 * Mᵀ * kreinMetric88) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
    have htr : Matrix.trace M = -Matrix.trace M := by
      conv_lhs => rw [hM'']
      rw [Matrix.trace_neg, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        kreinMetric88_properties.2.2.1, Matrix.one_mul, Matrix.trace_transpose]
    change Matrix.trace M = 0
    linarith
  exact ⟨g2Submodule_le_bivectorSpan, h2_so, hso_sl,
    finrank_g2Submodule_and_owner_bridge.1, finrank_cl44BivectorSpan,
    finrank_so88KreinSubalgebra, finrank_sl16Subalgebra⟩

/-! ### 3. Intrinsic Cartan `S₃` Outer Triality on `cl44BivectorLieSubalgebra` (`M1b-T14-C3`) -/

private def bivBasisVec (p : Fin 7 × Fin 4) : cl44BivectorSpan :=
  ⟨bivBasis p, Submodule.subset_span ⟨(bivBlockPair p.1 p.2).1, (bivBlockPair p.1 p.2).2,
    ne_of_lt (bivBlockPair_lt p.1 p.2), rfl⟩⟩

private lemma bivBasisVec_linearIndependent : LinearIndependent ℝ bivBasisVec := by
  have hinj := bivBasis_linearIndependent
  rw [Fintype.linearIndependent_iff] at hinj ⊢
  intro c hc p
  have hc' : ∑ q : Fin 7 × Fin 4, c q • bivBasis q = 0 := by
    have hval := congrArg Subtype.val hc
    simpa [bivBasisVec] using hval
  exact hinj c hc' p

private noncomputable def bivBasisObj : Module.Basis (Fin 7 × Fin 4) ℝ cl44BivectorSpan :=
  Module.Basis.mk bivBasisVec_linearIndependent (by
    rintro ⟨M, hM⟩ _
    have hM' : M ∈ Submodule.span ℝ (Set.range bivBasis) := by
      rwa [span_bivBasis_eq_cl44BivectorSpan]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hM'
    have hx : (⟨M, hM⟩ : cl44BivectorSpan) = ∑ p : Fin 7 × Fin 4, c p • bivBasisVec p := by
      apply Subtype.ext
      simpa [bivBasisVec] using hc.symm
    rw [hx]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))

private lemma bivBasisObj_apply (p : Fin 7 × Fin 4) :
    (bivBasisObj p : Matrix Krein16Idx Krein16Idx ℝ) = bivBasis p := by
  dsimp [bivBasisObj]
  rw [Module.Basis.coe_mk]
  rfl

private lemma cl44Gen0_conj_bivector_mem {B : Matrix Krein16Idx Krein16Idx ℝ}
    (hB : B ∈ cl44BivectorSpan) :
    cl44Gen 0 * B * cl44Gen 0 ∈ cl44BivectorSpan := by
  refine Submodule.span_induction (hx := hB) ?_ ?_ ?_ ?_
  · rintro _ ⟨a, b, hab, rfl⟩
    by_cases ha : a = 0
    · subst ha
      have hanti := eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hab.symm)
      have hEq : cl44Gen 0 * cl44Bivector 0 b * cl44Gen 0 = -cl44Bivector 0 b := by
        unfold cl44Bivector
        calc
          cl44Gen 0 * (cl44Gen 0 * cl44Gen b) * cl44Gen 0
              = (cl44Gen 0 * cl44Gen 0) * (cl44Gen b * cl44Gen 0) := by
                  simp only [Matrix.mul_assoc]
          _ = 1 * (-(cl44Gen 0 * cl44Gen b)) := by
                  rw [cl44Gen_sq 0, hanti]; simp
          _ = -(cl44Gen 0 * cl44Gen b) := Matrix.one_mul _
      rw [hEq]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨0, b, hab, rfl⟩)
    · by_cases hb : b = 0
      · subst hb
        have hanti := eq_neg_of_add_eq_zero_left (cl44Gen_anticomm hab)
        have hEq : cl44Gen 0 * cl44Bivector a 0 * cl44Gen 0 = -cl44Bivector a 0 := by
          unfold cl44Bivector
          calc
            cl44Gen 0 * (cl44Gen a * cl44Gen 0) * cl44Gen 0
                = (cl44Gen 0 * cl44Gen a) * (cl44Gen 0 * cl44Gen 0) := by
                    simp only [Matrix.mul_assoc]
            _ = (-(cl44Gen a * cl44Gen 0)) * 1 := by
                    rw [cl44Gen_sq 0, hanti]; simp
            _ = -(cl44Gen a * cl44Gen 0) := Matrix.mul_one _
        rw [hEq]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨a, 0, hab, rfl⟩)
      · have ha' : cl44Gen 0 * cl44Gen a = -(cl44Gen a * cl44Gen 0) :=
          eq_neg_of_add_eq_zero_right (cl44Gen_anticomm ha)
        have hb' : cl44Gen 0 * cl44Gen b = -(cl44Gen b * cl44Gen 0) :=
          eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hb)
        have hEq : cl44Gen 0 * cl44Bivector a b * cl44Gen 0 = cl44Bivector a b := by
          unfold cl44Bivector
          calc
            cl44Gen 0 * (cl44Gen a * cl44Gen b) * cl44Gen 0
                = (cl44Gen 0 * cl44Gen a) * cl44Gen b * cl44Gen 0 := by
                    simp only [Matrix.mul_assoc]
            _ = (-(cl44Gen a * cl44Gen 0)) * cl44Gen b * cl44Gen 0 := by rw [ha']
            _ = -(cl44Gen a * ((cl44Gen 0 * cl44Gen b) * cl44Gen 0)) := by
                    simp only [Matrix.neg_mul, Matrix.mul_assoc]
            _ = -(cl44Gen a * ((-(cl44Gen b * cl44Gen 0)) * cl44Gen 0)) := by rw [hb']
            _ = cl44Gen a * (cl44Gen b * (cl44Gen 0 * cl44Gen 0)) := by
                    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
            _ = cl44Gen a * cl44Gen b := by rw [cl44Gen_sq 0]; simp
        rw [hEq]
        exact Submodule.subset_span ⟨a, b, hab, rfl⟩
  · rw [Matrix.mul_zero, Matrix.zero_mul]
    exact Submodule.zero_mem _
  · intro X Y _ _ hX hY
    rw [Matrix.mul_add, Matrix.add_mul]
    exact Submodule.add_mem _ hX hY
  · intro r X _ hX
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact Submodule.smul_mem _ r hX

/-- Order-2 Cartan triality involution `σ(B) = e₀ B e₀` acting intrinsically on
`cl44BivectorLieSubalgebra`. -/
noncomputable def trialitySigma3 :
    cl44BivectorLieSubalgebra ≃ₗ⁅ℝ⁆ cl44BivectorLieSubalgebra :=
  let e0sq : cl44Gen 0 * cl44Gen 0 = 1 := by rw [cl44Gen_sq 0]; simp
  let f : cl44BivectorLieSubalgebra →ₗ⁅ℝ⁆ cl44BivectorLieSubalgebra :=
    { toFun := fun B => ⟨cl44Gen 0 * B.1 * cl44Gen 0, cl44Gen0_conj_bivector_mem B.2⟩
      map_add' := fun A B => by
        apply Subtype.ext
        change cl44Gen 0 * (A.1 + B.1) * cl44Gen 0 =
          cl44Gen 0 * A.1 * cl44Gen 0 + cl44Gen 0 * B.1 * cl44Gen 0
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r A => by
        apply Subtype.ext
        change cl44Gen 0 * (r • A.1) * cl44Gen 0 = r • (cl44Gen 0 * A.1 * cl44Gen 0)
        rw [Matrix.mul_smul, Matrix.smul_mul]
      map_lie' := fun {A B} => by
        apply Subtype.ext
        change cl44Gen 0 * (A.1 * B.1 - B.1 * A.1) * cl44Gen 0 =
          (cl44Gen 0 * A.1 * cl44Gen 0) * (cl44Gen 0 * B.1 * cl44Gen 0) -
          (cl44Gen 0 * B.1 * cl44Gen 0) * (cl44Gen 0 * A.1 * cl44Gen 0)
        have h1 : (cl44Gen 0 * A.1 * cl44Gen 0) * (cl44Gen 0 * B.1 * cl44Gen 0) =
            cl44Gen 0 * (A.1 * B.1) * cl44Gen 0 := by
          calc
            (cl44Gen 0 * A.1 * cl44Gen 0) * (cl44Gen 0 * B.1 * cl44Gen 0)
                = cl44Gen 0 * A.1 * (cl44Gen 0 * cl44Gen 0) * B.1 * cl44Gen 0 := by
                    simp only [Matrix.mul_assoc]
            _ = cl44Gen 0 * (A.1 * B.1) * cl44Gen 0 := by
                    rw [e0sq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        have h2 : (cl44Gen 0 * B.1 * cl44Gen 0) * (cl44Gen 0 * A.1 * cl44Gen 0) =
            cl44Gen 0 * (B.1 * A.1) * cl44Gen 0 := by
          calc
            (cl44Gen 0 * B.1 * cl44Gen 0) * (cl44Gen 0 * A.1 * cl44Gen 0)
                = cl44Gen 0 * B.1 * (cl44Gen 0 * cl44Gen 0) * A.1 * cl44Gen 0 := by
                    simp only [Matrix.mul_assoc]
            _ = cl44Gen 0 * (B.1 * A.1) * cl44Gen 0 := by
                    rw [e0sq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        rw [h1, h2, Matrix.mul_sub, Matrix.sub_mul] }
  have hinv : Function.LeftInverse f f := by
    intro B
    apply Subtype.ext
    change cl44Gen 0 * (cl44Gen 0 * B.1 * cl44Gen 0) * cl44Gen 0 = B.1
    calc
      cl44Gen 0 * (cl44Gen 0 * B.1 * cl44Gen 0) * cl44Gen 0
          = (cl44Gen 0 * cl44Gen 0) * B.1 * (cl44Gen 0 * cl44Gen 0) := by
              simp only [Matrix.mul_assoc]
      _ = B.1 := by rw [e0sq, Matrix.one_mul, Matrix.mul_one]
  { f with
    invFun := f
    left_inv := hinv
    right_inv := hinv }

private def projPlus : Matrix Krein16Idx Krein16Idx ℝ :=
  (1 / 2 : ℝ) • ((1 : Matrix Krein16Idx Krein16Idx ℝ) + gamma44)

private lemma projPlus_idem : projPlus * projPlus = projPlus := by
  unfold projPlus
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, gamma44_properties.2.1]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

private lemma bivectorSpan_comm_projPlus {B : Matrix Krein16Idx Krein16Idx ℝ}
    (hB : B ∈ cl44BivectorSpan) : B * projPlus = projPlus * B := by
  have hgam : B * gamma44 = gamma44 * B := by
    refine Submodule.span_induction (hx := hB) ?_ ?_ ?_ ?_
    · rintro _ ⟨a, b, hab, rfl⟩
      exact (cl44Bivector_chiral_even_and_krein_skew hab).1
    · simp
    · intro X Y _ _ hX hY
      rw [Matrix.add_mul, Matrix.mul_add, hX, hY]
    · intro r X _ hX
      rw [Matrix.smul_mul, Matrix.mul_smul, hX]
  unfold projPlus
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, hgam]

private def rhoPlus : cl44BivectorLieSubalgebra →ₗ⁅ℝ⁆ Matrix Krein16Idx Krein16Idx ℝ where
  toFun B := projPlus * B.1
  map_add' A B := by simp [Matrix.mul_add]
  map_smul' r A := by simp
  map_lie' {A B} := by
    change projPlus * (A.1 * B.1 - B.1 * A.1) =
      (projPlus * A.1) * (projPlus * B.1) - (projPlus * B.1) * (projPlus * A.1)
    have hA : A.1 * projPlus = projPlus * A.1 := bivectorSpan_comm_projPlus A.2
    have hB : B.1 * projPlus = projPlus * B.1 := bivectorSpan_comm_projPlus B.2
    have h1 : (projPlus * A.1) * (projPlus * B.1) = projPlus * (A.1 * B.1) := by
      calc
        (projPlus * A.1) * (projPlus * B.1)
            = projPlus * (A.1 * projPlus) * B.1 := by simp only [Matrix.mul_assoc]
        _ = projPlus * (projPlus * A.1) * B.1 := by rw [hA]
        _ = (projPlus * projPlus) * (A.1 * B.1) := by simp only [Matrix.mul_assoc]
        _ = projPlus * (A.1 * B.1) := by rw [projPlus_idem]
    have h2 : (projPlus * B.1) * (projPlus * A.1) = projPlus * (B.1 * A.1) := by
      calc
        (projPlus * B.1) * (projPlus * A.1)
            = projPlus * (B.1 * projPlus) * A.1 := by simp only [Matrix.mul_assoc]
        _ = projPlus * (projPlus * B.1) * A.1 := by rw [hB]
        _ = (projPlus * projPlus) * (B.1 * A.1) := by simp only [Matrix.mul_assoc]
        _ = projPlus * (B.1 * A.1) := by rw [projPlus_idem]
    rw [h1, h2, Matrix.mul_sub]

private lemma trace_gamma44_bivector_mul {a b c d : Fin 8} :
    Matrix.trace (gamma44 * cl44Bivector a b * cl44Bivector c d) = 0 := by
  let S : Finset (Fin 8) := {a, b, c, d}
  have hcard : S.card < 8 := by
    have h1 : S.card ≤ ({b, c, d} : Finset (Fin 8)).card + 1 := Finset.card_insert_le _ _
    have h2 : ({b, c, d} : Finset (Fin 8)).card ≤ ({c, d} : Finset (Fin 8)).card + 1 :=
      Finset.card_insert_le _ _
    have h3 : ({c, d} : Finset (Fin 8)).card ≤ ({d} : Finset (Fin 8)).card + 1 :=
      Finset.card_insert_le _ _
    have h4 : ({d} : Finset (Fin 8)).card = 1 := Finset.card_singleton d
    omega
  have hex : ∃ i : Fin 8, i ∉ S := by
    by_contra h
    push Not at h
    have hsub : Finset.univ ⊆ S := fun i _ => h i
    have hle := Finset.card_le_card hsub
    rw [Finset.card_fin] at hle
    omega
  rcases hex with ⟨i, hiS⟩
  have hia : i ≠ a := fun h => hiS (by simp [S, h])
  have hib : i ≠ b := fun h => hiS (by simp [S, h])
  have hic : i ≠ c := fun h => hiS (by simp [S, h])
  have hid : i ≠ d := fun h => hiS (by simp [S, h])
  have hcom1 : cl44Bivector a b * cl44Gen i = cl44Gen i * cl44Bivector a b :=
    sub_eq_zero.mp (cl44Bivector_orthogonal_shear.1 hia hib)
  have hcom2 : cl44Bivector c d * cl44Gen i = cl44Gen i * cl44Bivector c d :=
    sub_eq_zero.mp (cl44Bivector_orthogonal_shear.1 hic hid)
  have hgam : gamma44 * cl44Gen i = -(cl44Gen i * gamma44) :=
    eq_neg_of_add_eq_zero_right (gamma44_properties.2.2.2 i)
  let s : ℝ := if i.val < 4 then 1 else -1
  have hgi_sq : cl44Gen i * cl44Gen i = s • (1 : Matrix Krein16Idx Krein16Idx ℝ) := by
    rw [cl44Gen_sq i]
    dsimp [s]
    split_ifs <;> simp
  have hconj :
      cl44Gen i * (gamma44 * cl44Bivector a b * cl44Bivector c d) * cl44Gen i =
        (-s) • (gamma44 * cl44Bivector a b * cl44Bivector c d) := by
    calc
      cl44Gen i * (gamma44 * cl44Bivector a b * cl44Bivector c d) * cl44Gen i
          = (cl44Gen i * gamma44) * cl44Bivector a b * (cl44Bivector c d * cl44Gen i) := by
              simp only [Matrix.mul_assoc]
      _ = (-(gamma44 * cl44Gen i)) * cl44Bivector a b * (cl44Gen i * cl44Bivector c d) := by
              rw [hcom2]; simp only [hgam, neg_neg]
      _ = -(gamma44 * (cl44Gen i * cl44Bivector a b) * cl44Gen i * cl44Bivector c d) := by
              simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(gamma44 * (cl44Bivector a b * cl44Gen i) * cl44Gen i * cl44Bivector c d) := by
              rw [hcom1]
      _ = -(gamma44 * cl44Bivector a b * (cl44Gen i * cl44Gen i) * cl44Bivector c d) := by
              simp only [Matrix.mul_assoc]
      _ = -(s • (gamma44 * cl44Bivector a b * cl44Bivector c d)) := by
              rw [hgi_sq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = (-s) • (gamma44 * cl44Bivector a b * cl44Bivector c d) := (neg_smul _ _).symm
  have htr :
      s * Matrix.trace (gamma44 * cl44Bivector a b * cl44Bivector c d) =
        (-s) * Matrix.trace (gamma44 * cl44Bivector a b * cl44Bivector c d) := by
    calc
      s * Matrix.trace (gamma44 * cl44Bivector a b * cl44Bivector c d)
          = Matrix.trace ((gamma44 * cl44Bivector a b * cl44Bivector c d) *
              (cl44Gen i * cl44Gen i)) := by
                rw [hgi_sq, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
      _ = Matrix.trace (cl44Gen i * (gamma44 * cl44Bivector a b * cl44Bivector c d) *
            cl44Gen i) := by
            rw [← Matrix.mul_assoc, Matrix.trace_mul_comm _ (cl44Gen i), ← Matrix.mul_assoc]
      _ = (-s) * Matrix.trace (gamma44 * cl44Bivector a b * cl44Bivector c d) := by
            rw [hconj, Matrix.trace_smul, smul_eq_mul]
  have hs0 : s ≠ 0 := by dsimp [s]; split_ifs <;> norm_num
  have htr2 : (2 * s) * Matrix.trace (gamma44 * cl44Bivector a b * cl44Bivector c d) = 0 := by
    linarith
  exact (mul_eq_zero.mp htr2).resolve_left (mul_ne_zero two_ne_zero hs0)

private lemma trace_gamma44_bivectorSpan {M N : Matrix Krein16Idx Krein16Idx ℝ}
    (hM : M ∈ cl44BivectorSpan) (hN : N ∈ cl44BivectorSpan) :
    Matrix.trace (gamma44 * M * N) = 0 := by
  refine Submodule.span_induction (hx := hM) ?_ ?_ ?_ ?_
  · rintro _ ⟨a, b, _, rfl⟩
    refine Submodule.span_induction (hx := hN) ?_ ?_ ?_ ?_
    · rintro _ ⟨c, d, _, rfl⟩
      exact trace_gamma44_bivector_mul
    · simp
    · intro X Y _ _ hX hY
      rw [Matrix.mul_add, Matrix.trace_add, hX, hY, add_zero]
    · intro r X _ hX
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hX, mul_zero]
  · simp
  · intro X Y _ _ hX hY
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, hX, hY, add_zero]
  · intro r X _ hX
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hX, mul_zero]

private lemma trace_bivBasis_mul (p q : Fin 7 × Fin 4) :
    Matrix.trace (bivBasis p * bivBasis q) =
      if p = q then -16 * ((if (bivBlockPair p.1 p.2).1.val < 4 then (1 : ℝ) else -1) *
        (if (bivBlockPair p.1 p.2).2.val < 4 then (1 : ℝ) else -1)) else 0 := by
  let a := (bivBlockPair p.1 p.2).1
  let b := (bivBlockPair p.1 p.2).2
  let c := (bivBlockPair q.1 q.2).1
  let d := (bivBlockPair q.1 q.2).2
  have hab : a < b := bivBlockPair_lt p.1 p.2
  have hcd : c < d := bivBlockPair_lt q.1 q.2
  by_cases hpq : p = q
  · subst hpq
    simp only [↓reduceIte]
    have hsq : bivBasis p * bivBasis p =
        -((if a.val < 4 then (1 : ℝ) else -1) * (if b.val < 4 then (1 : ℝ) else -1)) •
          (1 : Matrix Krein16Idx Krein16Idx ℝ) := by
      have hanti : cl44Gen b * cl44Gen a = -(cl44Gen a * cl44Gen b) :=
        eq_neg_of_add_eq_zero_right (cl44Gen_anticomm (ne_of_lt hab))
      calc
        bivBasis p * bivBasis p
            = cl44Gen a * (cl44Gen b * cl44Gen a) * cl44Gen b := by
                simp only [bivBasis, cl44Bivector, a, b, Matrix.mul_assoc]
        _ = -(cl44Gen a * cl44Gen a * (cl44Gen b * cl44Gen b)) := by
                rw [hanti]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        _ = -((if a.val < 4 then (1 : ℝ) else -1) * (if b.val < 4 then (1 : ℝ) else -1)) •
              (1 : Matrix Krein16Idx Krein16Idx ℝ) := by
              rw [cl44Gen_sq a, cl44Gen_sq b]
              split_ifs <;> simp
    rw [hsq, Matrix.trace_smul, Matrix.trace_one, card_krein16Idx]
    simp only [a, b, smul_eq_mul, neg_mul]
    split_ifs <;> norm_num
  · simp only [hpq, ↓reduceIte]
    have hne : (a, b) ≠ (c, d) := by
      intro heq
      apply hpq
      have hfin : ∀ p₁ p₂ : Fin 7 × Fin 4,
          bivBlockPair p₁.1 p₁.2 = bivBlockPair p₂.1 p₂.2 → p₁ = p₂ := by
        intro p₁ p₂ hp
        fin_cases p₁ <;> fin_cases p₂ <;> first | rfl | exact absurd hp (by decide)
      exact hfin p q heq
    let mask_p : Fin 8 → Bool := fun k => decide (k = a ∨ k = b)
    let mask_q : Fin 8 → Bool := fun k => decide (k = c ∨ k = d)
    have hmp : bivBasis p = clMonomial mask_p := by
      have hstep : ∀ k : ℕ, k ≤ 8 →
          clMonomialGenFrom cl44Gen k mask_p =
            (if k ≤ a.val then cl44Gen a else 1) * (if k ≤ b.val then cl44Gen b else 1) := by
        intro k hk
        induction hd : 8 - k generalizing k with
        | zero =>
            have hk8 : k = 8 := by omega
            subst hk8
            rw [clMonomialGenFrom_ge cl44Gen 8 (le_refl _)]
            have ha8 : ¬ (8 ≤ a.val) := by omega
            have hb8 : ¬ (8 ≤ b.val) := by omega
            simp [ha8, hb8]
        | succ d' ih =>
            have hklt : k < 8 := by omega
            rw [clMonomialGenFrom_step cl44Gen k hklt, ih (k + 1) (by omega) (by omega)]
            have hka : (⟨k, hklt⟩ : Fin 8) = a ↔ k = a.val := by simp [Fin.ext_iff]
            have hkb : (⟨k, hklt⟩ : Fin 8) = b ↔ k = b.val := by simp [Fin.ext_iff]
            have hm : mask_p ⟨k, hklt⟩ = decide (k = a.val ∨ k = b.val) := by
              simp [mask_p, hka, hkb]
            rw [hm]
            have hab_ne : a.val ≠ b.val := ne_of_lt hab
            have hab_le : a.val ≤ b.val := le_of_lt hab
            by_cases h1 : k = a.val
            · subst h1
              have h2 : a.val + 1 ≤ b.val := hab
              simp [hab_ne, hab_le, h2]
            · by_cases h2 : k = b.val
              · subst h2
                have hna : ¬ (b.val ≤ a.val) := Nat.not_le.mpr hab
                have hna1 : ¬ (b.val + 1 ≤ a.val) := by omega
                simp [h1, hna, hna1]
              · have ha_iff : k ≤ a.val ↔ k + 1 ≤ a.val := by omega
                have hb_iff : k ≤ b.val ↔ k + 1 ≤ b.val := by omega
                simp [h1, h2, ha_iff, hb_iff]
      change cl44Bivector a b = clMonomialGenFrom cl44Gen 0 mask_p
      rw [hstep 0 (Nat.zero_le _)]
      simp [cl44Bivector]
    have hmq : bivBasis q = clMonomial mask_q := by
      have hstep : ∀ k : ℕ, k ≤ 8 →
          clMonomialGenFrom cl44Gen k mask_q =
            (if k ≤ c.val then cl44Gen c else 1) * (if k ≤ d.val then cl44Gen d else 1) := by
        intro k hk
        induction hd : 8 - k generalizing k with
        | zero =>
            have hk8 : k = 8 := by omega
            subst hk8
            rw [clMonomialGenFrom_ge cl44Gen 8 (le_refl _)]
            have hc8 : ¬ (8 ≤ c.val) := by omega
            have hd8 : ¬ (8 ≤ d.val) := by omega
            simp [hc8, hd8]
        | succ d' ih =>
            have hklt : k < 8 := by omega
            rw [clMonomialGenFrom_step cl44Gen k hklt, ih (k + 1) (by omega) (by omega)]
            have hkc : (⟨k, hklt⟩ : Fin 8) = c ↔ k = c.val := by simp [Fin.ext_iff]
            have hkd : (⟨k, hklt⟩ : Fin 8) = d ↔ k = d.val := by simp [Fin.ext_iff]
            have hm : mask_q ⟨k, hklt⟩ = decide (k = c.val ∨ k = d.val) := by
              simp [mask_q, hkc, hkd]
            rw [hm]
            have hcd_ne : c.val ≠ d.val := ne_of_lt hcd
            have hcd_le : c.val ≤ d.val := le_of_lt hcd
            by_cases h1 : k = c.val
            · subst h1
              have h2 : c.val + 1 ≤ d.val := hcd
              simp [hcd_ne, hcd_le, h2]
            · by_cases h2 : k = d.val
              · subst h2
                have hnc : ¬ (d.val ≤ c.val) := Nat.not_le.mpr hcd
                have hnc1 : ¬ (d.val + 1 ≤ c.val) := by omega
                simp [h1, hnc, hnc1]
              · have hc_iff : k ≤ c.val ↔ k + 1 ≤ c.val := by omega
                have hd_iff : k ≤ d.val ↔ k + 1 ≤ d.val := by omega
                simp [h1, h2, hc_iff, hd_iff]
      change cl44Bivector c d = clMonomialGenFrom cl44Gen 0 mask_q
      rw [hstep 0 (Nat.zero_le _)]
      simp [cl44Bivector]
    rw [hmp, hmq]
    rcases clMonomial_mul mask_p mask_q with ⟨s, _, hprod⟩
    rw [hprod, Matrix.trace_smul, smul_eq_mul, trace_clMonomial]
    have hdiff : (fun j => xor (mask_p j) (mask_q j)) ≠ (fun _ => false) := by
      intro heq
      have hmask_eq : mask_p = mask_q := by
        funext j
        have hj := congrFun heq j
        cases hpj : mask_p j <;> cases hqj : mask_q j <;> simp_all
      apply hne
      have ha_q : a = c ∨ a = d := by
        have ha : mask_q a = true := by rw [← hmask_eq]; simp [mask_p]
        simpa [mask_q] using ha
      have hb_q : b = c ∨ b = d := by
        have hb : mask_q b = true := by rw [← hmask_eq]; simp [mask_p]
        simpa [mask_q] using hb
      rcases ha_q with hac | had <;> rcases hb_q with hbc | hbd
      · rw [hac, hbc] at hab; exact absurd hab (lt_irrefl _)
      · exact Prod.ext hac hbd
      · rw [hbc, had] at hab; exact absurd (lt_trans hab hcd) (lt_irrefl _)
      · rw [had, hbd] at hab; exact absurd hab (lt_irrefl _)
    simp [hdiff]

private lemma rhoPlus_injective : Function.Injective rhoPlus := by
  rw [injective_iff_map_eq_zero]
  intro B hB
  apply Subtype.ext
  have hM : B.1 ∈ Submodule.span ℝ (Set.range bivBasis) := by
    rw [span_bivBasis_eq_cl44BivectorSpan]
    exact B.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hM
  have hc0 : ∀ p : Fin 7 × Fin 4, c p = 0 := by
    intro p
    have htr0 : Matrix.trace (projPlus * B.1 * bivBasis p) = 0 := by
      change Matrix.trace (rhoPlus B * bivBasis p) = 0
      rw [hB, Matrix.zero_mul, Matrix.trace_zero]
    have hgam0 : Matrix.trace (gamma44 * B.1 * bivBasis p) = 0 :=
      trace_gamma44_bivectorSpan B.2 (Submodule.subset_span
        ⟨(bivBlockPair p.1 p.2).1, (bivBlockPair p.1 p.2).2,
          ne_of_lt (bivBlockPair_lt p.1 p.2), rfl⟩)
    have htr_eq : Matrix.trace (projPlus * B.1 * bivBasis p) =
        (1 / 2 : ℝ) * Matrix.trace (B.1 * bivBasis p) := by
      unfold projPlus
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
        Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, hgam0, add_zero]
    rw [htr_eq] at htr0
    have htrB0 : Matrix.trace (B.1 * bivBasis p) = 0 :=
      (mul_eq_zero.mp htr0).resolve_left (by norm_num)
    rw [← hc, Matrix.sum_mul, Matrix.trace_sum] at htrB0
    have hterm : ∀ q : Fin 7 × Fin 4,
        Matrix.trace ((c q • bivBasis q) * bivBasis p) =
          if q = p then c p * (-16 * ((if (bivBlockPair p.1 p.2).1.val < 4 then (1 : ℝ) else -1) *
            (if (bivBlockPair p.1 p.2).2.val < 4 then (1 : ℝ) else -1))) else 0 := by
      intro q
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_bivBasis_mul]
      by_cases hqp : q = p
      · subst hqp; simp
      · simp [hqp]
    simp_rw [hterm] at htrB0
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at htrB0
    have hd0 : -16 * ((if (bivBlockPair p.1 p.2).1.val < 4 then (1 : ℝ) else -1) *
        (if (bivBlockPair p.1 p.2).2.val < 4 then (1 : ℝ) else -1)) ≠ 0 := by
      split_ifs <;> norm_num
    exact (mul_eq_zero.mp htrB0).resolve_right hd0
  rw [← hc]
  simp only [hc0, zero_smul, Finset.sum_const_zero]
  rfl

private def psiPlusProj : Matrix Krein16Idx Krein16Idx ℝ :=
  tensor4 cl11P0 cl11P0 cl11P0 cl11P0 + tensor4 cl11Up cl11Up cl11Up cl11Up +
  tensor4 cl11Down cl11Down cl11Down cl11Down + tensor4 cl11P1 cl11P1 cl11P1 cl11P1

private def reflPsiPlus : Matrix Krein16Idx Krein16Idx ℝ :=
  (1 : Matrix Krein16Idx Krein16Idx ℝ) - psiPlusProj

section MatrixUnitExpandLocal

attribute [local simp]
  tensor4_mul tensor4_one
  tensor4_zero_0 tensor4_zero_1 tensor4_zero_2 tensor4_zero_3
  tensor4_neg_0 tensor4_neg_1 tensor4_neg_2 tensor4_neg_3
  add_mul mul_add sub_mul mul_sub neg_mul mul_neg
  mul_assoc one_mul mul_one zero_mul mul_zero
  cl11Pos_sq cl11Neg_sq cl11Grad_sq
  cl11Pos_mul_cl11Neg cl11Neg_mul_cl11Pos
  cl11Neg_mul_cl11Grad cl11Grad_mul_cl11Neg
  cl11Pos_mul_cl11Grad cl11Grad_mul_cl11Pos
  cl11Up_mul_cl11Up cl11Down_mul_cl11Down cl11Up_mul_cl11Down cl11Down_mul_cl11Up
  cl11P0_mul_cl11P0 cl11P1_mul_cl11P1 cl11P0_mul_cl11P1 cl11P1_mul_cl11P0
  cl11Grad_mul_cl11Up cl11Up_mul_cl11Grad cl11Grad_mul_cl11Down cl11Down_mul_cl11Grad
  cl11Grad_mul_cl11P0 cl11P0_mul_cl11Grad cl11Grad_mul_cl11P1 cl11P1_mul_cl11Grad
  cl11P0_mul_cl11Up cl11P1_mul_cl11Up cl11Up_mul_cl11P0 cl11Up_mul_cl11P1
  cl11P0_mul_cl11Down cl11P1_mul_cl11Down cl11Down_mul_cl11P0 cl11Down_mul_cl11P1
  cl11Pos_mul_cl11P0 cl11P0_mul_cl11Pos cl11Pos_mul_cl11P1 cl11P1_mul_cl11Pos
  cl11Neg_mul_cl11P0 cl11P0_mul_cl11Neg cl11Neg_mul_cl11P1 cl11P1_mul_cl11Neg
  cl11Pos_mul_cl11Up cl11Up_mul_cl11Pos cl11Pos_mul_cl11Down cl11Down_mul_cl11Pos
  cl11Neg_mul_cl11Up cl11Up_mul_cl11Neg cl11Neg_mul_cl11Down cl11Down_mul_cl11Neg

private lemma reflPsiPlus_sq : reflPsiPlus * reflPsiPlus = 1 := by
  have hsq : psiPlusProj * psiPlusProj = (2 : ℝ) • psiPlusProj := by
    unfold psiPlusProj
    simp
    module
  unfold reflPsiPlus
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one, hsq, two_smul]
  abel

private lemma reflPsiPlus_comm_projPlus : reflPsiPlus * projPlus = projPlus * reflPsiPlus := by
  have hgam : psiPlusProj * gamma44 = psiPlusProj ∧ gamma44 * psiPlusProj = psiPlusProj := by
    unfold psiPlusProj gamma44
    constructor <;> (simp; try module)
  unfold reflPsiPlus projPlus
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, hgam.1, hgam.2]

private def sigmaPlusBlockMat : Fin 7 → Fin 4 → Fin 4 → ℝ
  | 0 => ![![1/2, 1/2, -1/2, 1/2], ![1/2, 1/2, 1/2, -1/2],
           ![-1/2, 1/2, 1/2, 1/2], ![1/2, -1/2, 1/2, 1/2]]
  | 1 => ![![1/2, -1/2, -1/2, -1/2], ![-1/2, 1/2, -1/2, -1/2],
           ![-1/2, -1/2, 1/2, -1/2], ![-1/2, -1/2, -1/2, 1/2]]
  | 2 => ![![1/2, 1/2, -1/2, 1/2], ![1/2, 1/2, 1/2, -1/2],
           ![-1/2, 1/2, 1/2, 1/2], ![1/2, -1/2, 1/2, 1/2]]
  | 3 => ![![1/2, -1/2, -1/2, -1/2], ![-1/2, 1/2, -1/2, -1/2],
           ![-1/2, -1/2, 1/2, -1/2], ![-1/2, -1/2, -1/2, 1/2]]
  | 4 => ![![1/2, 1/2, -1/2, 1/2], ![1/2, 1/2, 1/2, -1/2],
           ![-1/2, 1/2, 1/2, 1/2], ![1/2, -1/2, 1/2, 1/2]]
  | 5 => ![![1/2, 1/2, 1/2, -1/2], ![1/2, 1/2, -1/2, 1/2],
           ![1/2, -1/2, 1/2, 1/2], ![-1/2, 1/2, 1/2, 1/2]]
  | 6 => ![![1/2, -1/2, 1/2, 1/2], ![-1/2, 1/2, 1/2, 1/2],
           ![1/2, 1/2, 1/2, -1/2], ![1/2, 1/2, -1/2, 1/2]]

private noncomputable def sigmaPlusLin : cl44BivectorSpan →ₗ[ℝ] cl44BivectorSpan :=
  bivBasisObj.constr ℝ fun p =>
    ∑ j : Fin 4, sigmaPlusBlockMat p.1 j p.2 • bivBasisObj (p.1, j)

private lemma sigmaPlusLin_basis (i : Fin 7) (k : Fin 4) :
    (sigmaPlusLin (bivBasisObj (i, k)) : Matrix Krein16Idx Krein16Idx ℝ) =
      ∑ j : Fin 4, sigmaPlusBlockMat i j k • bivBasis (i, j) := by
  unfold sigmaPlusLin
  rw [Module.Basis.constr_basis]
  simp [bivBasisObj_apply]

private lemma sigmaPlusLin_rhoPlus_b0 (k : Fin 4) :
    projPlus * ∑ j : Fin 4, sigmaPlusBlockMat 0 j k • bivBasis (0, j) =
      reflPsiPlus * (projPlus * bivBasis (0, k)) * reflPsiPlus := by
  fin_cases k <;>
    (simp only [Fin.sum_univ_four, sigmaPlusBlockMat, bivBasis, bivBlockPair, cl44Bivector,
        cl44Gen, gamma44, projPlus, reflPsiPlus, psiPlusProj];
      simp;
      simp only [cl11One_eq_P0_add_P1, cl11Grad_eq_P0_sub_P1, cl11Pos_eq_Up_add_Down,
        cl11Neg_eq_Down_sub_Up, tensor4_add_0, tensor4_add_1, tensor4_add_2, tensor4_add_3,
        tensor4_sub_0, tensor4_sub_1, tensor4_sub_2, tensor4_sub_3];
      module)

private lemma sigmaPlusLin_rhoPlus_b1 (k : Fin 4) :
    projPlus * ∑ j : Fin 4, sigmaPlusBlockMat 1 j k • bivBasis (1, j) =
      reflPsiPlus * (projPlus * bivBasis (1, k)) * reflPsiPlus := by
  fin_cases k <;>
    (simp only [Fin.sum_univ_four, sigmaPlusBlockMat, bivBasis, bivBlockPair, cl44Bivector,
        cl44Gen, gamma44, projPlus, reflPsiPlus, psiPlusProj];
      simp;
      simp only [cl11One_eq_P0_add_P1, cl11Grad_eq_P0_sub_P1, cl11Pos_eq_Up_add_Down,
        cl11Neg_eq_Down_sub_Up, tensor4_add_0, tensor4_add_1, tensor4_add_2, tensor4_add_3,
        tensor4_sub_0, tensor4_sub_1, tensor4_sub_2, tensor4_sub_3];
      module)

private lemma sigmaPlusLin_rhoPlus_b2 (k : Fin 4) :
    projPlus * ∑ j : Fin 4, sigmaPlusBlockMat 2 j k • bivBasis (2, j) =
      reflPsiPlus * (projPlus * bivBasis (2, k)) * reflPsiPlus := by
  fin_cases k <;>
    (simp only [Fin.sum_univ_four, sigmaPlusBlockMat, bivBasis, bivBlockPair, cl44Bivector,
        cl44Gen, gamma44, projPlus, reflPsiPlus, psiPlusProj];
      simp;
      simp only [cl11One_eq_P0_add_P1, cl11Grad_eq_P0_sub_P1, cl11Pos_eq_Up_add_Down,
        cl11Neg_eq_Down_sub_Up, tensor4_add_0, tensor4_add_1, tensor4_add_2, tensor4_add_3,
        tensor4_sub_0, tensor4_sub_1, tensor4_sub_2, tensor4_sub_3];
      module)

private lemma sigmaPlusLin_rhoPlus_b3 (k : Fin 4) :
    projPlus * ∑ j : Fin 4, sigmaPlusBlockMat 3 j k • bivBasis (3, j) =
      reflPsiPlus * (projPlus * bivBasis (3, k)) * reflPsiPlus := by
  fin_cases k <;>
    (simp only [Fin.sum_univ_four, sigmaPlusBlockMat, bivBasis, bivBlockPair, cl44Bivector,
        cl44Gen, gamma44, projPlus, reflPsiPlus, psiPlusProj];
      simp;
      simp only [cl11One_eq_P0_add_P1, cl11Grad_eq_P0_sub_P1,
        tensor4_add_0, tensor4_add_1, tensor4_add_2, tensor4_add_3,
        tensor4_sub_0, tensor4_sub_1, tensor4_sub_2, tensor4_sub_3];
      module)

private lemma sigmaPlusLin_rhoPlus_b4 (k : Fin 4) :
    projPlus * ∑ j : Fin 4, sigmaPlusBlockMat 4 j k • bivBasis (4, j) =
      reflPsiPlus * (projPlus * bivBasis (4, k)) * reflPsiPlus := by
  fin_cases k <;>
    (simp only [Fin.sum_univ_four, sigmaPlusBlockMat, bivBasis, bivBlockPair, cl44Bivector,
        cl44Gen, gamma44, projPlus, reflPsiPlus, psiPlusProj];
      simp;
      simp only [cl11One_eq_P0_add_P1, cl11Grad_eq_P0_sub_P1, cl11Pos_eq_Up_add_Down,
        cl11Neg_eq_Down_sub_Up, tensor4_add_0, tensor4_add_1, tensor4_add_2, tensor4_add_3,
        tensor4_sub_0, tensor4_sub_1, tensor4_sub_2, tensor4_sub_3];
      module)

private lemma sigmaPlusLin_rhoPlus_b5 (k : Fin 4) :
    projPlus * ∑ j : Fin 4, sigmaPlusBlockMat 5 j k • bivBasis (5, j) =
      reflPsiPlus * (projPlus * bivBasis (5, k)) * reflPsiPlus := by
  fin_cases k <;>
    (simp only [Fin.sum_univ_four, sigmaPlusBlockMat, bivBasis, bivBlockPair, cl44Bivector,
        cl44Gen, gamma44, projPlus, reflPsiPlus, psiPlusProj];
      simp;
      simp only [cl11One_eq_P0_add_P1, cl11Grad_eq_P0_sub_P1, cl11Pos_eq_Up_add_Down,
        cl11Neg_eq_Down_sub_Up, tensor4_add_0, tensor4_add_1, tensor4_add_2, tensor4_add_3,
        tensor4_sub_0, tensor4_sub_1, tensor4_sub_2, tensor4_sub_3];
      module)

private lemma sigmaPlusLin_rhoPlus_b6 (k : Fin 4) :
    projPlus * ∑ j : Fin 4, sigmaPlusBlockMat 6 j k • bivBasis (6, j) =
      reflPsiPlus * (projPlus * bivBasis (6, k)) * reflPsiPlus := by
  fin_cases k <;>
    (simp only [Fin.sum_univ_four, sigmaPlusBlockMat, bivBasis, bivBlockPair, cl44Bivector,
        cl44Gen, gamma44, projPlus, reflPsiPlus, psiPlusProj];
      simp;
      simp only [cl11One_eq_P0_add_P1, cl11Grad_eq_P0_sub_P1, cl11Pos_eq_Up_add_Down,
        cl11Neg_eq_Down_sub_Up, tensor4_add_0, tensor4_add_1, tensor4_add_2, tensor4_add_3,
        tensor4_sub_0, tensor4_sub_1, tensor4_sub_2, tensor4_sub_3];
      module)

private lemma sigmaPlusLin_rhoPlus_basis (i : Fin 7) (k : Fin 4) :
    projPlus * (sigmaPlusLin (bivBasisObj (i, k)) : Matrix Krein16Idx Krein16Idx ℝ) =
      reflPsiPlus * (projPlus * bivBasis (i, k)) * reflPsiPlus := by
  rw [sigmaPlusLin_basis i k]
  fin_cases i
  · exact sigmaPlusLin_rhoPlus_b0 k
  · exact sigmaPlusLin_rhoPlus_b1 k
  · exact sigmaPlusLin_rhoPlus_b2 k
  · exact sigmaPlusLin_rhoPlus_b3 k
  · exact sigmaPlusLin_rhoPlus_b4 k
  · exact sigmaPlusLin_rhoPlus_b5 k
  · exact sigmaPlusLin_rhoPlus_b6 k

end MatrixUnitExpandLocal

private lemma sigmaPlusLin_rhoPlus (B : cl44BivectorSpan) :
    projPlus * (sigmaPlusLin B : Matrix Krein16Idx Krein16Idx ℝ) =
      reflPsiPlus * (projPlus * B.1) * reflPsiPlus := by
  have hspan : B ∈ Submodule.span ℝ (Set.range bivBasisObj) := by
    rw [bivBasisObj.span_eq]
    exact Submodule.mem_top
  refine Submodule.span_induction (hx := hspan) ?_ ?_ ?_ ?_
  · rintro _ ⟨⟨i, k⟩, rfl⟩
    simpa [bivBasisObj_apply] using sigmaPlusLin_rhoPlus_basis i k
  · simp [map_zero]
  · intro X Y _ _ hX hY
    simp only [map_add, Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, hX, hY]
  · intro r X _ hX
    simp only [map_smul, SetLike.val_smul, Matrix.mul_smul, Matrix.smul_mul, hX]

private lemma sigmaPlusLin_involutive (B : cl44BivectorSpan) :
    sigmaPlusLin (sigmaPlusLin B) = B := by
  have hsq : ∀ i : Fin 7, ∀ a c : Fin 4,
      (∑ b : Fin 4, sigmaPlusBlockMat i a b * sigmaPlusBlockMat i b c) =
        if a = c then 1 else 0 := by
    intro i a c
    fin_cases i <;> fin_cases a <;> fin_cases c <;>
      simp [Fin.sum_univ_four, sigmaPlusBlockMat] <;> norm_num
  have hbasis : ∀ p : Fin 7 × Fin 4,
      sigmaPlusLin (sigmaPlusLin (bivBasisObj p)) = bivBasisObj p := by
    rintro ⟨i, k⟩
    change sigmaPlusLin (bivBasisObj.constr ℝ (fun p =>
        ∑ j : Fin 4, sigmaPlusBlockMat p.1 j p.2 • bivBasisObj (p.1, j)) (bivBasisObj (i, k))) =
      bivBasisObj (i, k)
    rw [Module.Basis.constr_basis, map_sum]
    simp_rw [map_smul]
    have hinner : ∀ j : Fin 4,
        sigmaPlusLin (bivBasisObj (i, j)) =
          ∑ a : Fin 4, sigmaPlusBlockMat i a j • bivBasisObj (i, a) := by
      intro j
      unfold sigmaPlusLin
      rw [Module.Basis.constr_basis]
    simp_rw [hinner, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have hre : (∑ a : Fin 4, ∑ j : Fin 4,
        (sigmaPlusBlockMat i j k * sigmaPlusBlockMat i a j) • bivBasisObj (i, a)) =
        ∑ a : Fin 4,
          (∑ j : Fin 4, sigmaPlusBlockMat i a j * sigmaPlusBlockMat i j k) •
            bivBasisObj (i, a) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
    rw [hre]
    simp_rw [hsq i _ k]
    simp
  have hspan : B ∈ Submodule.span ℝ (Set.range bivBasisObj) := by
    rw [bivBasisObj.span_eq]
    exact Submodule.mem_top
  refine Submodule.span_induction (hx := hspan) ?_ ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩
    exact hbasis p
  · simp
  · intro X Y _ _ hX hY
    rw [map_add, map_add, hX, hY]
  · intro r X _ hX
    rw [map_smul, map_smul, hX]

private noncomputable def trialitySigmaPlus :
    cl44BivectorLieSubalgebra ≃ₗ⁅ℝ⁆ cl44BivectorLieSubalgebra :=
  let f : cl44BivectorLieSubalgebra →ₗ⁅ℝ⁆ cl44BivectorLieSubalgebra :=
    { toFun := fun B => ⟨(sigmaPlusLin ⟨B.1, B.2⟩).1, (sigmaPlusLin ⟨B.1, B.2⟩).2⟩
      map_add' := fun A B => by
        apply Subtype.ext
        change (sigmaPlusLin (⟨A.1, A.2⟩ + ⟨B.1, B.2⟩) : Matrix Krein16Idx Krein16Idx ℝ) =
          (sigmaPlusLin ⟨A.1, A.2⟩).1 + (sigmaPlusLin ⟨B.1, B.2⟩).1
        rw [map_add]
        rfl
      map_smul' := fun r A => by
        apply Subtype.ext
        change (sigmaPlusLin (r • (⟨A.1, A.2⟩ : cl44BivectorSpan)) :
            Matrix Krein16Idx Krein16Idx ℝ) = r • (sigmaPlusLin ⟨A.1, A.2⟩).1
        rw [map_smul]
        rfl
      map_lie' := fun {A B} => by
        apply rhoPlus_injective
        rw [LieHom.map_lie]
        change projPlus * (sigmaPlusLin ⟨A.1 * B.1 - B.1 * A.1, ⁅A, B⁆.2⟩).1 =
          (projPlus * (sigmaPlusLin ⟨A.1, A.2⟩).1) * (projPlus * (sigmaPlusLin ⟨B.1, B.2⟩).1) -
          (projPlus * (sigmaPlusLin ⟨B.1, B.2⟩).1) * (projPlus * (sigmaPlusLin ⟨A.1, A.2⟩).1)
        have hAB : (⟨A.1 * B.1 - B.1 * A.1, ⁅A, B⁆.2⟩ : cl44BivectorSpan) =
            ⟨⁅A, B⁆.1, ⁅A, B⁆.2⟩ := rfl
        rw [hAB, sigmaPlusLin_rhoPlus ⟨⁅A, B⁆.1, ⁅A, B⁆.2⟩,
          sigmaPlusLin_rhoPlus ⟨A.1, A.2⟩, sigmaPlusLin_rhoPlus ⟨B.1, B.2⟩]
        change reflPsiPlus * (projPlus * (A.1 * B.1 - B.1 * A.1)) * reflPsiPlus = _
        have hlie : projPlus * (A.1 * B.1 - B.1 * A.1) =
            rhoPlus A * rhoPlus B - rhoPlus B * rhoPlus A :=
          LieHom.map_lie rhoPlus A B
        rw [hlie]
        change reflPsiPlus * (rhoPlus A * rhoPlus B - rhoPlus B * rhoPlus A) * reflPsiPlus =
          (reflPsiPlus * rhoPlus A * reflPsiPlus) * (reflPsiPlus * rhoPlus B * reflPsiPlus) -
          (reflPsiPlus * rhoPlus B * reflPsiPlus) * (reflPsiPlus * rhoPlus A * reflPsiPlus)
        have h1 : (reflPsiPlus * rhoPlus A * reflPsiPlus) *
            (reflPsiPlus * rhoPlus B * reflPsiPlus) =
            reflPsiPlus * (rhoPlus A * rhoPlus B) * reflPsiPlus := by
          calc
            (reflPsiPlus * rhoPlus A * reflPsiPlus) *
                (reflPsiPlus * rhoPlus B * reflPsiPlus)
                = reflPsiPlus * rhoPlus A * (reflPsiPlus * reflPsiPlus) *
                    rhoPlus B * reflPsiPlus := by simp only [Matrix.mul_assoc]
            _ = reflPsiPlus * (rhoPlus A * rhoPlus B) * reflPsiPlus := by
                  rw [reflPsiPlus_sq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        have h2 : (reflPsiPlus * rhoPlus B * reflPsiPlus) *
            (reflPsiPlus * rhoPlus A * reflPsiPlus) =
            reflPsiPlus * (rhoPlus B * rhoPlus A) * reflPsiPlus := by
          calc
            (reflPsiPlus * rhoPlus B * reflPsiPlus) *
                (reflPsiPlus * rhoPlus A * reflPsiPlus)
                = reflPsiPlus * rhoPlus B * (reflPsiPlus * reflPsiPlus) *
                    rhoPlus A * reflPsiPlus := by simp only [Matrix.mul_assoc]
            _ = reflPsiPlus * (rhoPlus B * rhoPlus A) * reflPsiPlus := by
                  rw [reflPsiPlus_sq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        rw [h1, h2, Matrix.mul_sub, Matrix.sub_mul] }
  have hinv : Function.LeftInverse f f := fun B => by
    apply Subtype.ext
    change (sigmaPlusLin (sigmaPlusLin ⟨B.1, B.2⟩)).1 = B.1
    rw [sigmaPlusLin_involutive]
  { f with
    invFun := f
    left_inv := hinv
    right_inv := hinv }

/-- Order-3 Cartan triality automorphism `τ = σ ∘ σ₊` on `cl44BivectorLieSubalgebra`. -/
noncomputable def trialityTau3 :
    cl44BivectorLieSubalgebra ≃ₗ⁅ℝ⁆ cl44BivectorLieSubalgebra :=
  trialitySigmaPlus.trans trialitySigma3

private def bivBasisLie (p : Fin 7 × Fin 4) : cl44BivectorLieSubalgebra :=
  ⟨(bivBasisObj p).1, (bivBasisObj p).2⟩

private lemma trialitySigma3_bivBasis (i : Fin 7) (k : Fin 4) :
    trialitySigma3 (bivBasisLie (i, k)) =
      (if k = 0 then (-1 : ℝ) else 1) • bivBasisLie (i, k) := by
  apply Subtype.ext
  have hk0 : (k = 0) ↔ ((bivBlockPair i k).1 = 0) := by
    fin_cases i <;> fin_cases k <;> decide
  have hk0b : (bivBlockPair i k).2 ≠ 0 := by
    fin_cases i <;> fin_cases k <;> decide
  change cl44Gen 0 * (bivBasisLie (i, k)).1 * cl44Gen 0 =
    (if k = 0 then (-1 : ℝ) else 1) • (bivBasisLie (i, k)).1
  have hb : (bivBasisLie (i, k)).1 = bivBasis (i, k) := bivBasisObj_apply (i, k)
  rw [hb]
  by_cases hk : k = 0
  · subst hk
    have ha : (bivBlockPair i 0).1 = 0 := hk0.mp rfl
    have hanti := eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hk0b.symm)
    have hEq : cl44Gen 0 * cl44Bivector 0 (bivBlockPair i 0).2 * cl44Gen 0 =
        -cl44Bivector 0 (bivBlockPair i 0).2 := by
      unfold cl44Bivector
      calc
        cl44Gen 0 * (cl44Gen 0 * cl44Gen (bivBlockPair i 0).2) * cl44Gen 0
            = (cl44Gen 0 * cl44Gen 0) * (cl44Gen (bivBlockPair i 0).2 * cl44Gen 0) := by
                simp only [Matrix.mul_assoc]
        _ = 1 * (-(cl44Gen 0 * cl44Gen (bivBlockPair i 0).2)) := by
                rw [cl44Gen_sq 0, hanti]; simp
        _ = -(cl44Gen 0 * cl44Gen (bivBlockPair i 0).2) := Matrix.one_mul _
    unfold bivBasis
    rw [ha, hEq]
    simp
  · have ha : (bivBlockPair i k).1 ≠ 0 := fun h => hk (hk0.mpr h)
    have ha' : cl44Gen 0 * cl44Gen (bivBlockPair i k).1 =
        -(cl44Gen (bivBlockPair i k).1 * cl44Gen 0) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm ha)
    have hb' : cl44Gen 0 * cl44Gen (bivBlockPair i k).2 =
        -(cl44Gen (bivBlockPair i k).2 * cl44Gen 0) :=
      eq_neg_of_add_eq_zero_right (cl44Gen_anticomm hk0b)
    have hEq : cl44Gen 0 * cl44Bivector (bivBlockPair i k).1 (bivBlockPair i k).2 * cl44Gen 0 =
        cl44Bivector (bivBlockPair i k).1 (bivBlockPair i k).2 := by
      unfold cl44Bivector
      calc
        cl44Gen 0 * (cl44Gen (bivBlockPair i k).1 * cl44Gen (bivBlockPair i k).2) * cl44Gen 0
            = (cl44Gen 0 * cl44Gen (bivBlockPair i k).1) *
                cl44Gen (bivBlockPair i k).2 * cl44Gen 0 := by simp only [Matrix.mul_assoc]
        _ = (-(cl44Gen (bivBlockPair i k).1 * cl44Gen 0)) *
              cl44Gen (bivBlockPair i k).2 * cl44Gen 0 := by rw [ha']
        _ = -(cl44Gen (bivBlockPair i k).1 *
              ((cl44Gen 0 * cl44Gen (bivBlockPair i k).2) * cl44Gen 0)) := by
                simp only [Matrix.neg_mul, Matrix.mul_assoc]
        _ = -(cl44Gen (bivBlockPair i k).1 *
              ((-(cl44Gen (bivBlockPair i k).2 * cl44Gen 0)) * cl44Gen 0)) := by rw [hb']
        _ = cl44Gen (bivBlockPair i k).1 *
              (cl44Gen (bivBlockPair i k).2 * (cl44Gen 0 * cl44Gen 0)) := by
                simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
        _ = cl44Gen (bivBlockPair i k).1 * cl44Gen (bivBlockPair i k).2 := by
                rw [cl44Gen_sq 0]; simp
    unfold bivBasis
    rw [hEq]
    simp [hk]

private def tauBlkMat (i : Fin 7) (a b : Fin 4) : ℝ :=
  (if a = 0 then (-1 : ℝ) else 1) * sigmaPlusBlockMat i a b

private lemma tauBlk_cube_b0 (a d : Fin 4) :
    (∑ b : Fin 4, ∑ c : Fin 4, tauBlkMat 0 a b * tauBlkMat 0 b c * tauBlkMat 0 c d) =
      if a = d then 1 else 0 := by
  fin_cases a <;> fin_cases d <;>
    (simp [Fin.sum_univ_four, tauBlkMat, sigmaPlusBlockMat]; try norm_num)

private lemma tauBlk_cube_b1 (a d : Fin 4) :
    (∑ b : Fin 4, ∑ c : Fin 4, tauBlkMat 1 a b * tauBlkMat 1 b c * tauBlkMat 1 c d) =
      if a = d then 1 else 0 := by
  fin_cases a <;> fin_cases d <;>
    (simp [Fin.sum_univ_four, tauBlkMat, sigmaPlusBlockMat]; try norm_num)

private lemma tauBlk_cube_b2 (a d : Fin 4) :
    (∑ b : Fin 4, ∑ c : Fin 4, tauBlkMat 2 a b * tauBlkMat 2 b c * tauBlkMat 2 c d) =
      if a = d then 1 else 0 := by
  fin_cases a <;> fin_cases d <;>
    (simp [Fin.sum_univ_four, tauBlkMat, sigmaPlusBlockMat]; try norm_num)

private lemma tauBlk_cube_b3 (a d : Fin 4) :
    (∑ b : Fin 4, ∑ c : Fin 4, tauBlkMat 3 a b * tauBlkMat 3 b c * tauBlkMat 3 c d) =
      if a = d then 1 else 0 := by
  fin_cases a <;> fin_cases d <;>
    (simp [Fin.sum_univ_four, tauBlkMat, sigmaPlusBlockMat]; try norm_num)

private lemma tauBlk_cube_b4 (a d : Fin 4) :
    (∑ b : Fin 4, ∑ c : Fin 4, tauBlkMat 4 a b * tauBlkMat 4 b c * tauBlkMat 4 c d) =
      if a = d then 1 else 0 := by
  fin_cases a <;> fin_cases d <;>
    (simp [Fin.sum_univ_four, tauBlkMat, sigmaPlusBlockMat]; try norm_num)

private lemma tauBlk_cube_b5 (a d : Fin 4) :
    (∑ b : Fin 4, ∑ c : Fin 4, tauBlkMat 5 a b * tauBlkMat 5 b c * tauBlkMat 5 c d) =
      if a = d then 1 else 0 := by
  fin_cases a <;> fin_cases d <;>
    (simp [Fin.sum_univ_four, tauBlkMat, sigmaPlusBlockMat]; try norm_num)

private lemma tauBlk_cube_b6 (a d : Fin 4) :
    (∑ b : Fin 4, ∑ c : Fin 4, tauBlkMat 6 a b * tauBlkMat 6 b c * tauBlkMat 6 c d) =
      if a = d then 1 else 0 := by
  fin_cases a <;> fin_cases d <;>
    (simp [Fin.sum_univ_four, tauBlkMat, sigmaPlusBlockMat]; try norm_num)

private lemma trialityTau3_order3_basis (i : Fin 7) (k : Fin 4) :
    trialityTau3 (trialityTau3 (trialityTau3 (bivBasisLie (i, k)))) = bivBasisLie (i, k) := by
  have htau_apply : ∀ j : Fin 4,
      trialityTau3 (bivBasisLie (i, j)) = ∑ a : Fin 4, tauBlkMat i a j • bivBasisLie (i, a) := by
    intro j
    change trialitySigma3 (trialitySigmaPlus (bivBasisLie (i, j))) = _
    have hsp : trialitySigmaPlus (bivBasisLie (i, j)) =
        ∑ a : Fin 4, sigmaPlusBlockMat i a j • bivBasisLie (i, a) := by
      apply Subtype.ext
      change (sigmaPlusLin (bivBasisObj (i, j)) : Matrix Krein16Idx Krein16Idx ℝ) =
        ∑ a : Fin 4, sigmaPlusBlockMat i a j • (bivBasisLie (i, a)).1
      dsimp [bivBasisLie]
      simp_rw [bivBasisObj_apply]
      exact sigmaPlusLin_basis i j
    rw [hsp, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, trialitySigma3_bivBasis i a, smul_smul, mul_comm]
    dsimp [tauBlkMat]
  have htau_vec : ∀ v : Fin 4 → ℝ,
      trialityTau3 (∑ a : Fin 4, v a • bivBasisLie (i, a)) =
        ∑ b : Fin 4, (∑ a : Fin 4, tauBlkMat i b a * v a) • bivBasisLie (i, b) := by
    intro v
    rw [map_sum]
    simp_rw [map_smul, htau_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  have hcube : ∀ a d : Fin 4,
      (∑ b : Fin 4, ∑ c : Fin 4, tauBlkMat i a b * tauBlkMat i b c * tauBlkMat i c d) =
        if a = d then 1 else 0 := by
    intro a d
    fin_cases i
    · exact tauBlk_cube_b0 a d
    · exact tauBlk_cube_b1 a d
    · exact tauBlk_cube_b2 a d
    · exact tauBlk_cube_b3 a d
    · exact tauBlk_cube_b4 a d
    · exact tauBlk_cube_b5 a d
    · exact tauBlk_cube_b6 a d
  rw [htau_apply k, htau_vec, htau_vec]
  have hcoeff : ∀ a : Fin 4,
      (∑ c : Fin 4, tauBlkMat i a c * ∑ b : Fin 4, tauBlkMat i c b * tauBlkMat i b k) =
        if a = k then 1 else 0 := by
    intro a
    simp_rw [Finset.mul_sum, ← mul_assoc]
    exact hcube a k
  simp_rw [hcoeff]
  simp

/-- Intrinsic `S₃` outer triality relations on `cl44BivectorLieSubalgebra`:
`σ² = 1`, `τ³ = 1`, `τ ≠ 1`, and `σ τ σ = τ²`. -/
lemma triality_s3_relations :
    trialitySigma3.trans trialitySigma3 = LieEquiv.refl ∧
    (trialityTau3.trans (trialityTau3.trans trialityTau3)) = LieEquiv.refl ∧
    trialityTau3 ≠ LieEquiv.refl ∧
    trialitySigma3.trans (trialityTau3.trans trialitySigma3) =
      trialityTau3.trans trialityTau3 := by
  have hsig2 : trialitySigma3.trans trialitySigma3 = LieEquiv.refl := by
    apply LieEquiv.ext
    intro B
    exact trialitySigma3.left_inv B
  have hsig_apply : ∀ B, trialitySigma3 (trialitySigma3 B) = B :=
    fun B => trialitySigma3.left_inv B
  have hsp_apply : ∀ B, trialitySigmaPlus (trialitySigmaPlus B) = B :=
    fun B => trialitySigmaPlus.left_inv B
  have htau3 : (trialityTau3.trans (trialityTau3.trans trialityTau3)) = LieEquiv.refl := by
    apply LieEquiv.ext
    intro B
    apply Subtype.ext
    change (trialityTau3 (trialityTau3 (trialityTau3 B))).1 = B.1
    have hgen : ∀ X : cl44BivectorSpan,
        (trialityTau3 (trialityTau3 (trialityTau3 ⟨X.1, X.2⟩))).1 = X.1 := by
      intro X
      have hXs : X ∈ Submodule.span ℝ (Set.range bivBasisObj) := by
        rw [bivBasisObj.span_eq]
        exact Submodule.mem_top
      refine Submodule.span_induction (hx := hXs) ?_ ?_ ?_ ?_
      · rintro _ ⟨⟨i, k⟩, rfl⟩
        exact congrArg Subtype.val (trialityTau3_order3_basis i k)
      · change (trialityTau3 (trialityTau3 (trialityTau3 (0 : cl44BivectorLieSubalgebra)))).1 =
          (0 : cl44BivectorSpan).1
        rw [map_zero, map_zero, map_zero]
        rfl
      · intro U V _ _ hU hV
        have hsum : (⟨(U + V).1, (U + V).2⟩ : cl44BivectorLieSubalgebra) =
            ⟨U.1, U.2⟩ + ⟨V.1, V.2⟩ := rfl
        rw [hsum, map_add, map_add, map_add]
        change (trialityTau3 (trialityTau3 (trialityTau3 ⟨U.1, U.2⟩))).1 +
          (trialityTau3 (trialityTau3 (trialityTau3 ⟨V.1, V.2⟩))).1 = U.1 + V.1
        rw [hU, hV]
      · intro r U _ hU
        have hsm : (⟨(r • U).1, (r • U).2⟩ : cl44BivectorLieSubalgebra) =
            r • (⟨U.1, U.2⟩ : cl44BivectorLieSubalgebra) := rfl
        rw [hsm, map_smul, map_smul, map_smul]
        change r • (trialityTau3 (trialityTau3 (trialityTau3 ⟨U.1, U.2⟩))).1 = r • U.1
        rw [hU]
    exact hgen ⟨B.1, B.2⟩
  have htau3_apply : ∀ B, trialityTau3 (trialityTau3 (trialityTau3 B)) = B := by
    intro B
    have h := congrArg (fun f : cl44BivectorLieSubalgebra ≃ₗ⁅ℝ⁆ cl44BivectorLieSubalgebra =>
      f B) htau3
    change trialityTau3 (trialityTau3 (trialityTau3 B)) = B at h
    exact h
  have htau_ne : trialityTau3 ≠ LieEquiv.refl := by
    intro h
    have hv := congrArg (fun f : cl44BivectorLieSubalgebra ≃ₗ⁅ℝ⁆ cl44BivectorLieSubalgebra =>
      Matrix.trace ((f (bivBasisLie (0, 0))).1 * bivBasis (0, 0))) h
    have hlhs : trialityTau3 (bivBasisLie (0, 0)) =
        ∑ a : Fin 4, ((if a = 0 then (-1 : ℝ) else 1) * sigmaPlusBlockMat 0 a 0) •
          bivBasisLie (0, a) := by
      change trialitySigma3 (trialitySigmaPlus (bivBasisLie (0, 0))) = _
      have hsp : trialitySigmaPlus (bivBasisLie (0, 0)) =
          ∑ a : Fin 4, sigmaPlusBlockMat 0 a 0 • bivBasisLie (0, a) := by
        apply Subtype.ext
        change (sigmaPlusLin (bivBasisObj (0, 0)) : Matrix Krein16Idx Krein16Idx ℝ) =
          ∑ a : Fin 4, sigmaPlusBlockMat 0 a 0 • (bivBasisLie (0, a)).1
        dsimp [bivBasisLie]
        simp_rw [bivBasisObj_apply]
        exact sigmaPlusLin_basis 0 0
      rw [hsp, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, trialitySigma3_bivBasis 0 a, smul_smul, mul_comm]
    have hleft_tr : Matrix.trace ((trialityTau3 (bivBasisLie (0, 0))).1 * bivBasis (0, 0)) = 8 := by
      have hval : (trialityTau3 (bivBasisLie (0, 0))).1 =
          ∑ a : Fin 4, ((if a = 0 then (-1 : ℝ) else 1) * sigmaPlusBlockMat 0 a 0) •
            bivBasis (0, a) := by
        rw [hlhs, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [SetLike.val_smul]
        dsimp [bivBasisLie]
        rw [bivBasisObj_apply]
      rw [hval, Matrix.sum_mul, Matrix.trace_sum]
      simp_rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_bivBasis_mul]
      simp [sigmaPlusBlockMat, bivBlockPair]
      norm_num
    have hright_tr :
        Matrix.trace (((LieEquiv.refl :
          cl44BivectorLieSubalgebra ≃ₗ⁅ℝ⁆ cl44BivectorLieSubalgebra)
            (bivBasisLie (0, 0))).1 * bivBasis (0, 0)) = -16 := by
      change Matrix.trace ((bivBasisLie (0, 0)).1 * bivBasis (0, 0)) = -16
      dsimp [bivBasisLie]
      rw [bivBasisObj_apply, trace_bivBasis_mul]
      simp [bivBlockPair]
    rw [hleft_tr, hright_tr] at hv
    norm_num at hv
  have hconj : trialitySigma3.trans (trialityTau3.trans trialitySigma3) =
      trialityTau3.trans trialityTau3 := by
    apply LieEquiv.ext
    intro B
    change trialitySigma3 (trialityTau3 (trialitySigma3 B)) = trialityTau3 (trialityTau3 B)
    exact trialityTau3.injective (by
      change trialityTau3 (trialitySigma3 (trialityTau3 (trialitySigma3 B))) =
        trialityTau3 (trialityTau3 (trialityTau3 B))
      rw [htau3_apply]
      change trialitySigma3 (trialitySigmaPlus (trialitySigma3 (trialitySigma3
        (trialitySigmaPlus (trialitySigma3 B))))) = B
      rw [hsig_apply, hsp_apply, hsig_apply])
  exact ⟨hsig2, htau3, htau_ne, hconj⟩

/-- Fixed Lie subalgebra of `cl44BivectorLieSubalgebra` under the `S₃` triality action. -/
def trialityFixedBivectorLieSubalgebra :
    LieSubalgebra ℝ cl44BivectorLieSubalgebra :=
  { toSubmodule :=
      { carrier := {B | trialitySigma3 B = B ∧ trialityTau3 B = B}
        add_mem' := by
          rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
          exact ⟨by rw [map_add, hA1, hB1], by rw [map_add, hA2, hB2]⟩
        zero_mem' := ⟨map_zero _, map_zero _⟩
        smul_mem' := by
          rintro c A ⟨hA1, hA2⟩
          exact ⟨by rw [map_smul, hA1], by rw [map_smul, hA2]⟩ }
    lie_mem' := by
      rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
      exact ⟨by rw [LieEquiv.map_lie, hA1, hB1], by rw [LieEquiv.map_lie, hA2, hB2]⟩ }

private lemma cl11P0_eq_ket (a b : Fin 2) : cl11P0 a b = ket0 a * ket0 b := by
  fin_cases a <;> fin_cases b <;> simp [cl11P0, ket0]

private lemma cl11Up_eq_ket (a b : Fin 2) : cl11Up a b = ket0 a * ket1 b := by
  fin_cases a <;> fin_cases b <;> simp [cl11Up, ket0, ket1]

private lemma cl11Down_eq_ket (a b : Fin 2) : cl11Down a b = ket1 a * ket0 b := by
  fin_cases a <;> fin_cases b <;> simp [cl11Down, ket0, ket1]

private lemma cl11P1_eq_ket (a b : Fin 2) : cl11P1 a b = ket1 a * ket1 b := by
  fin_cases a <;> fin_cases b <;> simp [cl11P1, ket1]

private lemma psiPlusProj_entry (k j : Krein16Idx) :
    psiPlusProj k j = majoranaRefSpinor k * (kreinMetric88.mulVec majoranaRefSpinor) j := by
  have hkrein : kreinMetric88.mulVec majoranaRefSpinor =
      vec4 ket1 ket1 ket1 ket1 + vec4 ket0 ket0 ket0 ket0 := by
    unfold majoranaRefSpinor kreinMetric88
    rw [Matrix.mulVec_add, tensor4_mulVec, tensor4_mulVec,
      cl11Pos_mulVec_ket0, cl11Neg_mulVec_ket0, cl11Pos_mulVec_ket1, cl11Neg_mulVec_ket1,
      vec4_neg_1, vec4_neg_3, neg_neg]
  rw [hkrein]
  simp only [psiPlusProj, majoranaRefSpinor, Matrix.add_apply, Pi.add_apply, tensor4, vec4,
    cl11P0_eq_ket, cl11Up_eq_ket, cl11Down_eq_ket, cl11P1_eq_ket]
  ring

private lemma psiPlusProj_comm_kreinMetric88 :
    kreinMetric88 * psiPlusProj = psiPlusProj * kreinMetric88 := by
  unfold psiPlusProj kreinMetric88
  simp [Matrix.add_mul, Matrix.mul_add, tensor4_mul,
    tensor4_neg_1, tensor4_neg_3,
    cl11Pos_mul_cl11P0, cl11P0_mul_cl11Pos,
    cl11Neg_mul_cl11P0, cl11P0_mul_cl11Neg, cl11Pos_mul_cl11Up, cl11Up_mul_cl11Pos,
    cl11Neg_mul_cl11Up, cl11Up_mul_cl11Neg, cl11Pos_mul_cl11Down, cl11Down_mul_cl11Pos,
    cl11Neg_mul_cl11Down, cl11Down_mul_cl11Neg, cl11Pos_mul_cl11P1, cl11P1_mul_cl11Pos,
    cl11Neg_mul_cl11P1, cl11P1_mul_cl11Neg]
  abel

private lemma g2_mem_trialityFixed (Z : g2LieSubalgebra) :
    g2IntoCl44BivectorLieHom Z ∈ trialityFixedBivectorLieSubalgebra := by
  have hstab := g2Submodule_mem_stabilizer Z.2
  have hsig : trialitySigma3 (g2IntoCl44BivectorLieHom Z) = g2IntoCl44BivectorLieHom Z := by
    apply Subtype.ext
    change cl44Gen 0 * Z.1 * cl44Gen 0 = Z.1
    have hsq0 : cl44Gen 0 * cl44Gen 0 = 1 := by rw [cl44Gen_sq 0]; simp
    rw [← hstab.2.2.1, Matrix.mul_assoc, hsq0, Matrix.mul_one]
  have hsp : trialitySigmaPlus (g2IntoCl44BivectorLieHom Z) = g2IntoCl44BivectorLieHom Z := by
    apply rhoPlus_injective
    change projPlus * (sigmaPlusLin ⟨(g2IntoCl44BivectorLieHom Z).1,
        (g2IntoCl44BivectorLieHom Z).2⟩).1 =
      projPlus * (g2IntoCl44BivectorLieHom Z).1
    rw [sigmaPlusLin_rhoPlus ⟨(g2IntoCl44BivectorLieHom Z).1, (g2IntoCl44BivectorLieHom Z).2⟩]
    have hZpsi : Z.1 * psiPlusProj = 0 := by
      ext i j
      simp only [Matrix.mul_apply, psiPlusProj_entry, Matrix.zero_apply]
      have hsum : (∑ k : Krein16Idx, Z.1 i k *
          (majoranaRefSpinor k * (kreinMetric88.mulVec majoranaRefSpinor) j)) =
          (Z.1.mulVec majoranaRefSpinor i) * (kreinMetric88.mulVec majoranaRefSpinor) j := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
      rw [hsum, hstab.2.2.2, Pi.zero_apply, zero_mul]
    have hpsiZ : psiPlusProj * Z.1 = 0 := by
      have hpsi_sym : psiPlusProjᵀ = psiPlusProj := by
        unfold psiPlusProj
        rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_add,
          tensor4_transpose, tensor4_transpose, tensor4_transpose, tensor4_transpose,
          cl11P0_transpose, cl11Up_transpose, cl11Down_transpose, cl11P1_transpose]
        abel
      have hZeta : Z.1ᵀ * kreinMetric88 = -(kreinMetric88 * Z.1) :=
        eq_neg_of_add_eq_zero_left hstab.1
      have hT : (psiPlusProj * Z.1)ᵀ = -(kreinMetric88 * (Z.1 * psiPlusProj) * kreinMetric88) := by
        calc
          (psiPlusProj * Z.1)ᵀ = Z.1ᵀ * psiPlusProj := by rw [Matrix.transpose_mul, hpsi_sym]
          _ = Z.1ᵀ * (kreinMetric88 * kreinMetric88) * psiPlusProj := by
                rw [kreinMetric88_properties.2.2.1, Matrix.mul_one]
          _ = (Z.1ᵀ * kreinMetric88) * (kreinMetric88 * psiPlusProj) := by
                simp only [Matrix.mul_assoc]
          _ = (-(kreinMetric88 * Z.1)) * (psiPlusProj * kreinMetric88) := by
                rw [hZeta, psiPlusProj_comm_kreinMetric88]
          _ = -(kreinMetric88 * (Z.1 * psiPlusProj) * kreinMetric88) := by
                simp only [Matrix.neg_mul, Matrix.mul_assoc]
      have hT0 : (psiPlusProj * Z.1)ᵀ = 0 := by rw [hT, hZpsi, Matrix.mul_zero,
        Matrix.zero_mul, neg_zero]
      have := congrArg Matrix.transpose hT0
      simpa using this
    change reflPsiPlus * (projPlus * Z.1) * reflPsiPlus = projPlus * Z.1
    have hcomm : projPlus * Z.1 = Z.1 * projPlus := (bivectorSpan_comm_projPlus
      (g2IntoCl44BivectorLieHom Z).2).symm
    have hreflZ : reflPsiPlus * Z.1 * reflPsiPlus = Z.1 := by
      unfold reflPsiPlus
      rw [Matrix.sub_mul, Matrix.one_mul, hpsiZ, sub_zero, Matrix.mul_sub,
        Matrix.mul_one, hZpsi, sub_zero]
    calc
      reflPsiPlus * (projPlus * Z.1) * reflPsiPlus
          = reflPsiPlus * (Z.1 * projPlus) * reflPsiPlus := by rw [hcomm]
      _ = reflPsiPlus * Z.1 * (projPlus * reflPsiPlus) := by simp only [Matrix.mul_assoc]
      _ = reflPsiPlus * Z.1 * (reflPsiPlus * projPlus) := by rw [reflPsiPlus_comm_projPlus]
      _ = (reflPsiPlus * Z.1 * reflPsiPlus) * projPlus := by simp only [Matrix.mul_assoc]
      _ = Z.1 * projPlus := by rw [hreflZ]
      _ = projPlus * Z.1 := hcomm.symm
  have htau : trialityTau3 (g2IntoCl44BivectorLieHom Z) = g2IntoCl44BivectorLieHom Z := by
    change trialitySigma3 (trialitySigmaPlus (g2IntoCl44BivectorLieHom Z)) =
      g2IntoCl44BivectorLieHom Z
    rw [hsp, hsig]
  exact ⟨hsig, htau⟩

private noncomputable def g2ToTrialityFixedLieHom :
    g2LieSubalgebra →ₗ⁅ℝ⁆ trialityFixedBivectorLieSubalgebra where
  toFun Z := ⟨g2IntoCl44BivectorLieHom Z, g2_mem_trialityFixed Z⟩
  map_add' A B := by apply Subtype.ext; exact map_add g2IntoCl44BivectorLieHom A B
  map_smul' r A := by apply Subtype.ext; exact map_smul g2IntoCl44BivectorLieHom r A
  map_lie' {A B} := by apply Subtype.ext; exact LieHom.map_lie g2IntoCl44BivectorLieHom A B

private lemma g2ToTrialityFixedLieHom_injective :
    Function.Injective g2ToTrialityFixedLieHom := by
  intro A B h
  apply g2IntoCl44BivectorLieHom_injective
  exact congrArg Subtype.val h

/-- Dimension of the `S₃`-triality-fixed subalgebra of `cl44BivectorLieSubalgebra` is `14`. -/
lemma finrank_trialityFixedBivectorLieSubalgebra :
    Module.finrank ℝ trialityFixedBivectorLieSubalgebra = 14 := by
  have hlower : 14 ≤ Module.finrank ℝ trialityFixedBivectorLieSubalgebra := by
    rw [← finrank_g2LieSubalgebra]
    exact LinearMap.finrank_le_finrank_of_injective g2ToTrialityFixedLieHom_injective
  let proj14 : trialityFixedBivectorLieSubalgebra →ₗ[ℝ] (Fin 7 × Fin 2 → ℝ) :=
    { toFun := fun B p =>
        Matrix.trace (B.1.1 * bivBasis (p.1, if p.2 = 0 then 1 else 2))
      map_add' := fun A B => by
        funext p
        simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun r A => by
        funext p
        rw [SetLike.val_smul, SetLike.val_smul, Matrix.smul_mul, Matrix.trace_smul]
        rfl }
  have hproj_inj : Function.Injective proj14 := by
    rw [injective_iff_map_eq_zero]
    intro B hB
    have hM : B.1.1 ∈ Submodule.span ℝ (Set.range bivBasis) := by
      rw [span_bivBasis_eq_cl44BivectorSpan]
      exact B.1.2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hM
    have htr_c : ∀ i : Fin 7, ∀ k : Fin 4,
        Matrix.trace (B.1.1 * bivBasis (i, k)) =
          c (i, k) * (-16 * ((if (bivBlockPair i k).1.val < 4 then (1 : ℝ) else -1) *
            (if (bivBlockPair i k).2.val < 4 then (1 : ℝ) else -1))) := by
      intro i k
      rw [← hc, Matrix.sum_mul, Matrix.trace_sum]
      have hterm : ∀ q : Fin 7 × Fin 4,
          Matrix.trace ((c q • bivBasis q) * bivBasis (i, k)) =
            if q = (i, k) then c (i, k) * (-16 *
              ((if (bivBlockPair i k).1.val < 4 then (1 : ℝ) else -1) *
              (if (bivBlockPair i k).2.val < 4 then (1 : ℝ) else -1))) else 0 := by
        intro q
        rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_bivBasis_mul]
        by_cases hq : q = (i, k)
        · subst hq; simp
        · simp [hq]
      simp_rw [hterm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hdenom_ne : ∀ i : Fin 7, ∀ k : Fin 4,
        -16 * ((if (bivBlockPair i k).1.val < 4 then (1 : ℝ) else -1) *
          (if (bivBlockPair i k).2.val < 4 then (1 : ℝ) else -1)) ≠ 0 := by
      intro i k; split_ifs <;> norm_num
    have hc1 : ∀ i : Fin 7, c (i, 1) = 0 := by
      intro i
      have h0 : Matrix.trace (B.1.1 * bivBasis (i, 1)) = 0 := congrFun hB (i, 0)
      rw [htr_c i 1] at h0
      exact (mul_eq_zero.mp h0).resolve_right (hdenom_ne i 1)
    have hc2 : ∀ i : Fin 7, c (i, 2) = 0 := by
      intro i
      have h0 : Matrix.trace (B.1.1 * bivBasis (i, 2)) = 0 := congrFun hB (i, 1)
      rw [htr_c i 2] at h0
      exact (mul_eq_zero.mp h0).resolve_right (hdenom_ne i 2)
    have hsig : trialitySigma3 B.1 = B.1 := B.2.1
    have htau : trialityTau3 B.1 = B.1 := B.2.2
    have hsp : trialitySigmaPlus B.1 = B.1 := by
      have h := congrArg trialitySigma3 htau
      change trialitySigma3 (trialitySigma3 (trialitySigmaPlus B.1)) = trialitySigma3 B.1 at h
      have hinv : trialitySigma3 (trialitySigma3 (trialitySigmaPlus B.1)) =
          trialitySigmaPlus B.1 := trialitySigma3.left_inv _
      rw [hinv, hsig] at h
      exact h
    have hc0 : ∀ i : Fin 7, c (i, 0) = 0 := by
      intro i
      have heq := congrArg (fun X : cl44BivectorLieSubalgebra =>
        Matrix.trace (X.1 * bivBasis (i, 0))) hsig
      have hsig_tr : Matrix.trace ((trialitySigma3 B.1).1 * bivBasis (i, 0)) =
          -Matrix.trace (B.1.1 * bivBasis (i, 0)) := by
        have hconj0 : cl44Gen 0 * bivBasis (i, 0) * cl44Gen 0 = -bivBasis (i, 0) := by
          have hv := congrArg Subtype.val (trialitySigma3_bivBasis i 0)
          change cl44Gen 0 * (bivBasisLie (i, 0)).1 * cl44Gen 0 =
            ((if (0 : Fin 4) = 0 then (-1 : ℝ) else 1) • bivBasisLie (i, 0)).1 at hv
          dsimp [bivBasisLie] at hv
          rw [bivBasisObj_apply] at hv
          simpa using hv
        have he0sq : cl44Gen 0 * cl44Gen 0 = 1 := by rw [cl44Gen_sq 0]; simp
        calc
          Matrix.trace ((cl44Gen 0 * B.1.1 * cl44Gen 0) * bivBasis (i, 0))
              = Matrix.trace (B.1.1 * (cl44Gen 0 * bivBasis (i, 0) * cl44Gen 0)) := by
                  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm (cl44Gen 0)]
                  simp only [Matrix.mul_assoc]
          _ = Matrix.trace (B.1.1 * (-bivBasis (i, 0))) := by rw [hconj0]
          _ = -Matrix.trace (B.1.1 * bivBasis (i, 0)) := by
                rw [Matrix.mul_neg, Matrix.trace_neg]
      rw [hsig_tr] at heq
      have htr2 : (2 : ℝ) * Matrix.trace (B.1.1 * bivBasis (i, 0)) = 0 := by
        rw [two_mul]
        exact add_eq_zero_iff_neg_eq.mpr heq
      have htr0 : Matrix.trace (B.1.1 * bivBasis (i, 0)) = 0 :=
        (mul_eq_zero.mp htr2).resolve_left two_ne_zero
      rw [htr_c i 0] at htr0
      exact (mul_eq_zero.mp htr0).resolve_right (hdenom_ne i 0)
    have hc3 : ∀ i : Fin 7, c (i, 3) = 0 := by
      intro i
      have heq := congrArg (fun X : cl44BivectorLieSubalgebra =>
        Matrix.trace (X.1 * bivBasis (i, 0))) hsp
      have hBspan : (⟨B.1.1, B.1.2⟩ : cl44BivectorSpan) =
          ∑ p : Fin 7 × Fin 4, c p • bivBasisObj p := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simp_rw [SetLike.val_smul, bivBasisObj_apply]
        exact hc.symm
      have hsp_val : (trialitySigmaPlus B.1).1 =
          ∑ p : Fin 7 × Fin 4, ∑ j : Fin 4,
            (c p * sigmaPlusBlockMat p.1 j p.2) • bivBasis (p.1, j) := by
        change (sigmaPlusLin ⟨B.1.1, B.1.2⟩).1 = _
        rw [hBspan, map_sum, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [map_smul, SetLike.val_smul, sigmaPlusLin_basis p.1 p.2, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]
      rw [hsp_val, Matrix.sum_mul, Matrix.trace_sum] at heq
      simp_rw [Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
        smul_eq_mul, trace_bivBasis_mul] at heq
      have hlhs_eval : (∑ x : Fin 7 × Fin 4, ∑ j : Fin 4,
          (c x * sigmaPlusBlockMat x.1 j x.2) *
            (if (x.1, j) = (i, 0) then -16 *
              ((if (bivBlockPair x.1 j).1.val < 4 then (1 : ℝ) else -1) *
              (if (bivBlockPair x.1 j).2.val < 4 then (1 : ℝ) else -1)) else 0)) =
          (∑ k : Fin 4, c (i, k) * sigmaPlusBlockMat i 0 k) *
            (-16 * ((if (bivBlockPair i 0).1.val < 4 then (1 : ℝ) else -1) *
              (if (bivBlockPair i 0).2.val < 4 then (1 : ℝ) else -1))) := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
        · rw [Finset.sum_comm]
          rw [Finset.sum_eq_single 0]
          · simp [Finset.sum_mul]
          · intro j _ hj0
            refine Finset.sum_eq_zero fun k _ => ?_
            simp [hj0]
          · intro h0m
            exact absurd (Finset.mem_univ 0) h0m
        · intro i' _ hi'
          refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => ?_
          have hne : (i', j) ≠ (i, 0) := fun h => hi' (congrArg Prod.fst h)
          simp [hne]
        · intro him
          exact absurd (Finset.mem_univ i) him
      rw [hlhs_eval, htr_c i 0, hc0 i] at heq
      simp only [zero_mul] at heq
      have hcomb : (∑ k : Fin 4, c (i, k) * sigmaPlusBlockMat i 0 k) = 0 :=
        (mul_eq_zero.mp heq).resolve_right (hdenom_ne i 0)
      rw [Fin.sum_univ_four, hc0 i, hc1 i, hc2 i] at hcomb
      simp only [zero_mul, zero_add] at hcomb
      have hne : sigmaPlusBlockMat i 0 3 ≠ 0 := by
        fin_cases i <;> simp [sigmaPlusBlockMat]
      exact (mul_eq_zero.mp hcomb).resolve_right hne
    apply Subtype.ext
    apply Subtype.ext
    have hB0 : B.1.1 = 0 := by
      rw [← hc]
      refine Finset.sum_eq_zero fun p _ => ?_
      rcases p with ⟨i, k⟩
      fin_cases k
      · simp [hc0 i]
      · simp [hc1 i]
      · simp [hc2 i]
      · simp [hc3 i]
    exact hB0
  have hupper : Module.finrank ℝ trialityFixedBivectorLieSubalgebra ≤ 14 := by
    have hle := LinearMap.finrank_le_finrank_of_injective hproj_inj
    simpa [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin] using hle
  exact le_antisymm hupper hlower

/-- Intrinsic Lie-algebra isomorphism between the `S₃`-triality-fixed bivectors inside
`cl44BivectorLieSubalgebra` and `g2LieSubalgebra`. -/
noncomputable def trialityFixedEquivG2LieSubalgebra :
    trialityFixedBivectorLieSubalgebra ≃ₗ⁅ℝ⁆ g2LieSubalgebra :=
  let hrank : Module.finrank ℝ g2LieSubalgebra =
      Module.finrank ℝ trialityFixedBivectorLieSubalgebra := by
    rw [finrank_g2LieSubalgebra, finrank_trialityFixedBivectorLieSubalgebra]
  let leq : g2LieSubalgebra ≃ₗ[ℝ] trialityFixedBivectorLieSubalgebra :=
    LinearEquiv.ofInjectiveOfFinrankEq g2ToTrialityFixedLieHom.toLinearMap
      g2ToTrialityFixedLieHom_injective hrank
  (LieEquiv.ofBijective g2ToTrialityFixedLieHom leq.bijective).symm

/-! ### 4. Generic Cartan Eigen-Grading and `G_{2(2)}`-Invariant Cayley 4-Form (`M1b-T14-C4`) -/

/-- Simultaneous eigen-grading (`Ax.5`) implies `[H₁, H₂]` commutes with every joint
eigenvector `X`. -/
lemma simultaneous_eigen_grading_commutator_annihilates
    {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
    (H₁ H₂ X : B) (α₁ α₂ : R)
    (h1 : H₁ * X - X * H₁ = α₁ • X)
    (h2 : H₂ * X - X * H₂ = α₂ • X) :
    (H₁ * H₂ - H₂ * H₁) * X - X * (H₁ * H₂ - H₂ * H₁) = 0 := by
  have hjac : (H₁ * H₂ - H₂ * H₁) * X - X * (H₁ * H₂ - H₂ * H₁) =
      (H₁ * (H₂ * X - X * H₂) - (H₂ * X - X * H₂) * H₁) -
      (H₂ * (H₁ * X - X * H₁) - (H₁ * X - X * H₁) * H₂) := by
    noncomm_ring
  rw [hjac, h1, h2, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub, ← smul_sub,
    h1, h2, smul_smul, smul_smul, mul_comm α₁ α₂, sub_self]

/-- In a centerless Lie algebra, any pair `H₁, H₂` admitting a spanning set of joint
eigenvectors must commute (`⁅H₁, H₂⁆ = 0`). -/
lemma centerless_cartan_commutes
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (hcenter : ∀ Z : L, (∀ X : L, ⁅Z, X⁆ = 0) → Z = 0)
    (H₁ H₂ : L)
    (hspan : Submodule.span R {X : L | ∃ α₁ α₂ : R,
      ⁅H₁, X⁆ = α₁ • X ∧ ⁅H₂, X⁆ = α₂ • X} = ⊤) :
    ⁅H₁, H₂⁆ = 0 := by
  apply hcenter
  intro X
  have hX : X ∈ Submodule.span R {Y : L | ∃ α₁ α₂ : R,
      ⁅H₁, Y⁆ = α₁ • Y ∧ ⁅H₂, Y⁆ = α₂ • Y} := by
    rw [hspan]
    exact Submodule.mem_top
  refine Submodule.span_induction (hx := hX) ?_ ?_ ?_ ?_
  · rintro Y ⟨α₁, α₂, h1, h2⟩
    have hjac := leibniz_lie H₁ H₂ Y
    rw [h2, h1, lie_smul, lie_smul, h1, h2, smul_smul, smul_smul, mul_comm α₂ α₁] at hjac
    exact (eq_sub_of_add_eq hjac.symm).trans (sub_self _)
  · exact lie_zero _
  · intro A B _ _ hA hB
    rw [lie_add, hA, hB, add_zero]
  · intro r A _ hA
    rw [lie_smul, hA, smul_zero]

/-- Grade-4 Clifford subspace `Cl⁽⁴⁾(4,4) ⊂ M₁₆(ℝ)` spanned by all ordered 4-products
`γ_a γ_b γ_c γ_d` (`a < b < c < d`). -/
def cl44Grade4Span : Submodule ℝ (Matrix Krein16Idx Krein16Idx ℝ) :=
  Submodule.span ℝ {M | ∃ a b c d : Fin 8,
    a < b ∧ b < c ∧ c < d ∧ M = cl44Gen a * cl44Gen b * cl44Gen c * cl44Gen d}

private def Grade4Set : Type :=
  {s : Finset (Fin 8) // s ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin 8))}

private instance : Fintype Grade4Set :=
  inferInstanceAs (Fintype {s : Finset (Fin 8) //
    s ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin 8))})

private def grade4Elem (s : Grade4Set) : Matrix Krein16Idx Krein16Idx ℝ :=
  let hcard : s.1.card = 4 := (Finset.mem_powersetCard.mp s.2).2
  let f := s.1.orderEmbOfFin hcard
  cl44Gen (f 0) * cl44Gen (f 1) * cl44Gen (f 2) * cl44Gen (f 3)

/-- `Module.finrank ℝ cl44Grade4Span = 70` (`Nat.choose 8 4 = 70`). -/
lemma finrank_cl44Grade4Span : Module.finrank ℝ cl44Grade4Span = 70 := by
  let mask4 : Grade4Set → (Fin 8 → Bool) := fun s i => decide (i ∈ s.1)
  have hmask_inj : Function.Injective mask4 := by
    intro s₁ s₂ h
    apply Subtype.ext
    ext i
    have hi := congrFun h i
    simpa [mask4] using hi
  have hcl : ∀ s : Grade4Set, grade4Elem s = clMonomial (mask4 s) := by
    intro s
    have hcard : s.1.card = 4 := (Finset.mem_powersetCard.mp s.2).2
    let f := s.1.orderEmbOfFin hcard
    let f0 := f 0
    let f1 := f 1
    let f2 := f 2
    let f3 := f 3
    have h01 : f0 < f1 := f.strictMono (by decide)
    have h12 : f1 < f2 := f.strictMono (by decide)
    have h23 : f2 < f3 := f.strictMono (by decide)
    have hmem : ∀ i : Fin 8, i ∈ s.1 ↔ i = f0 ∨ i = f1 ∨ i = f2 ∨ i = f3 := by
      intro i
      rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin s.1 hcard, Set.mem_range]
      constructor
      · rintro ⟨j, rfl⟩
        fin_cases j
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
    have hstep : ∀ k : ℕ, k ≤ 8 →
        clMonomialGenFrom cl44Gen k (mask4 s) =
          (if k ≤ f0.val then cl44Gen f0 else 1) *
          (if k ≤ f1.val then cl44Gen f1 else 1) *
          (if k ≤ f2.val then cl44Gen f2 else 1) *
          (if k ≤ f3.val then cl44Gen f3 else 1) := by
      intro k hk
      induction hd : 8 - k generalizing k with
      | zero =>
          have hk8 : k = 8 := by omega
          subst hk8
          rw [clMonomialGenFrom_ge cl44Gen 8 (le_refl _)]
          have hf0 : ¬ (8 ≤ f0.val) := by omega
          have hf1 : ¬ (8 ≤ f1.val) := by omega
          have hf2 : ¬ (8 ≤ f2.val) := by omega
          have hf3 : ¬ (8 ≤ f3.val) := by omega
          simp [hf0, hf1, hf2, hf3]
      | succ d' ih =>
          have hklt : k < 8 := by omega
          rw [clMonomialGenFrom_step cl44Gen k hklt, ih (k + 1) (by omega) (by omega)]
          have hk_iff : ∀ u : Fin 8, (⟨k, hklt⟩ : Fin 8) = u ↔ k = u.val := by
            intro u; simp [Fin.ext_iff]
          have hm : mask4 s ⟨k, hklt⟩ =
              decide (k = f0.val ∨ k = f1.val ∨ k = f2.val ∨ k = f3.val) := by
            simp only [mask4, hmem, hk_iff]
          rw [hm]
          by_cases h0 : k = f0.val
          · subst h0
            have h01' : f0.val ≤ f1.val := le_of_lt h01
            have h02' : f0.val ≤ f2.val := le_of_lt (lt_trans h01 h12)
            have h03' : f0.val ≤ f3.val := le_of_lt (lt_trans (lt_trans h01 h12) h23)
            have h1 : f0.val + 1 ≤ f1.val := h01
            have h2 : f0.val + 1 ≤ f2.val := lt_trans h01 h12
            have h3 : f0.val + 1 ≤ f3.val := lt_trans (lt_trans h01 h12) h23
            simp [h01', h02', h03', h1, h2, h3, Matrix.mul_assoc]
          · by_cases h1 : k = f1.val
            · subst h1
              have hn0 : ¬ (f1.val ≤ f0.val) := Nat.not_le.mpr h01
              have hn0' : ¬ (f1.val + 1 ≤ f0.val) := by omega
              have h12' : f1.val ≤ f2.val := le_of_lt h12
              have h13' : f1.val ≤ f3.val := le_of_lt (lt_trans h12 h23)
              have h2 : f1.val + 1 ≤ f2.val := h12
              have h3 : f1.val + 1 ≤ f3.val := lt_trans h12 h23
              simp [h0, hn0, hn0', h12', h13', h2, h3, Matrix.mul_assoc]
            · by_cases h2 : k = f2.val
              · subst h2
                have hn0 : ¬ (f2.val ≤ f0.val) := Nat.not_le.mpr (lt_trans h01 h12)
                have hn0' : ¬ (f2.val + 1 ≤ f0.val) := by omega
                have hn1 : ¬ (f2.val ≤ f1.val) := Nat.not_le.mpr h12
                have hn1' : ¬ (f2.val + 1 ≤ f1.val) := by omega
                have h23' : f2.val ≤ f3.val := le_of_lt h23
                have h3 : f2.val + 1 ≤ f3.val := h23
                simp [h0, h1, hn0, hn0', hn1, hn1', h23', h3]
              · by_cases h3 : k = f3.val
                · subst h3
                  have hn0 : ¬ (f3.val ≤ f0.val) := Nat.not_le.mpr (lt_trans (lt_trans h01 h12) h23)
                  have hn0' : ¬ (f3.val + 1 ≤ f0.val) := by omega
                  have hn1 : ¬ (f3.val ≤ f1.val) := Nat.not_le.mpr (lt_trans h12 h23)
                  have hn1' : ¬ (f3.val + 1 ≤ f1.val) := by omega
                  have hn2 : ¬ (f3.val ≤ f2.val) := Nat.not_le.mpr h23
                  have hn2' : ¬ (f3.val + 1 ≤ f2.val) := by omega
                  simp [h0, h1, h2, hn0, hn0', hn1, hn1', hn2, hn2']
                · have ha0 : k ≤ f0.val ↔ k + 1 ≤ f0.val := by omega
                  have ha1 : k ≤ f1.val ↔ k + 1 ≤ f1.val := by omega
                  have ha2 : k ≤ f2.val ↔ k + 1 ≤ f2.val := by omega
                  have ha3 : k ≤ f3.val ↔ k + 1 ≤ f3.val := by omega
                  simp [h0, h1, h2, h3, ha0, ha1, ha2, ha3]
    change cl44Gen f0 * cl44Gen f1 * cl44Gen f2 * cl44Gen f3 = clMonomialGenFrom cl44Gen 0 (mask4 s)
    rw [hstep 0 (Nat.zero_le _)]
    simp
  have hli : LinearIndependent ℝ grade4Elem := by
    have heq : grade4Elem = fun s => clMonomial (mask4 s) := funext hcl
    rw [heq]
    exact clMonomial_linearIndependent.comp mask4 hmask_inj
  have hrange : Set.range grade4Elem = {M | ∃ a b c d : Fin 8,
      a < b ∧ b < c ∧ c < d ∧ M = cl44Gen a * cl44Gen b * cl44Gen c * cl44Gen d} := by
    ext M
    constructor
    · rintro ⟨s, rfl⟩
      have hcard : s.1.card = 4 := (Finset.mem_powersetCard.mp s.2).2
      let f := s.1.orderEmbOfFin hcard
      exact ⟨f 0, f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide),
        f.strictMono (by decide), rfl⟩
    · rintro ⟨a, b, c, d, hab, hbc, hcd, rfl⟩
      let s0 : Finset (Fin 8) := {a, b, c, d}
      have hab' : a ≠ b := ne_of_lt hab
      have hac' : a ≠ c := ne_of_lt (lt_trans hab hbc)
      have had' : a ≠ d := ne_of_lt (lt_trans (lt_trans hab hbc) hcd)
      have hbc' : b ≠ c := ne_of_lt hbc
      have hbd' : b ≠ d := ne_of_lt (lt_trans hbc hcd)
      have hcd' : c ≠ d := ne_of_lt hcd
      have hcard : s0.card = 4 := by
        simp [s0, hab', hac', had', hbc', hbd', hcd']
      let s : Grade4Set := ⟨s0, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩⟩
      refine ⟨s, ?_⟩
      let g : Fin 4 ↪o Fin 8 :=
        OrderEmbedding.ofStrictMono ![a, b, c, d] (by
          have habc := lt_trans hab hbc
          have habcd := lt_trans habc hcd
          have hbcd := lt_trans hbc hcd
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all)
      have hg_range : Set.range g = (s0 : Set (Fin 8)) := by
        ext x
        simp only [Set.mem_range, Finset.mem_coe, s0, Finset.mem_insert, Finset.mem_singleton, g]
        constructor
        · rintro ⟨j, rfl⟩
          fin_cases j
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
        · rintro (rfl | rfl | rfl | rfl)
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨3, rfl⟩
      have heq_emb : s.1.orderEmbOfFin hcard = g :=
        (Finset.orderEmbOfFin_unique' hcard (fun i => by
          rw [← Finset.mem_coe, ← hg_range]
          exact Set.mem_range_self i)).symm
      change cl44Gen (s.1.orderEmbOfFin hcard 0) * cl44Gen (s.1.orderEmbOfFin hcard 1) *
          cl44Gen (s.1.orderEmbOfFin hcard 2) * cl44Gen (s.1.orderEmbOfFin hcard 3) =
        cl44Gen a * cl44Gen b * cl44Gen c * cl44Gen d
      rw [heq_emb]
      rfl
  unfold cl44Grade4Span
  rw [← hrange, finrank_span_eq_card hli]
  change Fintype.card {s : Finset (Fin 8) //
    s ∈ Finset.powersetCard 4 (Finset.univ : Finset (Fin 8))} = 70
  rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_fin]
  decide

/-- `G_{2(2)}`-invariant Cayley 4-form inside `Cl⁽⁴⁾(4,4)` supported on `{1..7}`. -/
def cayleyFourFormCl44 : Matrix Krein16Idx Krein16Idx ℝ :=
  cl44Gen 1 * cl44Gen 2 * cl44Gen 4 * cl44Gen 7 -
  cl44Gen 1 * cl44Gen 2 * cl44Gen 5 * cl44Gen 6 -
  cl44Gen 1 * cl44Gen 3 * cl44Gen 4 * cl44Gen 6 -
  cl44Gen 1 * cl44Gen 3 * cl44Gen 5 * cl44Gen 7 +
  cl44Gen 2 * cl44Gen 3 * cl44Gen 4 * cl44Gen 5 -
  cl44Gen 2 * cl44Gen 3 * cl44Gen 6 * cl44Gen 7 +
  cl44Gen 4 * cl44Gen 5 * cl44Gen 6 * cl44Gen 7

section MatrixUnitExpandCayley

attribute [local simp]
  tensor4_mul tensor4_one
  tensor4_zero_0 tensor4_zero_1 tensor4_zero_2 tensor4_zero_3
  tensor4_neg_0 tensor4_neg_1 tensor4_neg_2 tensor4_neg_3
  add_mul mul_add sub_mul mul_sub neg_mul mul_neg
  mul_assoc one_mul mul_one zero_mul mul_zero
  cl11Pos_sq cl11Neg_sq cl11Grad_sq
  cl11Pos_mul_cl11Neg cl11Neg_mul_cl11Pos
  cl11Neg_mul_cl11Grad cl11Grad_mul_cl11Neg
  cl11Pos_mul_cl11Grad cl11Grad_mul_cl11Pos
  cl11Up_mul_cl11Up cl11Down_mul_cl11Down cl11Up_mul_cl11Down cl11Down_mul_cl11Up
  cl11P0_mul_cl11P0 cl11P1_mul_cl11P1 cl11P0_mul_cl11P1 cl11P1_mul_cl11P0
  cl11Grad_mul_cl11Up cl11Up_mul_cl11Grad cl11Grad_mul_cl11Down cl11Down_mul_cl11Grad
  cl11Grad_mul_cl11P0 cl11P0_mul_cl11Grad cl11Grad_mul_cl11P1 cl11P1_mul_cl11Grad
  cl11P0_mul_cl11Up cl11P1_mul_cl11Up cl11Up_mul_cl11P0 cl11Up_mul_cl11P1
  cl11P0_mul_cl11Down cl11P1_mul_cl11Down cl11Down_mul_cl11P0 cl11Down_mul_cl11P1
  cl11Pos_mul_cl11P0 cl11P0_mul_cl11Pos cl11Pos_mul_cl11P1 cl11P1_mul_cl11Pos
  cl11Neg_mul_cl11P0 cl11P0_mul_cl11Neg cl11Neg_mul_cl11P1 cl11P1_mul_cl11Neg
  cl11Pos_mul_cl11Up cl11Up_mul_cl11Pos cl11Pos_mul_cl11Down cl11Down_mul_cl11Pos
  cl11Neg_mul_cl11Up cl11Up_mul_cl11Neg cl11Neg_mul_cl11Down cl11Down_mul_cl11Neg

private lemma cayleyFourFormCl44_eq :
    cayleyFourFormCl44 =
      (4 : ℝ) • (psiPlusProj + cl44Gen 0 * psiPlusProj * cl44Gen 0) - 1 := by
  unfold cayleyFourFormCl44 psiPlusProj cl44Gen
  simp
  rw [← tensor4_one]
  simp only [cl11One_eq_P0_add_P1, cl11Grad_eq_P0_sub_P1, cl11Pos_eq_Up_add_Down,
    cl11Neg_eq_Down_sub_Up, tensor4_add_0, tensor4_add_1, tensor4_add_2, tensor4_add_3,
    tensor4_sub_1, tensor4_sub_2, tensor4_sub_3]
  module

private lemma cl44Gen0_conj_psiPlusProj :
    cl44Gen 0 * psiPlusProj * cl44Gen 0 =
      tensor4 cl11P1 cl11P0 cl11P0 cl11P0 + tensor4 cl11Down cl11Up cl11Up cl11Up +
      tensor4 cl11Up cl11Down cl11Down cl11Down + tensor4 cl11P0 cl11P1 cl11P1 cl11P1 := by
  unfold cl44Gen psiPlusProj
  simp

end MatrixUnitExpandCayley

/-- Nonvanishing, grade-4 membership, non-bivector separation, `e₀`-commutativity, and
full `g_{2(2)}`-invariance of `cayleyFourFormCl44`. -/
lemma cayleyFourFormCl44_properties :
    cayleyFourFormCl44 ≠ 0 ∧
    cayleyFourFormCl44 ∈ cl44Grade4Span ∧
    cayleyFourFormCl44 ∉ cl44BivectorSpan ∧
    cayleyFourFormCl44 * cl44Gen 0 = cl44Gen 0 * cayleyFourFormCl44 ∧
    ∀ Z ∈ g2Submodule, Z * cayleyFourFormCl44 - cayleyFourFormCl44 * Z = 0 := by
  have hne : cayleyFourFormCl44 ≠ 0 := by
    intro h
    have h00 := congrArg (fun M : Matrix Krein16Idx Krein16Idx ℝ =>
      M (0, 0, 0, 0) (0, 0, 0, 0)) h
    rw [cayleyFourFormCl44_eq, cl44Gen0_conj_psiPlusProj] at h00
    simp [psiPlusProj, tensor4, cl11P0, cl11P1, cl11Up, cl11Down] at h00
    norm_num at h00
  have hmem4 : cayleyFourFormCl44 ∈ cl44Grade4Span := by
    have hq : ∀ a b c d : Fin 8, a < b → b < c → c < d →
        cl44Gen a * cl44Gen b * cl44Gen c * cl44Gen d ∈ cl44Grade4Span :=
      fun a b c d hab hbc hcd => Submodule.subset_span ⟨a, b, c, d, hab, hbc, hcd, rfl⟩
    unfold cayleyFourFormCl44
    exact Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ (Submodule.sub_mem _
        (hq 1 2 4 7 (by decide) (by decide) (by decide))
        (hq 1 2 5 6 (by decide) (by decide) (by decide)))
        (hq 1 3 4 6 (by decide) (by decide) (by decide)))
        (hq 1 3 5 7 (by decide) (by decide) (by decide)))
        (hq 2 3 4 5 (by decide) (by decide) (by decide)))
        (hq 2 3 6 7 (by decide) (by decide) (by decide)))
        (hq 4 5 6 7 (by decide) (by decide) (by decide))
  have hnbiv : cayleyFourFormCl44 ∉ cl44BivectorSpan := by
    intro hbiv
    have htr_biv : ∀ B ∈ cl44BivectorSpan, Matrix.trace (B * kreinMetric88) = 0 := by
      intro B hB
      have hskew : Bᵀ * kreinMetric88 + kreinMetric88 * B = 0 := by
        refine Submodule.span_induction (hx := hB) ?_ ?_ ?_ ?_
        · rintro _ ⟨a, b, hab, rfl⟩
          exact (cl44Bivector_chiral_even_and_krein_skew hab).2
        · simp
        · intro X Y _ _ hX hY
          rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
          calc
            (Xᵀ * kreinMetric88 + Yᵀ * kreinMetric88) + (kreinMetric88 * X + kreinMetric88 * Y)
                = (Xᵀ * kreinMetric88 + kreinMetric88 * X) +
                  (Yᵀ * kreinMetric88 + kreinMetric88 * Y) := by abel
            _ = 0 := by rw [hX, hY, add_zero]
        · intro r X _ hX
          rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]
      have htr := congrArg Matrix.trace hskew
      rw [Matrix.trace_add, Matrix.trace_zero] at htr
      have htr1 : Matrix.trace (Bᵀ * kreinMetric88) = Matrix.trace (B * kreinMetric88) := by
        calc
          Matrix.trace (Bᵀ * kreinMetric88)
              = Matrix.trace ((Bᵀ * kreinMetric88)ᵀ) := (Matrix.trace_transpose _).symm
          _ = Matrix.trace (kreinMetric88 * B) := by
                rw [Matrix.transpose_mul, kreinMetric88_properties.2.1, Matrix.transpose_transpose]
          _ = Matrix.trace (B * kreinMetric88) := Matrix.trace_mul_comm _ _
      rw [htr1, Matrix.trace_mul_comm kreinMetric88 B] at htr
      linarith
    have h0 := htr_biv cayleyFourFormCl44 hbiv
    have htr_psi : Matrix.trace (psiPlusProj * kreinMetric88) = 2 := by
      have htr_up : Matrix.trace (cl11Up * cl11Pos) = 1 := by
        rw [cl11Up_mul_cl11Pos]; unfold Matrix.trace cl11P0; rw [Fin.sum_univ_two]; norm_num
      have htr_un : Matrix.trace (cl11Up * cl11Neg) = 1 := by
        rw [cl11Up_mul_cl11Neg]; unfold Matrix.trace cl11P0; rw [Fin.sum_univ_two]; norm_num
      have htr_dp : Matrix.trace (cl11Down * cl11Pos) = 1 := by
        rw [cl11Down_mul_cl11Pos]; unfold Matrix.trace cl11P1; rw [Fin.sum_univ_two]; norm_num
      have htr_dn : Matrix.trace (cl11Down * cl11Neg) = -1 := by
        rw [cl11Down_mul_cl11Neg]; unfold Matrix.trace cl11P1; rw [Fin.sum_univ_two]; norm_num
      have htr_p0p : Matrix.trace (cl11P0 * cl11Pos) = 0 := by
        rw [cl11P0_mul_cl11Pos]; unfold Matrix.trace cl11Up; rw [Fin.sum_univ_two]; norm_num
      have htr_p0n : Matrix.trace (cl11P0 * cl11Neg) = 0 := by
        rw [cl11P0_mul_cl11Neg]; unfold Matrix.trace cl11Up; rw [Fin.sum_univ_two]; norm_num
      have htr_p1p : Matrix.trace (cl11P1 * cl11Pos) = 0 := by
        rw [cl11P1_mul_cl11Pos]; unfold Matrix.trace cl11Down; rw [Fin.sum_univ_two]; norm_num
      have htr_p1n : Matrix.trace (cl11P1 * cl11Neg) = 0 := by
        rw [cl11P1_mul_cl11Neg]; unfold Matrix.trace cl11Down; rw [Fin.sum_univ_two]; norm_num
      unfold psiPlusProj kreinMetric88
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_mul,
        Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
        tensor4_mul, tensor4_mul, tensor4_mul, tensor4_mul,
        tensor4_trace, tensor4_trace, tensor4_trace, tensor4_trace,
        htr_p0p, htr_up, htr_un, htr_dp, htr_dn, htr_p1p]
      norm_num
    have htr_conj : Matrix.trace ((cl44Gen 0 * psiPlusProj * cl44Gen 0) * kreinMetric88) = 2 := by
      have he0_eta : cl44Gen 0 * kreinMetric88 * cl44Gen 0 = kreinMetric88 := by
        unfold cl44Gen kreinMetric88
        rw [tensor4_mul, tensor4_mul, cl11Pos_sq, Matrix.one_mul, Matrix.mul_one,
          Matrix.one_mul, Matrix.mul_one]
      calc
        Matrix.trace ((cl44Gen 0 * psiPlusProj * cl44Gen 0) * kreinMetric88)
            = Matrix.trace (psiPlusProj * (cl44Gen 0 * kreinMetric88 * cl44Gen 0)) := by
                rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm (cl44Gen 0)]
                simp only [Matrix.mul_assoc]
        _ = Matrix.trace (psiPlusProj * kreinMetric88) := by rw [he0_eta]
        _ = 2 := htr_psi
    have htr16 : Matrix.trace (cayleyFourFormCl44 * kreinMetric88) = 16 := by
      rw [cayleyFourFormCl44_eq, Matrix.sub_mul, Matrix.smul_mul, Matrix.add_mul,
        Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
        htr_psi, htr_conj, kreinMetric88_properties.2.2.2.1, smul_eq_mul]
      norm_num
    linarith
  have he0_comm : cayleyFourFormCl44 * cl44Gen 0 = cl44Gen 0 * cayleyFourFormCl44 := by
    have he0sq : cl44Gen 0 * cl44Gen 0 = 1 := by rw [cl44Gen_sq 0]; simp
    rw [cayleyFourFormCl44_eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    have h1 : (cl44Gen 0 * psiPlusProj * cl44Gen 0) * cl44Gen 0 = cl44Gen 0 * psiPlusProj := by
      rw [Matrix.mul_assoc, he0sq, Matrix.mul_one]
    have h2 : cl44Gen 0 * (cl44Gen 0 * psiPlusProj * cl44Gen 0) = psiPlusProj * cl44Gen 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, he0sq, Matrix.one_mul]
    rw [h1, h2, add_comm]
  have hg2_inv : ∀ Z ∈ g2Submodule, Z * cayleyFourFormCl44 - cayleyFourFormCl44 * Z = 0 := by
    intro Z hZ
    have hstab := g2Submodule_mem_stabilizer hZ
    have hZpsi : Z * psiPlusProj = 0 := by
      ext i j
      simp only [Matrix.mul_apply, psiPlusProj_entry, Matrix.zero_apply]
      have hsum : (∑ k : Krein16Idx, Z i k *
          (majoranaRefSpinor k * (kreinMetric88.mulVec majoranaRefSpinor) j)) =
          (Z.mulVec majoranaRefSpinor i) * (kreinMetric88.mulVec majoranaRefSpinor) j := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
      rw [hsum, hstab.2.2.2, Pi.zero_apply, zero_mul]
    have hpsiZ : psiPlusProj * Z = 0 := by
      have hpsi_sym : psiPlusProjᵀ = psiPlusProj := by
        unfold psiPlusProj
        rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_add,
          tensor4_transpose, tensor4_transpose, tensor4_transpose, tensor4_transpose,
          cl11P0_transpose, cl11Up_transpose, cl11Down_transpose, cl11P1_transpose]
        abel
      have hZeta : Zᵀ * kreinMetric88 = -(kreinMetric88 * Z) :=
        eq_neg_of_add_eq_zero_left hstab.1
      have hT : (psiPlusProj * Z)ᵀ = -(kreinMetric88 * (Z * psiPlusProj) * kreinMetric88) := by
        calc
          (psiPlusProj * Z)ᵀ = Zᵀ * psiPlusProj := by rw [Matrix.transpose_mul, hpsi_sym]
          _ = Zᵀ * (kreinMetric88 * kreinMetric88) * psiPlusProj := by
                rw [kreinMetric88_properties.2.2.1, Matrix.mul_one]
          _ = (Zᵀ * kreinMetric88) * (kreinMetric88 * psiPlusProj) := by
                simp only [Matrix.mul_assoc]
          _ = (-(kreinMetric88 * Z)) * (psiPlusProj * kreinMetric88) := by
                rw [hZeta, psiPlusProj_comm_kreinMetric88]
          _ = -(kreinMetric88 * (Z * psiPlusProj) * kreinMetric88) := by
                simp only [Matrix.neg_mul, Matrix.mul_assoc]
      have hT0 : (psiPlusProj * Z)ᵀ = 0 := by
        rw [hT, hZpsi, Matrix.mul_zero, Matrix.zero_mul, neg_zero]
      have := congrArg Matrix.transpose hT0
      simpa using this
    have hZ_conj_l : Z * (cl44Gen 0 * psiPlusProj * cl44Gen 0) = 0 := by
      calc
        Z * (cl44Gen 0 * psiPlusProj * cl44Gen 0)
            = (Z * cl44Gen 0) * psiPlusProj * cl44Gen 0 := by simp only [Matrix.mul_assoc]
        _ = (cl44Gen 0 * Z) * psiPlusProj * cl44Gen 0 := by rw [hstab.2.2.1]
        _ = cl44Gen 0 * (Z * psiPlusProj) * cl44Gen 0 := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hZpsi, Matrix.mul_zero, Matrix.zero_mul]
    have hZ_conj_r : (cl44Gen 0 * psiPlusProj * cl44Gen 0) * Z = 0 := by
      calc
        (cl44Gen 0 * psiPlusProj * cl44Gen 0) * Z
            = cl44Gen 0 * psiPlusProj * (cl44Gen 0 * Z) := by simp only [Matrix.mul_assoc]
        _ = cl44Gen 0 * psiPlusProj * (Z * cl44Gen 0) := by rw [hstab.2.2.1]
        _ = cl44Gen 0 * (psiPlusProj * Z) * cl44Gen 0 := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hpsiZ, Matrix.mul_zero, Matrix.zero_mul]
    rw [cayleyFourFormCl44_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, hZpsi, hpsiZ, hZ_conj_l, hZ_conj_r]
    simp
  exact ⟨hne, hmem4, hnbiv, he0_comm, hg2_inv⟩

/-! ### 5. Exact Turn 14 28-Edge 15-Node Hasse Poset Alignment (`M1b-T14-C5`) -/

/-- The 15 nodes of the exact Turn 14 Krein-triality causal Hasse poset (`rk A0 = 3`,
`rk A_omega = 4`). -/
inductive Turn14KreinPosetNode : Type
  | Delta0 | T | S
  | K_TT | Pi_ST | Sigma_TS | Gamma_SS
  | G | Tau | A0
  | B | A_omega
  | H | E
  | XiTop
  deriving DecidableEq, Repr

/-- Exact Turn 14 rank grading (`0..6`). -/
def Turn14KreinPosetNode.rank : Turn14KreinPosetNode → ℕ
  | .Delta0 => 0
  | .T => 1 | .S => 1
  | .K_TT => 2 | .Pi_ST => 2 | .Sigma_TS => 2 | .Gamma_SS => 2
  | .G => 3 | .Tau => 3 | .A0 => 3
  | .B => 4 | .A_omega => 4
  | .H => 5 | .E => 5
  | .XiTop => 6

/-- Exact 28-edge Turn 14 Hasse covering relation. -/
def Turn14KreinPosetNode.Covers : Turn14KreinPosetNode → Turn14KreinPosetNode → Bool
  | .Delta0, .T => true | .Delta0, .S => true
  | .T, .K_TT => true | .T, .Pi_ST => true | .T, .Sigma_TS => true
  | .S, .Pi_ST => true | .S, .Sigma_TS => true | .S, .Gamma_SS => true
  | .Pi_ST, .G => true | .Sigma_TS, .G => true
  | .Pi_ST, .Tau => true | .Sigma_TS, .Tau => true
  | .K_TT, .A0 => true | .Pi_ST, .A0 => true | .Sigma_TS, .A0 => true
  | .K_TT, .B => true | .G, .B => true | .Tau, .B => true | .Gamma_SS, .B => true
  | .A0, .A_omega => true | .Tau, .A_omega => true | .Gamma_SS, .A_omega => true
  | .B, .H => true | .A_omega, .H => true
  | .B, .E => true | .A_omega, .E => true
  | .H, .XiTop => true | .E, .XiTop => true
  | _, _ => false

/-- Every covering edge strictly increases `Turn14KreinPosetNode.rank`. -/
lemma covers_strict_rank (u v : Turn14KreinPosetNode) (h : u.Covers v = true) :
    u.rank < v.rank := by
  cases u <;> cases v <;> simp [Turn14KreinPosetNode.Covers] at h <;> decide

private lemma reflTransGen_covers_eq_or_rank_lt {u v : Turn14KreinPosetNode}
    (h : Relation.ReflTransGen (fun a b => a.Covers b = true) u v) :
    u = v ∨ u.rank < v.rank := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
      rcases ih with rfl | hlt
      · exact Or.inr (covers_strict_rank _ _ hbc)
      · exact Or.inr (lt_trans hlt (covers_strict_rank _ _ hbc))

/-- Partial order generated by the reflexive-transitive closure of the 28 Turn 14 edges. -/
instance : PartialOrder Turn14KreinPosetNode where
  le u v := Relation.ReflTransGen (fun a b => a.Covers b = true) u v
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm u v huv hvu := by
    rcases reflTransGen_covers_eq_or_rank_lt huv with rfl | h1
    · rfl
    · rcases reflTransGen_covers_eq_or_rank_lt hvu with h_eq | h2
      · exact h_eq.symm
      · exact False.elim (lt_asymm h1 h2)

private def turn14ToFin : Turn14KreinPosetNode → Fin 15
  | .Delta0 => 0 | .T => 1 | .S => 2
  | .K_TT => 3 | .Pi_ST => 4 | .Sigma_TS => 5 | .Gamma_SS => 6
  | .G => 7 | .Tau => 8 | .A0 => 9
  | .B => 10 | .A_omega => 11
  | .H => 12 | .E => 13
  | .XiTop => 14

private def turn14OfFin : Fin 15 → Turn14KreinPosetNode
  | 0 => .Delta0 | 1 => .T | 2 => .S
  | 3 => .K_TT | 4 => .Pi_ST | 5 => .Sigma_TS | 6 => .Gamma_SS
  | 7 => .G | 8 => .Tau | 9 => .A0
  | 10 => .B | 11 => .A_omega
  | 12 => .H | 13 => .E
  | 14 => .XiTop

private lemma turn14OfFin_toFin (u : Turn14KreinPosetNode) :
    turn14OfFin (turn14ToFin u) = u := by
  cases u <;> rfl

private def turn14CausalLe (u v : Turn14KreinPosetNode) : Bool :=
  match u with
  | .Delta0 => true
  | .T => v != .Delta0 && v != .S && v != .Gamma_SS
  | .S => v != .Delta0 && v != .T && v != .K_TT
  | .K_TT => v == .K_TT || v == .A0 || v == .B || v == .A_omega ||
      v == .H || v == .E || v == .XiTop
  | .Pi_ST => v == .Pi_ST || v.rank >= 3
  | .Sigma_TS => v == .Sigma_TS || v.rank >= 3
  | .Gamma_SS => v == .Gamma_SS || v.rank >= 4
  | .G => v == .G || v == .B || v.rank >= 5
  | .Tau => v == .Tau || v.rank >= 4
  | .A0 => v == .A0 || v == .A_omega || v.rank >= 5
  | .B => v == .B || v.rank >= 5
  | .A_omega => v == .A_omega || v.rank >= 5
  | .H => v == .H || v == .XiTop
  | .E => v == .E || v == .XiTop
  | .XiTop => v == .XiTop

private lemma turn14CausalLe_refl (i : Fin 15) :
    turn14CausalLe (turn14OfFin i) (turn14OfFin i) = true := by
  fin_cases i <;> decide

private lemma turn14CausalLe_of_covers (i j : Fin 15)
    (h : (turn14OfFin i).Covers (turn14OfFin j) = true) :
    turn14CausalLe (turn14OfFin i) (turn14OfFin j) = true := by
  fin_cases i <;> fin_cases j <;> simp [turn14OfFin, Turn14KreinPosetNode.Covers] at h <;> decide

private lemma turn14CausalLe_trans (i j k : Fin 15) :
    turn14CausalLe (turn14OfFin i) (turn14OfFin j) = true →
    turn14CausalLe (turn14OfFin j) (turn14OfFin k) = true →
    turn14CausalLe (turn14OfFin i) (turn14OfFin k) = true := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

private lemma turn14CausalLe_step :
    ∀ i j : Fin 15, turn14CausalLe (turn14OfFin i) (turn14OfFin j) = true →
      i = j ∨ ∃ k : Fin 15, (turn14OfFin i).Covers (turn14OfFin k) = true ∧
        turn14CausalLe (turn14OfFin k) (turn14OfFin j) = true ∧
        (turn14OfFin i).rank < (turn14OfFin k).rank := by
  decide

private lemma le_iff_turn14CausalLe (u v : Turn14KreinPosetNode) :
    u ≤ v ↔ turn14CausalLe u v = true := by
  constructor
  · intro huv
    induction huv with
    | refl =>
        rw [← turn14OfFin_toFin u]
        exact turn14CausalLe_refl (turn14ToFin u)
    | @tail b c _ hbc ih =>
        rw [← turn14OfFin_toFin u, ← turn14OfFin_toFin b] at ih
        rw [← turn14OfFin_toFin b, ← turn14OfFin_toFin c] at hbc
        rw [← turn14OfFin_toFin u, ← turn14OfFin_toFin c]
        exact turn14CausalLe_trans _ _ _ ih (turn14CausalLe_of_covers _ _ hbc)
  · suffices h : ∀ d : ℕ, ∀ u v : Turn14KreinPosetNode,
        6 - u.rank = d → turn14CausalLe u v = true → u ≤ v by
      exact h (6 - u.rank) u v rfl
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro u v hd hle
        rw [← turn14OfFin_toFin u, ← turn14OfFin_toFin v] at hle ⊢
        rcases turn14CausalLe_step (turn14ToFin u) (turn14ToFin v) hle with
          heq | ⟨k, hik, hkj, hrk⟩
        · rw [heq]
        · have hrk_le : (turn14OfFin k).rank ≤ 6 := by
            fin_cases k <;> decide
          have hd' : 6 - (turn14OfFin k).rank < d := by
            have hu : (turn14OfFin (turn14ToFin u)).rank = u.rank := by
              rw [turn14OfFin_toFin]
            rw [← hd, ← hu]
            omega
          exact le_trans (Relation.ReflTransGen.single hik)
            (ih (6 - (turn14OfFin k).rank) hd' (turn14OfFin k) (turn14OfFin (turn14ToFin v))
              rfl hkj)

/-- Every covering edge in `Turn14KreinPosetNode` is transitively reduced (a genuine Hasse
edge with no intermediate element). -/
lemma covers_transitively_reduced (u v : Turn14KreinPosetNode) (h : u.Covers v = true) :
    u < v ∧ ¬ ∃ w : Turn14KreinPosetNode, u < w ∧ w < v := by
  have huv_le : u ≤ v := Relation.ReflTransGen.single h
  have hne : u ≠ v := by
    intro heq
    subst heq
    exact Nat.lt_irrefl _ (covers_strict_rank u u h)
  have huv_lt : u < v := lt_of_le_of_ne huv_le hne
  refine ⟨huv_lt, ?_⟩
  rintro ⟨w, huw, hwv⟩
  have huw_c := (le_iff_turn14CausalLe u w).mp (le_of_lt huw)
  have hwv_c := (le_iff_turn14CausalLe w v).mp (le_of_lt hwv)
  have huw_ne : turn14ToFin u ≠ turn14ToFin w := fun h =>
    ne_of_lt huw (by simpa [turn14OfFin_toFin] using congrArg turn14OfFin h)
  have hwv_ne : turn14ToFin w ≠ turn14ToFin v := fun h =>
    ne_of_lt hwv (by simpa [turn14OfFin_toFin] using congrArg turn14OfFin h)
  rw [← turn14OfFin_toFin u, ← turn14OfFin_toFin v] at h
  rw [← turn14OfFin_toFin u, ← turn14OfFin_toFin w] at huw_c
  rw [← turn14OfFin_toFin w, ← turn14OfFin_toFin v] at hwv_c
  have hdec : ∀ i j k : Fin 15,
      (turn14OfFin i).Covers (turn14OfFin j) = true →
      turn14CausalLe (turn14OfFin i) (turn14OfFin k) = true →
      turn14CausalLe (turn14OfFin k) (turn14OfFin j) = true →
      i ≠ k → k ≠ j → False := by
    decide
  exact hdec (turn14ToFin u) (turn14ToFin v) (turn14ToFin w) h huw_c hwv_c huw_ne hwv_ne

/-- The set of covering predecessors of every node `v` is an antichain. -/
lemma coveringPred_antichain (v : Turn14KreinPosetNode) :
    IsAntichain (· ≤ ·) {u : Turn14KreinPosetNode | u.Covers v = true} := by
  intro u₁ hu₁ u₂ hu₂ hne hle
  have hc := (le_iff_turn14CausalLe u₁ u₂).mp hle
  have hne' : turn14ToFin u₁ ≠ turn14ToFin u₂ := fun h =>
    hne (by simpa [turn14OfFin_toFin] using congrArg turn14OfFin h)
  change u₁.Covers v = true at hu₁
  change u₂.Covers v = true at hu₂
  rw [← turn14OfFin_toFin u₁, ← turn14OfFin_toFin v] at hu₁
  rw [← turn14OfFin_toFin u₂, ← turn14OfFin_toFin v] at hu₂
  rw [← turn14OfFin_toFin u₁, ← turn14OfFin_toFin u₂] at hc
  have hdec : ∀ i j k : Fin 15,
      (turn14OfFin i).Covers (turn14OfFin k) = true →
      (turn14OfFin j).Covers (turn14OfFin k) = true →
      i ≠ j → turn14CausalLe (turn14OfFin i) (turn14OfFin j) = true → False := by
    decide
  exact hdec (turn14ToFin u₁) (turn14ToFin u₂) (turn14ToFin v) hu₁ hu₂ hne' hc

/-- `Delta0` is the minimum element of `Turn14KreinPosetNode`. -/
lemma bot_le_all (x : Turn14KreinPosetNode) : Turn14KreinPosetNode.Delta0 ≤ x := by
  rw [le_iff_turn14CausalLe]
  rfl

/-- `XiTop` is the maximum element of `Turn14KreinPosetNode`. -/
lemma all_le_top (x : Turn14KreinPosetNode) : x ≤ Turn14KreinPosetNode.XiTop := by
  rw [le_iff_turn14CausalLe]
  cases x <;> rfl

/-- All 28 Turn 14 covering edges are transitively reduced and `{H, E}` has least upper
bound `XiTop`. -/
lemma turn14_covers_transitively_reduced_and_isLUB :
    (∀ u v : Turn14KreinPosetNode, u.Covers v = true →
      u < v ∧ ¬ ∃ w : Turn14KreinPosetNode, u < w ∧ w < v) ∧
    IsLUB ({Turn14KreinPosetNode.H, Turn14KreinPosetNode.E} : Set Turn14KreinPosetNode)
      Turn14KreinPosetNode.XiTop := by
  refine ⟨covers_transitively_reduced, ?_, ?_⟩
  · intro x _
    exact all_le_top x
  · intro x hx
    have hH : Turn14KreinPosetNode.H ≤ x := hx (by simp)
    have hE : Turn14KreinPosetNode.E ≤ x := hx (by simp)
    rw [le_iff_turn14CausalLe] at hH hE ⊢
    cases x <;> simp_all [turn14CausalLe]

end InfoGeometry.Lie.KreinCl44TrialityBottCayleyClosure
