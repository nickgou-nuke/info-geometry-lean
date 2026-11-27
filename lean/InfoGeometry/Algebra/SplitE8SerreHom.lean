/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SplitE8RootSystem
import InfoGeometry.Algebra.SplitE8Simplicity
import Mathlib.Algebra.Lie.SerreConstruction

/-!
# Serre presentation isomorphism for split `𝔈₈(8)` (`SplitE8Lie`)

The split `𝔈₈(8)` Magic-Square carrier `SplitE8Lie` has a 248-dimensional Chevalley
basis (`e8ChevalleyBasis`). This file proves the remaining positive and negative Serre
relations (`e8Simple_serre_E`, `e8Simple_serre_F`), descends Mathlib's free Lie algebra
evaluation to a Lie algebra homomorphism `splitE8SerreQuotientMap : LieAlgebra.e₈ ℝ →ₗ⁅ℝ⁆
SplitE8Lie`, proves surjectivity via `splitE8_simple_generators_generate`, bounds
`Module.finrank ℝ (LieAlgebra.e₈ ℝ) ≤ 248` via the Chevalley involution and triangular
spanning (`8 + 120 + 120`), and deduces the explicit Lie algebra equivalence
`splitE8SerreEquiv : LieAlgebra.e₈ ℝ ≃ₗ⁅ℝ⁆ SplitE8Lie`, `finrank_e8_serre = 248`, and
`e8Serre_isSimple : LieAlgebra.IsSimple ℝ (LieAlgebra.e₈ ℝ)`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open scoped BigOperators
open InfoGeometry.Algebra.MagicSquareTitsBracket
open InfoGeometry.Exceptional.CFSGPort.Chevalley

/-! ## 1. Serre Relations and Quotient Homomorphism into `SplitE8Lie` -/

private theorem forall_fin240_of_blocks (P : Fin 240 → Bool)
    (h0 : (List.finRange 24).all (fun k => P ⟨0 + k.val, by omega⟩) = true)
    (h1 : (List.finRange 24).all (fun k => P ⟨24 + k.val, by omega⟩) = true)
    (h2 : (List.finRange 24).all (fun k => P ⟨48 + k.val, by omega⟩) = true)
    (h3 : (List.finRange 24).all (fun k => P ⟨72 + k.val, by omega⟩) = true)
    (h4 : (List.finRange 24).all (fun k => P ⟨96 + k.val, by omega⟩) = true)
    (h5 : (List.finRange 24).all (fun k => P ⟨120 + k.val, by omega⟩) = true)
    (h6 : (List.finRange 24).all (fun k => P ⟨144 + k.val, by omega⟩) = true)
    (h7 : (List.finRange 24).all (fun k => P ⟨168 + k.val, by omega⟩) = true)
    (h8 : (List.finRange 24).all (fun k => P ⟨192 + k.val, by omega⟩) = true)
    (h9 : (List.finRange 24).all (fun k => P ⟨216 + k.val, by omega⟩) = true)
    (r : Fin 240) : P r = true := by
  have hb : ∀ (off : ℕ) (hoff : off + 24 ≤ 240),
      (List.finRange 24).all (fun k => P ⟨off + k.val, by omega⟩) = true →
      ∀ k : Fin 24, P ⟨off + k.val, by omega⟩ = true := by
    intro off hoff hchk k
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
    exact hchk k
  by_cases c0 : r.val < 24
  · have heq : (⟨0 + (⟨r.val, c0⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
      Fin.ext (by dsimp; omega)
    simpa [heq] using hb 0 (by decide) h0 ⟨r.val, c0⟩
  · by_cases c1 : r.val < 48
    · have hk : r.val - 24 < 24 := by omega
      have heq : (⟨24 + (⟨r.val - 24, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
        Fin.ext (by dsimp; omega)
      simpa [heq] using hb 24 (by decide) h1 ⟨r.val - 24, hk⟩
    · by_cases c2 : r.val < 72
      · have hk : r.val - 48 < 24 := by omega
        have heq : (⟨48 + (⟨r.val - 48, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using hb 48 (by decide) h2 ⟨r.val - 48, hk⟩
      · by_cases c3 : r.val < 96
        · have hk : r.val - 72 < 24 := by omega
          have heq : (⟨72 + (⟨r.val - 72, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
            Fin.ext (by dsimp; omega)
          simpa [heq] using hb 72 (by decide) h3 ⟨r.val - 72, hk⟩
        · by_cases c4 : r.val < 120
          · have hk : r.val - 96 < 24 := by omega
            have heq : (⟨96 + (⟨r.val - 96, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
              Fin.ext (by dsimp; omega)
            simpa [heq] using hb 96 (by decide) h4 ⟨r.val - 96, hk⟩
          · by_cases c5 : r.val < 144
            · have hk : r.val - 120 < 24 := by omega
              have heq : (⟨120 + (⟨r.val - 120, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                Fin.ext (by dsimp; omega)
              simpa [heq] using hb 120 (by decide) h5 ⟨r.val - 120, hk⟩
            · by_cases c6 : r.val < 168
              · have hk : r.val - 144 < 24 := by omega
                have heq : (⟨144 + (⟨r.val - 144, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                  Fin.ext (by dsimp; omega)
                simpa [heq] using hb 144 (by decide) h6 ⟨r.val - 144, hk⟩
              · by_cases c7 : r.val < 192
                · have hk : r.val - 168 < 24 := by omega
                  have heq : (⟨168 + (⟨r.val - 168, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                    Fin.ext (by dsimp; omega)
                  simpa [heq] using hb 168 (by decide) h7 ⟨r.val - 168, hk⟩
                · by_cases c8 : r.val < 216
                  · have hk : r.val - 192 < 24 := by omega
                    have heq :
                        (⟨192 + (⟨r.val - 192, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                      Fin.ext (by dsimp; omega)
                    simpa [heq] using hb 192 (by decide) h8 ⟨r.val - 192, hk⟩
                  · have hk : r.val - 216 < 24 := by omega
                    have heq :
                        (⟨216 + (⟨r.val - 216, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                      Fin.ext (by dsimp; omega)
                    simpa [heq] using hb 216 (by decide) h9 ⟨r.val - 216, hk⟩

private theorem eq_zero_of_cartan8_eigenvector
    (x : SplitE8Lie) (w : Fin 8 → ℤ)
    (hw_eig : ∀ a : Fin 8, ⁅cartan8 a, x⁆ = (w a : ℝ) • x)
    (hw_ne0 : ∃ a : Fin 8, w a ≠ 0)
    (hw_not_root : ∀ r : Fin 240, ∃ a : Fin 8, w a ≠ cartan8Weight r a) : x = 0 := by
  have hrep := splitE8Cartan8Basis.sum_repr x
  rw [Fintype.sum_sum_type] at hrep
  simp only [splitE8Cartan8Basis_inl, splitE8Cartan8Basis_inr] at hrep
  let hpart := ∑ a : Fin 8, (splitE8Cartan8Basis.repr x) (Sum.inl a) • cartan8 a
  have hh_mem : hpart ∈ splitE8Cartan :=
    Submodule.sum_mem _ fun a _ => splitE8Cartan.smul_mem _ (cartan8_mem_splitE8Cartan a)
  have hc0 : ∀ a : Fin 8,
      ⁅cartan8 a, x⁆ = ∑ r : Fin 240, ((splitE8Cartan8Basis.repr x) (Sum.inr r) *
        (cartan8Weight r a : ℝ)) • e8RootVec r := by
    intro a
    conv_lhs => rw [← hrep]
    have hk : ⁅cartan8 a, hpart⁆ = 0 := by
      have hc := (inferInstance : IsLieAbelian splitE8Cartan).trivial
        ⟨cartan8 a, cartan8_mem_splitE8Cartan a⟩ ⟨hpart, hh_mem⟩
      exact congrArg Subtype.val hc
    rw [lie_add, hk, zero_add, lie_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [lie_smul, e8RootVec_bracket_cartan8, smul_smul]
  have hr_zero : ∀ r : Fin 240, (splitE8Cartan8Basis.repr x) (Sum.inr r) = 0 := by
    intro r
    obtain ⟨a, ha⟩ := hw_not_root r
    let lam : ℝ := (w a : ℝ)
    have hdiff : lam • hpart + ∑ q : Fin 240, (splitE8Cartan8Basis.repr x (Sum.inr q) *
        (lam - (cartan8Weight q a : ℝ))) • e8RootVec q = 0 := by
      have heq : lam • x - ⁅cartan8 a, x⁆ = 0 := by
        rw [hw_eig a, sub_self]
      have h1 : lam • x = lam • hpart + ∑ q : Fin 240,
          lam • ((splitE8Cartan8Basis.repr x) (Sum.inr q) • e8RootVec q) := by
        conv_lhs => rw [← hrep]
        rw [smul_add]
        congr 1
        rw [Finset.smul_sum]
      rw [h1, hc0 a] at heq
      have hsub : lam • hpart + ∑ q : Fin 240, lam • (splitE8Cartan8Basis.repr x (Sum.inr q) •
          e8RootVec q) - ∑ q : Fin 240, (splitE8Cartan8Basis.repr x (Sum.inr q) *
          (cartan8Weight q a : ℝ)) • e8RootVec q =
        lam • hpart + ∑ q : Fin 240, (splitE8Cartan8Basis.repr x (Sum.inr q) *
          (lam - (cartan8Weight q a : ℝ))) • e8RootVec q := by
        rw [add_sub_assoc, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_smul, ← sub_smul]
        congr 1; ring
      rw [← heq]
      exact hsub.symm
    have hkill := e8_cartan_weight_kill_mem ⊥
      (fun _ y hy => by rw [Submodule.mem_bot] at hy; subst hy; simp)
      Finset.univ (lam • hpart) (splitE8Cartan.smul_mem lam hh_mem)
      (fun q => splitE8Cartan8Basis.repr x (Sum.inr q) * (lam - (cartan8Weight q a : ℝ)))
      (by rw [hdiff]; exact Submodule.zero_mem _)
    have hr' := (Submodule.mem_bot ℝ).mp (hkill.2 r (Finset.mem_univ r))
    have hmul := (smul_eq_zero.mp hr').resolve_right (e8RootVec_ne_zero r)
    have hlam_ne : lam - (cartan8Weight r a : ℝ) ≠ 0 := by
      intro h0
      apply ha
      exact Int.cast_injective (sub_eq_zero.mp h0)
    exact (mul_eq_zero.mp hmul).resolve_right hlam_ne
  have hs0 : ∑ r : Fin 240, splitE8Cartan8Basis.repr x (Sum.inr r) • e8RootVec r = 0 :=
    Finset.sum_eq_zero fun r _ => by rw [hr_zero r, zero_smul]
  have hx_cartan : x = hpart := by rw [← hrep, hs0, add_zero]
  obtain ⟨a₀, ha₀⟩ := hw_ne0
  have hbr0 : ⁅cartan8 a₀, x⁆ = 0 := by
    rw [hx_cartan]
    have hc := (inferInstance : IsLieAbelian splitE8Cartan).trivial
      ⟨cartan8 a₀, cartan8_mem_splitE8Cartan a₀⟩ ⟨hpart, hh_mem⟩
    exact congrArg Subtype.val hc
  rw [hw_eig a₀] at hbr0
  exact (smul_eq_zero.mp hbr0).resolve_left (Int.cast_ne_zero.mpr ha₀)

private theorem cartan8_bracket_iterate_e8RootVec
    (n : ℕ) (r₁ r₂ : Fin 240) (a : Fin 8) :
    ⁅cartan8 a, Nat.iterate (fun x => ⁅e8RootVec r₁, x⁆) n (e8RootVec r₂)⁆ =
      (((n : ℤ) * cartan8Weight r₁ a + cartan8Weight r₂ a : ℤ) : ℝ) •
        Nat.iterate (fun x => ⁅e8RootVec r₁, x⁆) n (e8RootVec r₂) := by
  induction n with
  | zero => simpa using e8RootVec_bracket_cartan8 a r₂
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [leibniz_lie, e8RootVec_bracket_cartan8, ih, smul_lie, lie_smul, ← add_smul]
    congr 1; push_cast; ring

private theorem iterate_bracket_smul
    (c₁ c₂ : ℝ) (u v : SplitE8Lie) (n : ℕ) :
    Nat.iterate (fun x => ⁅c₁ • u, x⁆) n (c₂ • v) =
      (c₁ ^ n * c₂) • Nat.iterate (fun x => ⁅u, x⁆) n v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, smul_lie, lie_smul, smul_smul,
      Function.iterate_succ_apply']
    congr 1; ring

private theorem e8ESimpleIdx_serre_weight_ne_zero {i j : Fin 8} (hij : i ≠ j) :
    ∃ a : Fin 8,
      ((1 - Tag.cartan .E8 i j).toNat : ℤ) * cartan8Weight (e8ESimpleIdx i) a +
        cartan8Weight (e8ESimpleIdx j) a ≠ 0 := by
  have hchk : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      if i == j then true
      else (List.finRange 8).any (fun a =>
        ((1 - Tag.cartan .E8 i j).toNat : ℤ) * cartan8Weight (e8ESimpleIdx i) a +
          cartan8Weight (e8ESimpleIdx j) a != 0))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hij' := hchk i j
  have hne : (i == j) = false := beq_false_of_ne hij
  simp only [hne, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, List.mem_finRange,
    true_and, bne_iff_ne, ne_eq] at hij'
  exact hij'

private theorem e8ESimpleIdx_serre_weight_not_mem_range {i j : Fin 8} (hij : i ≠ j) :
    ∀ r : Fin 240, ∃ a : Fin 8,
      ((1 - Tag.cartan .E8 i j).toNat : ℤ) * cartan8Weight (e8ESimpleIdx i) a +
        cartan8Weight (e8ESimpleIdx j) a ≠ cartan8Weight r a := by
  intro r
  have hchk := forall_fin240_of_blocks
    (fun r => (List.finRange 8).all fun i => (List.finRange 8).all fun j =>
      if i == j then true
      else (List.finRange 8).any fun a =>
        ((1 - Tag.cartan .E8 i j).toNat : ℤ) * cartan8Weight (e8ESimpleIdx i) a +
          cartan8Weight (e8ESimpleIdx j) a != cartan8Weight r a)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) r
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hij' := hchk i j
  have hne : (i == j) = false := beq_false_of_ne hij
  simp only [hne, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, List.mem_finRange,
    true_and, bne_iff_ne, ne_eq] at hij'
  exact hij'

private theorem e8RootNeg_e8ESimpleIdx (i : Fin 8) :
    e8RootNeg (e8ESimpleIdx i) = e8FSimpleIdx i := by
  fin_cases i <;> decide

/-- Positive Serre relations `ad (e8SimpleE i) ^ (1 - C_{ij}) (e8SimpleE j) = 0`
in `SplitE8Lie`. -/
theorem e8Simple_serre_E {i j : Fin 8} (hij : i ≠ j) :
    (Nat.iterate (fun x => ⁅e8SimpleE i, x⁆)
      (1 - Tag.cartan .E8 i j).toNat) (e8SimpleE j) = 0 := by
  simp only [e8SimpleE_eq_rootVec]
  exact eq_zero_of_cartan8_eigenvector _ _
    (cartan8_bracket_iterate_e8RootVec _ (e8ESimpleIdx i) (e8ESimpleIdx j))
    (e8ESimpleIdx_serre_weight_ne_zero hij)
    (e8ESimpleIdx_serre_weight_not_mem_range hij)

/-- Negative Serre relations `ad (e8SimpleF i) ^ (1 - C_{ij}) (e8SimpleF j) = 0`
in `SplitE8Lie`. -/
theorem e8Simple_serre_F {i j : Fin 8} (hij : i ≠ j) :
    (Nat.iterate (fun x => ⁅e8SimpleF i, x⁆)
      (1 - Tag.cartan .E8 i j).toNat) (e8SimpleF j) = 0 := by
  simp only [e8SimpleF_eq_rootVec, iterate_bracket_smul]
  suffices h0 : (Nat.iterate (fun x => ⁅e8RootVec (e8FSimpleIdx i), x⁆)
      (1 - Tag.cartan .E8 i j).toNat) (e8RootVec (e8FSimpleIdx j)) = 0 by
    rw [h0, smul_zero]
  refine eq_zero_of_cartan8_eigenvector _ _
    (cartan8_bracket_iterate_e8RootVec _ (e8FSimpleIdx i) (e8FSimpleIdx j)) ?_ ?_
  · obtain ⟨a, ha⟩ := e8ESimpleIdx_serre_weight_ne_zero hij
    refine ⟨a, ?_⟩
    rw [← e8RootNeg_e8ESimpleIdx i, ← e8RootNeg_e8ESimpleIdx j,
      cartan8Weight_neg, cartan8Weight_neg]
    simp only [Pi.neg_apply]
    intro h0
    apply ha
    linarith
  · intro r
    obtain ⟨a, ha⟩ := e8ESimpleIdx_serre_weight_not_mem_range hij (e8RootNeg r)
    refine ⟨a, ?_⟩
    rw [← e8RootNeg_e8ESimpleIdx i, ← e8RootNeg_e8ESimpleIdx j,
      cartan8Weight_neg, cartan8Weight_neg]
    have hnr := congrFun (cartan8Weight_neg r) a
    simp only [Pi.neg_apply] at hnr ⊢
    intro h0
    apply ha
    linarith

/-- Evaluate the eight Cartan, positive-root, and negative-root generators in `SplitE8Lie`. -/
def splitE8SerreGenerator (g : CartanMatrix.Generators (Fin 8)) : SplitE8Lie :=
  match g with
  | .H i => e8SimpleH i
  | .E i => e8SimpleE i
  | .F i => e8SimpleF i

/-- The universal Lie homomorphism from the free Lie algebra on the E₈ Serre generators
to `SplitE8Lie`. -/
def splitE8FreeSerreEval :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 8)) →ₗ⁅ℝ⁆ SplitE8Lie :=
  FreeLieAlgebra.lift ℝ splitE8SerreGenerator

@[simp] theorem splitE8FreeSerreEval_H (i : Fin 8) :
    splitE8FreeSerreEval (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = e8SimpleH i := by
  simp [splitE8FreeSerreEval, splitE8SerreGenerator]

@[simp] theorem splitE8FreeSerreEval_E (i : Fin 8) :
    splitE8FreeSerreEval (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)) = e8SimpleE i := by
  simp [splitE8FreeSerreEval, splitE8SerreGenerator]

@[simp] theorem splitE8FreeSerreEval_F (i : Fin 8) :
    splitE8FreeSerreEval (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)) = e8SimpleF i := by
  simp [splitE8FreeSerreEval, splitE8SerreGenerator]

private theorem map_iterate_ad {R L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (x y : L) (n : ℕ) :
    f (Nat.iterate (fun z => ⁅x, z⁆) n y) =
      Nat.iterate (fun z => ⁅f x, z⁆) n (f y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', LieHom.map_lie, ih]

private theorem ad_pow_apply_eq_iterate {R L : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] (x y : L) (n : ℕ) :
    ((LieAlgebra.ad R L x) ^ n) y = Nat.iterate (fun z => ⁅x, z⁆) n y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (LieAlgebra.ad R L x) (((LieAlgebra.ad R L x) ^ n) y) = _
    rw [ih]
    simp only [LieAlgebra.ad_apply, Function.iterate_succ_apply']

private theorem e8_serre_exponent {i j : Fin 8} (hij : i ≠ j) :
    (-CartanMatrix.E 8 i j).toNat + 1 = (1 - CartanMatrix.E 8 i j).toNat := by
  have hle := CartanMatrix.E_off_diag_nonpos 8 i j hij
  omega

/-- The free-Lie evaluation kills the Cartan commutation relations. -/
theorem splitE8FreeSerreEval_HH (i j : Fin 8) :
    splitE8FreeSerreEval (CartanMatrix.Relations.HH ℝ (i, j)) = 0 := by
  change splitE8FreeSerreEval
    ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H j)⁆ = 0
  rw [LieHom.map_lie, splitE8FreeSerreEval_H, splitE8FreeSerreEval_H]
  exact e8SimpleH_comm i j

/-- The free-Lie evaluation kills the `[E, F]` relations. -/
theorem splitE8FreeSerreEval_EF (i j : Fin 8) :
    splitE8FreeSerreEval (CartanMatrix.Relations.EF ℝ (i, j)) = 0 := by
  by_cases hij : i = j
  · subst j
    simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, ↓reduceIte]
    change splitE8FreeSerreEval
      (⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)⁆ -
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = 0
    rw [map_sub, LieHom.map_lie, splitE8FreeSerreEval_E,
      splitE8FreeSerreEval_F, splitE8FreeSerreEval_H, e8Simple_bracket_EF_same]
    simp
  · simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, hij, ↓reduceIte]
    change splitE8FreeSerreEval
      ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F j)⁆ = 0
    rw [LieHom.map_lie, splitE8FreeSerreEval_E, splitE8FreeSerreEval_F]
    exact e8Simple_bracket_EF_ne hij

/-- The free-Lie evaluation kills the `[H, E]` relations. -/
theorem splitE8FreeSerreEval_HE (i j : Fin 8) :
    splitE8FreeSerreEval (CartanMatrix.Relations.HE ℝ (CartanMatrix.E 8) (i, j)) = 0 := by
  simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ, map_sub, LieHom.map_lie, splitE8FreeSerreEval_H,
    splitE8FreeSerreEval_E, map_smul, splitE8FreeSerreEval_E, e8Simple_bracket_HE]
  have hentry := congrFun (congrFun splitE8_cartan_eq_mathlib i) j
  rw [← congrArg (fun z : ℤ => (z : ℝ)) hentry]
  simp

/-- The free-Lie evaluation kills the `[H, F]` relations. -/
theorem splitE8FreeSerreEval_HF (i j : Fin 8) :
    splitE8FreeSerreEval (CartanMatrix.Relations.HF ℝ (CartanMatrix.E 8) (i, j)) = 0 := by
  simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ, map_add, LieHom.map_lie, splitE8FreeSerreEval_H,
    splitE8FreeSerreEval_F, map_smul, splitE8FreeSerreEval_F, e8Simple_bracket_HF]
  have hentry := congrFun (congrFun splitE8_cartan_eq_mathlib i) j
  rw [← congrArg (fun z : ℤ => (z : ℝ)) hentry]
  simp

/-- The free-Lie evaluation kills the positive-root Serre relations. -/
theorem splitE8FreeSerreEval_adE (i j : Fin 8) :
    splitE8FreeSerreEval (CartanMatrix.Relations.adE ℝ (CartanMatrix.E 8) (i, j)) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [CartanMatrix.Relations.adE, Function.uncurry_apply_pair]
  · simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply]
    rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
      splitE8FreeSerreEval_E, splitE8FreeSerreEval_E, ← Function.iterate_succ_apply,
      Nat.succ_eq_add_one, e8_serre_exponent hij, ← splitE8_cartan_eq_mathlib]
    exact e8Simple_serre_E hij

/-- The free-Lie evaluation kills the negative-root Serre relations. -/
theorem splitE8FreeSerreEval_adF (i j : Fin 8) :
    splitE8FreeSerreEval (CartanMatrix.Relations.adF ℝ (CartanMatrix.E 8) (i, j)) = 0 := by
  by_cases hij : i = j
  · subst j
    simp [CartanMatrix.Relations.adF, Function.uncurry_apply_pair]
  · simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply]
    rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie,
      splitE8FreeSerreEval_F, splitE8FreeSerreEval_F, ← Function.iterate_succ_apply,
      Nat.succ_eq_add_one, e8_serre_exponent hij, ← splitE8_cartan_eq_mathlib]
    exact e8Simple_serre_F hij

/-- The evaluation kernel contains the full E₈ Cartan--Serre ideal. -/
theorem splitE8FreeSerreEval_serreIdeal :
    CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8) ≤ splitE8FreeSerreEval.ker := by
  classical
  rw [CartanMatrix.Relations.toIdeal, LieSubmodule.lieSpan_le]
  intro x hx
  simp only [CartanMatrix.Relations.toSet, Set.mem_union, Set.mem_range] at hx
  rcases hx with (((((⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) |
      ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
  · exact splitE8FreeSerreEval_HH i j
  · exact splitE8FreeSerreEval_EF i j
  · exact splitE8FreeSerreEval_HE i j
  · exact splitE8FreeSerreEval_HF i j
  · exact splitE8FreeSerreEval_adE i j
  · exact splitE8FreeSerreEval_adF i j

private theorem splitE8FreeSerreEval_serreIdeal_submodule :
    (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8)).toSubmodule ≤
      LinearMap.ker splitE8FreeSerreEval.toLinearMap :=
  splitE8FreeSerreEval_serreIdeal

/-- The descended Serre quotient homomorphism `LieAlgebra.e₈ ℝ →ₗ⁅ℝ⁆ SplitE8Lie`. -/
noncomputable def splitE8SerreQuotientMap :
    LieAlgebra.e₈ ℝ →ₗ⁅ℝ⁆ SplitE8Lie := by
  let I := CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8)
  have hI : I.toSubmodule ≤ LinearMap.ker splitE8FreeSerreEval.toLinearMap :=
    splitE8FreeSerreEval_serreIdeal
  refine
    { I.toSubmodule.liftQ splitE8FreeSerreEval.toLinearMap hI with
      map_lie' := ?_ }
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change splitE8FreeSerreEval ⁅x, y⁆ =
        ⁅splitE8FreeSerreEval x, splitE8FreeSerreEval y⁆
      exact LieHom.map_lie splitE8FreeSerreEval x y

@[simp] theorem splitE8SerreQuotientMap_H (i : Fin 8) :
    splitE8SerreQuotientMap
      (Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i))) =
        e8SimpleH i := by
  change (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8)).toSubmodule.liftQ
    splitE8FreeSerreEval.toLinearMap splitE8FreeSerreEval_serreIdeal_submodule
    (Submodule.Quotient.mk _) = _
  simp [splitE8FreeSerreEval_H]

@[simp] theorem splitE8SerreQuotientMap_E (i : Fin 8) :
    splitE8SerreQuotientMap
      (Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i))) =
        e8SimpleE i := by
  change (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8)).toSubmodule.liftQ
    splitE8FreeSerreEval.toLinearMap splitE8FreeSerreEval_serreIdeal_submodule
    (Submodule.Quotient.mk _) = _
  simp [splitE8FreeSerreEval_E]

@[simp] theorem splitE8SerreQuotientMap_F (i : Fin 8) :
    splitE8SerreQuotientMap
      (Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i))) =
        e8SimpleF i := by
  change (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8)).toSubmodule.liftQ
    splitE8FreeSerreEval.toLinearMap splitE8FreeSerreEval_serreIdeal_submodule
    (Submodule.Quotient.mk _) = _
  simp [splitE8FreeSerreEval_F]

/-! ## 2. Canonical `Fin 120` Positive Root Table and Generator Spanning in `SplitE8Lie` -/

private theorem forall_fin120_of_blocks (P : Fin 120 → Bool)
    (h0 : (List.finRange 24).all (fun k => P ⟨0 + k.val, by omega⟩) = true)
    (h1 : (List.finRange 24).all (fun k => P ⟨24 + k.val, by omega⟩) = true)
    (h2 : (List.finRange 24).all (fun k => P ⟨48 + k.val, by omega⟩) = true)
    (h3 : (List.finRange 24).all (fun k => P ⟨72 + k.val, by omega⟩) = true)
    (h4 : (List.finRange 24).all (fun k => P ⟨96 + k.val, by omega⟩) = true)
    (p : Fin 120) : P p = true := by
  have hb : ∀ (off : ℕ) (hoff : off + 24 ≤ 120),
      (List.finRange 24).all (fun k => P ⟨off + k.val, by omega⟩) = true →
      ∀ k : Fin 24, P ⟨off + k.val, by omega⟩ = true := by
    intro off hoff hchk k
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
    exact hchk k
  by_cases c0 : p.val < 24
  · have heq : (⟨0 + (⟨p.val, c0⟩ : Fin 24).val, by omega⟩ : Fin 120) = p :=
      Fin.ext (by dsimp; omega)
    simpa [heq] using hb 0 (by decide) h0 ⟨p.val, c0⟩
  · by_cases c1 : p.val < 48
    · have hk : p.val - 24 < 24 := by omega
      have heq : (⟨24 + (⟨p.val - 24, hk⟩ : Fin 24).val, by omega⟩ : Fin 120) = p :=
        Fin.ext (by dsimp; omega)
      simpa [heq] using hb 24 (by decide) h1 ⟨p.val - 24, hk⟩
    · by_cases c2 : p.val < 72
      · have hk : p.val - 48 < 24 := by omega
        have heq : (⟨48 + (⟨p.val - 48, hk⟩ : Fin 24).val, by omega⟩ : Fin 120) = p :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using hb 48 (by decide) h2 ⟨p.val - 48, hk⟩
      · by_cases c3 : p.val < 96
        · have hk : p.val - 72 < 24 := by omega
          have heq : (⟨72 + (⟨p.val - 72, hk⟩ : Fin 24).val, by omega⟩ : Fin 120) = p :=
            Fin.ext (by dsimp; omega)
          simpa [heq] using hb 72 (by decide) h3 ⟨p.val - 72, hk⟩
        · have hk : p.val - 96 < 24 := by omega
          have heq : (⟨96 + (⟨p.val - 96, hk⟩ : Fin 24).val, by omega⟩ : Fin 120) = p :=
            Fin.ext (by dsimp; omega)
          simpa [heq] using hb 96 (by decide) h4 ⟨p.val - 96, hk⟩

private theorem forall_fin8_fin120_of_blocks (P : Fin 8 → Fin 120 → Bool)
    (h0 : (List.finRange 8).all
      (fun i => (List.finRange 24).all fun k => P i ⟨0 + k.val, by omega⟩) = true)
    (h1 : (List.finRange 8).all
      (fun i => (List.finRange 24).all fun k => P i ⟨24 + k.val, by omega⟩) = true)
    (h2 : (List.finRange 8).all
      (fun i => (List.finRange 24).all fun k => P i ⟨48 + k.val, by omega⟩) = true)
    (h3 : (List.finRange 8).all
      (fun i => (List.finRange 24).all fun k => P i ⟨72 + k.val, by omega⟩) = true)
    (h4 : (List.finRange 8).all
      (fun i => (List.finRange 24).all fun k => P i ⟨96 + k.val, by omega⟩) = true)
    (i : Fin 8) (p : Fin 120) : P i p = true := by
  apply forall_fin120_of_blocks (P i)
  · exact List.all_eq_true.mp h0 i (List.mem_finRange i)
  · exact List.all_eq_true.mp h1 i (List.mem_finRange i)
  · exact List.all_eq_true.mp h2 i (List.mem_finRange i)
  · exact List.all_eq_true.mp h3 i (List.mem_finRange i)
  · exact List.all_eq_true.mp h4 i (List.mem_finRange i)

private def simplePosIdx (i : Fin 8) : Fin 120 := ⟨i.val, by omega⟩

private def simpleOfPos (p : Fin 120) : Fin 8 := ⟨p.val % 8, by omega⟩

private def e8PosRoot (p : Fin 120) : Fin 240 :=
  match p.val with
  | 0 => ⟨67, by decide⟩ | 1 => ⟨41, by decide⟩ | 2 => ⟨26, by decide⟩ | 3 => ⟨37, by decide⟩ | 4 => ⟨42, by decide⟩ | 5 => ⟨121, by decide⟩
  | 6 => ⟨3, by decide⟩ | 7 => ⟨4, by decide⟩ | 8 => ⟨75, by decide⟩ | 9 => ⟨38, by decide⟩ | 10 => ⟨25, by decide⟩ | 11 => ⟨43, by decide⟩
  | 12 => ⟨125, by decide⟩ | 13 => ⟨145, by decide⟩ | 14 => ⟨2, by decide⟩ | 15 => ⟨77, by decide⟩ | 16 => ⟨35, by decide⟩ | 17 => ⟨44, by decide⟩
  | 18 => ⟨27, by decide⟩ | 19 => ⟨126, by decide⟩ | 20 => ⟨149, by decide⟩ | 21 => ⟨97, by decide⟩ | 22 => ⟨65, by decide⟩ | 23 => ⟨79, by decide⟩
  | 24 => ⟨39, by decide⟩ | 25 => ⟨127, by decide⟩ | 26 => ⟨120, by decide⟩ | 27 => ⟨150, by decide⟩ | 28 => ⟨101, by decide⟩ | 29 => ⟨71, by decide⟩
  | 30 => ⟨137, by decide⟩ | 31 => ⟨36, by decide⟩ | 32 => ⟨123, by decide⟩ | 33 => ⟨151, by decide⟩ | 34 => ⟨144, by decide⟩ | 35 => ⟨102, by decide⟩
  | 36 => ⟨69, by decide⟩ | 37 => ⟨141, by decide⟩ | 38 => ⟨161, by decide⟩ | 39 => ⟨122, by decide⟩ | 40 => ⟨147, by decide⟩ | 41 => ⟨103, by decide⟩
  | 42 => ⟨96, by decide⟩ | 43 => ⟨73, by decide⟩ | 44 => ⟨142, by decide⟩ | 45 => ⟨165, by decide⟩ | 46 => ⟨113, by decide⟩ | 47 => ⟨124, by decide⟩
  | 48 => ⟨146, by decide⟩ | 49 => ⟨99, by decide⟩ | 50 => ⟨143, by decide⟩ | 51 => ⟨136, by decide⟩ | 52 => ⟨166, by decide⟩ | 53 => ⟨117, by decide⟩
  | 54 => ⟨148, by decide⟩ | 55 => ⟨98, by decide⟩ | 56 => ⟨139, by decide⟩ | 57 => ⟨167, by decide⟩ | 58 => ⟨160, by decide⟩ | 59 => ⟨118, by decide⟩
  | 60 => ⟨17, by decide⟩ | 61 => ⟨100, by decide⟩ | 62 => ⟨138, by decide⟩ | 63 => ⟨163, by decide⟩ | 64 => ⟨119, by decide⟩ | 65 => ⟨177, by decide⟩
  | 66 => ⟨112, by decide⟩ | 67 => ⟨23, by decide⟩ | 68 => ⟨140, by decide⟩ | 69 => ⟨162, by decide⟩ | 70 => ⟨181, by decide⟩ | 71 => ⟨115, by decide⟩
  | 72 => ⟨225, by decide⟩ | 73 => ⟨20, by decide⟩ | 74 => ⟨164, by decide⟩ | 75 => ⟨182, by decide⟩ | 76 => ⟨114, by decide⟩ | 77 => ⟨229, by decide⟩
  | 78 => ⟨201, by decide⟩ | 79 => ⟨176, by decide⟩ | 80 => ⟨116, by decide⟩ | 81 => ⟨183, by decide⟩ | 82 => ⟨230, by decide⟩ | 83 => ⟨205, by decide⟩
  | 84 => ⟨179, by decide⟩ | 85 => ⟨224, by decide⟩ | 86 => ⟨231, by decide⟩ | 87 => ⟨206, by decide⟩ | 88 => ⟨178, by decide⟩ | 89 => ⟨227, by decide⟩
  | 90 => ⟨200, by decide⟩ | 91 => ⟨207, by decide⟩ | 92 => ⟨180, by decide⟩ | 93 => ⟨226, by decide⟩ | 94 => ⟨203, by decide⟩ | 95 => ⟨83, by decide⟩
  | 96 => ⟨16, by decide⟩ | 97 => ⟨228, by decide⟩ | 98 => ⟨202, by decide⟩ | 99 => ⟨91, by decide⟩ | 100 => ⟨22, by decide⟩ | 101 => ⟨204, by decide⟩
  | 102 => ⟨93, by decide⟩ | 103 => ⟨19, by decide⟩ | 104 => ⟨95, by decide⟩ | 105 => ⟨81, by decide⟩ | 106 => ⟨50, by decide⟩ | 107 => ⟨87, by decide⟩
  | 108 => ⟨58, by decide⟩ | 109 => ⟨85, by decide⟩ | 110 => ⟨60, by decide⟩ | 111 => ⟨89, by decide⟩ | 112 => ⟨62, by decide⟩ | 113 => ⟨48, by decide⟩
  | 114 => ⟨54, by decide⟩ | 115 => ⟨52, by decide⟩ | 116 => ⟨56, by decide⟩ | 117 => ⟨9, by decide⟩ | 118 => ⟨12, by decide⟩ | _ => ⟨6, by decide⟩

private def e8Fin240ToPos (r : Fin 240) : Fin 120 :=
  match r.val with
  | 0 => ⟨0, by decide⟩ | 1 => ⟨0, by decide⟩ | 2 => ⟨14, by decide⟩ | 3 => ⟨6, by decide⟩ | 4 => ⟨7, by decide⟩ | 5 => ⟨0, by decide⟩
  | 6 => ⟨119, by decide⟩ | 7 => ⟨0, by decide⟩ | 8 => ⟨0, by decide⟩ | 9 => ⟨117, by decide⟩ | 10 => ⟨0, by decide⟩ | 11 => ⟨0, by decide⟩
  | 12 => ⟨118, by decide⟩ | 13 => ⟨0, by decide⟩ | 14 => ⟨0, by decide⟩ | 15 => ⟨0, by decide⟩ | 16 => ⟨96, by decide⟩ | 17 => ⟨60, by decide⟩
  | 18 => ⟨0, by decide⟩ | 19 => ⟨103, by decide⟩ | 20 => ⟨73, by decide⟩ | 21 => ⟨0, by decide⟩ | 22 => ⟨100, by decide⟩ | 23 => ⟨67, by decide⟩
  | 24 => ⟨0, by decide⟩ | 25 => ⟨10, by decide⟩ | 26 => ⟨2, by decide⟩ | 27 => ⟨18, by decide⟩ | 28 => ⟨0, by decide⟩ | 29 => ⟨0, by decide⟩
  | 30 => ⟨0, by decide⟩ | 31 => ⟨0, by decide⟩ | 32 => ⟨0, by decide⟩ | 33 => ⟨0, by decide⟩ | 34 => ⟨0, by decide⟩ | 35 => ⟨16, by decide⟩
  | 36 => ⟨31, by decide⟩ | 37 => ⟨3, by decide⟩ | 38 => ⟨9, by decide⟩ | 39 => ⟨24, by decide⟩ | 40 => ⟨0, by decide⟩ | 41 => ⟨1, by decide⟩
  | 42 => ⟨4, by decide⟩ | 43 => ⟨11, by decide⟩ | 44 => ⟨17, by decide⟩ | 45 => ⟨0, by decide⟩ | 46 => ⟨0, by decide⟩ | 47 => ⟨0, by decide⟩
  | 48 => ⟨113, by decide⟩ | 49 => ⟨0, by decide⟩ | 50 => ⟨106, by decide⟩ | 51 => ⟨0, by decide⟩ | 52 => ⟨115, by decide⟩ | 53 => ⟨0, by decide⟩
  | 54 => ⟨114, by decide⟩ | 55 => ⟨0, by decide⟩ | 56 => ⟨116, by decide⟩ | 57 => ⟨0, by decide⟩ | 58 => ⟨108, by decide⟩ | 59 => ⟨0, by decide⟩
  | 60 => ⟨110, by decide⟩ | 61 => ⟨0, by decide⟩ | 62 => ⟨112, by decide⟩ | 63 => ⟨0, by decide⟩ | 64 => ⟨0, by decide⟩ | 65 => ⟨22, by decide⟩
  | 66 => ⟨0, by decide⟩ | 67 => ⟨0, by decide⟩ | 68 => ⟨0, by decide⟩ | 69 => ⟨36, by decide⟩ | 70 => ⟨0, by decide⟩ | 71 => ⟨29, by decide⟩
  | 72 => ⟨0, by decide⟩ | 73 => ⟨43, by decide⟩ | 74 => ⟨0, by decide⟩ | 75 => ⟨8, by decide⟩ | 76 => ⟨0, by decide⟩ | 77 => ⟨15, by decide⟩
  | 78 => ⟨0, by decide⟩ | 79 => ⟨23, by decide⟩ | 80 => ⟨0, by decide⟩ | 81 => ⟨105, by decide⟩ | 82 => ⟨0, by decide⟩ | 83 => ⟨95, by decide⟩
  | 84 => ⟨0, by decide⟩ | 85 => ⟨109, by decide⟩ | 86 => ⟨0, by decide⟩ | 87 => ⟨107, by decide⟩ | 88 => ⟨0, by decide⟩ | 89 => ⟨111, by decide⟩
  | 90 => ⟨0, by decide⟩ | 91 => ⟨99, by decide⟩ | 92 => ⟨0, by decide⟩ | 93 => ⟨102, by decide⟩ | 94 => ⟨0, by decide⟩ | 95 => ⟨104, by decide⟩
  | 96 => ⟨42, by decide⟩ | 97 => ⟨21, by decide⟩ | 98 => ⟨55, by decide⟩ | 99 => ⟨49, by decide⟩ | 100 => ⟨61, by decide⟩ | 101 => ⟨28, by decide⟩
  | 102 => ⟨35, by decide⟩ | 103 => ⟨41, by decide⟩ | 104 => ⟨0, by decide⟩ | 105 => ⟨0, by decide⟩ | 106 => ⟨0, by decide⟩ | 107 => ⟨0, by decide⟩
  | 108 => ⟨0, by decide⟩ | 109 => ⟨0, by decide⟩ | 110 => ⟨0, by decide⟩ | 111 => ⟨0, by decide⟩ | 112 => ⟨66, by decide⟩ | 113 => ⟨46, by decide⟩
  | 114 => ⟨76, by decide⟩ | 115 => ⟨71, by decide⟩ | 116 => ⟨80, by decide⟩ | 117 => ⟨53, by decide⟩ | 118 => ⟨59, by decide⟩ | 119 => ⟨64, by decide⟩
  | 120 => ⟨26, by decide⟩ | 121 => ⟨5, by decide⟩ | 122 => ⟨39, by decide⟩ | 123 => ⟨32, by decide⟩ | 124 => ⟨47, by decide⟩ | 125 => ⟨12, by decide⟩
  | 126 => ⟨19, by decide⟩ | 127 => ⟨25, by decide⟩ | 128 => ⟨0, by decide⟩ | 129 => ⟨0, by decide⟩ | 130 => ⟨0, by decide⟩ | 131 => ⟨0, by decide⟩
  | 132 => ⟨0, by decide⟩ | 133 => ⟨0, by decide⟩ | 134 => ⟨0, by decide⟩ | 135 => ⟨0, by decide⟩ | 136 => ⟨51, by decide⟩ | 137 => ⟨30, by decide⟩
  | 138 => ⟨62, by decide⟩ | 139 => ⟨56, by decide⟩ | 140 => ⟨68, by decide⟩ | 141 => ⟨37, by decide⟩ | 142 => ⟨44, by decide⟩ | 143 => ⟨50, by decide⟩
  | 144 => ⟨34, by decide⟩ | 145 => ⟨13, by decide⟩ | 146 => ⟨48, by decide⟩ | 147 => ⟨40, by decide⟩ | 148 => ⟨54, by decide⟩ | 149 => ⟨20, by decide⟩
  | 150 => ⟨27, by decide⟩ | 151 => ⟨33, by decide⟩ | 152 => ⟨0, by decide⟩ | 153 => ⟨0, by decide⟩ | 154 => ⟨0, by decide⟩ | 155 => ⟨0, by decide⟩
  | 156 => ⟨0, by decide⟩ | 157 => ⟨0, by decide⟩ | 158 => ⟨0, by decide⟩ | 159 => ⟨0, by decide⟩ | 160 => ⟨58, by decide⟩ | 161 => ⟨38, by decide⟩
  | 162 => ⟨69, by decide⟩ | 163 => ⟨63, by decide⟩ | 164 => ⟨74, by decide⟩ | 165 => ⟨45, by decide⟩ | 166 => ⟨52, by decide⟩ | 167 => ⟨57, by decide⟩
  | 168 => ⟨0, by decide⟩ | 169 => ⟨0, by decide⟩ | 170 => ⟨0, by decide⟩ | 171 => ⟨0, by decide⟩ | 172 => ⟨0, by decide⟩ | 173 => ⟨0, by decide⟩
  | 174 => ⟨0, by decide⟩ | 175 => ⟨0, by decide⟩ | 176 => ⟨79, by decide⟩ | 177 => ⟨65, by decide⟩ | 178 => ⟨88, by decide⟩ | 179 => ⟨84, by decide⟩
  | 180 => ⟨92, by decide⟩ | 181 => ⟨70, by decide⟩ | 182 => ⟨75, by decide⟩ | 183 => ⟨81, by decide⟩ | 184 => ⟨0, by decide⟩ | 185 => ⟨0, by decide⟩
  | 186 => ⟨0, by decide⟩ | 187 => ⟨0, by decide⟩ | 188 => ⟨0, by decide⟩ | 189 => ⟨0, by decide⟩ | 190 => ⟨0, by decide⟩ | 191 => ⟨0, by decide⟩
  | 192 => ⟨0, by decide⟩ | 193 => ⟨0, by decide⟩ | 194 => ⟨0, by decide⟩ | 195 => ⟨0, by decide⟩ | 196 => ⟨0, by decide⟩ | 197 => ⟨0, by decide⟩
  | 198 => ⟨0, by decide⟩ | 199 => ⟨0, by decide⟩ | 200 => ⟨90, by decide⟩ | 201 => ⟨78, by decide⟩ | 202 => ⟨98, by decide⟩ | 203 => ⟨94, by decide⟩
  | 204 => ⟨101, by decide⟩ | 205 => ⟨83, by decide⟩ | 206 => ⟨87, by decide⟩ | 207 => ⟨91, by decide⟩ | 208 => ⟨0, by decide⟩ | 209 => ⟨0, by decide⟩
  | 210 => ⟨0, by decide⟩ | 211 => ⟨0, by decide⟩ | 212 => ⟨0, by decide⟩ | 213 => ⟨0, by decide⟩ | 214 => ⟨0, by decide⟩ | 215 => ⟨0, by decide⟩
  | 216 => ⟨0, by decide⟩ | 217 => ⟨0, by decide⟩ | 218 => ⟨0, by decide⟩ | 219 => ⟨0, by decide⟩ | 220 => ⟨0, by decide⟩ | 221 => ⟨0, by decide⟩
  | 222 => ⟨0, by decide⟩ | 223 => ⟨0, by decide⟩ | 224 => ⟨85, by decide⟩ | 225 => ⟨72, by decide⟩ | 226 => ⟨93, by decide⟩ | 227 => ⟨89, by decide⟩
  | 228 => ⟨97, by decide⟩ | 229 => ⟨77, by decide⟩ | 230 => ⟨82, by decide⟩ | 231 => ⟨86, by decide⟩ | 232 => ⟨0, by decide⟩ | 233 => ⟨0, by decide⟩
  | 234 => ⟨0, by decide⟩ | 235 => ⟨0, by decide⟩ | 236 => ⟨0, by decide⟩ | 237 => ⟨0, by decide⟩ | 238 => ⟨0, by decide⟩ | _ => ⟨0, by decide⟩

private def e8PosHeight (p : Fin 120) : ℕ :=
  match p.val with
  | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1
  | 8 => 2 | 9 => 2 | 10 => 2 | 11 => 2 | 12 => 2 | 13 => 2 | 14 => 2 | 15 => 3
  | 16 => 3 | 17 => 3 | 18 => 3 | 19 => 3 | 20 => 3 | 21 => 3 | 22 => 4 | 23 => 4
  | 24 => 4 | 25 => 4 | 26 => 4 | 27 => 4 | 28 => 4 | 29 => 5 | 30 => 5 | 31 => 5
  | 32 => 5 | 33 => 5 | 34 => 5 | 35 => 5 | 36 => 6 | 37 => 6 | 38 => 6 | 39 => 6
  | 40 => 6 | 41 => 6 | 42 => 6 | 43 => 7 | 44 => 7 | 45 => 7 | 46 => 7 | 47 => 7
  | 48 => 7 | 49 => 7 | 50 => 8 | 51 => 8 | 52 => 8 | 53 => 8 | 54 => 8 | 55 => 8
  | 56 => 9 | 57 => 9 | 58 => 9 | 59 => 9 | 60 => 9 | 61 => 9 | 62 => 10 | 63 => 10
  | 64 => 10 | 65 => 10 | 66 => 10 | 67 => 10 | 68 => 11 | 69 => 11 | 70 => 11 | 71 => 11
  | 72 => 11 | 73 => 11 | 74 => 12 | 75 => 12 | 76 => 12 | 77 => 12 | 78 => 12 | 79 => 13
  | 80 => 13 | 81 => 13 | 82 => 13 | 83 => 13 | 84 => 14 | 85 => 14 | 86 => 14 | 87 => 14
  | 88 => 15 | 89 => 15 | 90 => 15 | 91 => 15 | 92 => 16 | 93 => 16 | 94 => 16 | 95 => 16
  | 96 => 17 | 97 => 17 | 98 => 17 | 99 => 17 | 100 => 18 | 101 => 18 | 102 => 18 | 103 => 19
  | 104 => 19 | 105 => 19 | 106 => 20 | 107 => 20 | 108 => 21 | 109 => 21 | 110 => 22 | 111 => 22
  | 112 => 23 | 113 => 23 | 114 => 24 | 115 => 25 | 116 => 26 | 117 => 27 | 118 => 28 | _ => 29

private def e8PosParent (p : Fin 120) : Option (Fin 8 × Fin 120) :=
  match p.val with
  | 8 => some (0, ⟨2, by decide⟩) | 9 => some (1, ⟨3, by decide⟩) | 10 => some (2, ⟨3, by decide⟩)
  | 11 => some (3, ⟨4, by decide⟩) | 12 => some (4, ⟨5, by decide⟩) | 13 => some (5, ⟨6, by decide⟩)
  | 14 => some (6, ⟨7, by decide⟩) | 15 => some (0, ⟨10, by decide⟩) | 16 => some (1, ⟨10, by decide⟩)
  | 17 => some (1, ⟨11, by decide⟩) | 18 => some (2, ⟨11, by decide⟩) | 19 => some (3, ⟨12, by decide⟩)
  | 20 => some (4, ⟨13, by decide⟩) | 21 => some (5, ⟨14, by decide⟩) | 22 => some (0, ⟨16, by decide⟩)
  | 23 => some (0, ⟨18, by decide⟩) | 24 => some (1, ⟨18, by decide⟩) | 25 => some (1, ⟨19, by decide⟩)
  | 26 => some (2, ⟨19, by decide⟩) | 27 => some (3, ⟨20, by decide⟩) | 28 => some (4, ⟨21, by decide⟩)
  | 29 => some (0, ⟨24, by decide⟩) | 30 => some (0, ⟨26, by decide⟩) | 31 => some (3, ⟨24, by decide⟩)
  | 32 => some (1, ⟨26, by decide⟩) | 33 => some (1, ⟨27, by decide⟩) | 34 => some (2, ⟨27, by decide⟩)
  | 35 => some (3, ⟨28, by decide⟩) | 36 => some (0, ⟨31, by decide⟩) | 37 => some (0, ⟨32, by decide⟩)
  | 38 => some (0, ⟨34, by decide⟩) | 39 => some (3, ⟨32, by decide⟩) | 40 => some (1, ⟨34, by decide⟩)
  | 41 => some (1, ⟨35, by decide⟩) | 42 => some (2, ⟨35, by decide⟩) | 43 => some (2, ⟨36, by decide⟩)
  | 44 => some (0, ⟨39, by decide⟩) | 45 => some (0, ⟨40, by decide⟩) | 46 => some (0, ⟨42, by decide⟩)
  | 47 => some (4, ⟨39, by decide⟩) | 48 => some (3, ⟨40, by decide⟩) | 49 => some (1, ⟨42, by decide⟩)
  | 50 => some (2, ⟨44, by decide⟩) | 51 => some (0, ⟨47, by decide⟩) | 52 => some (0, ⟨48, by decide⟩)
  | 53 => some (0, ⟨49, by decide⟩) | 54 => some (4, ⟨48, by decide⟩) | 55 => some (3, ⟨49, by decide⟩)
  | 56 => some (2, ⟨51, by decide⟩) | 57 => some (2, ⟨52, by decide⟩) | 58 => some (0, ⟨54, by decide⟩)
  | 59 => some (0, ⟨55, by decide⟩) | 60 => some (5, ⟨54, by decide⟩) | 61 => some (4, ⟨55, by decide⟩)
  | 62 => some (3, ⟨56, by decide⟩) | 63 => some (2, ⟨58, by decide⟩) | 64 => some (2, ⟨59, by decide⟩)
  | 65 => some (0, ⟨60, by decide⟩) | 66 => some (0, ⟨61, by decide⟩) | 67 => some (5, ⟨61, by decide⟩)
  | 68 => some (1, ⟨62, by decide⟩) | 69 => some (3, ⟨63, by decide⟩) | 70 => some (2, ⟨65, by decide⟩)
  | 71 => some (2, ⟨66, by decide⟩) | 72 => some (0, ⟨67, by decide⟩) | 73 => some (6, ⟨67, by decide⟩)
  | 74 => some (1, ⟨69, by decide⟩) | 75 => some (3, ⟨70, by decide⟩) | 76 => some (3, ⟨71, by decide⟩)
  | 77 => some (2, ⟨72, by decide⟩) | 78 => some (0, ⟨73, by decide⟩) | 79 => some (1, ⟨75, by decide⟩)
  | 80 => some (1, ⟨76, by decide⟩) | 81 => some (4, ⟨75, by decide⟩) | 82 => some (3, ⟨77, by decide⟩)
  | 83 => some (2, ⟨78, by decide⟩) | 84 => some (1, ⟨81, by decide⟩) | 85 => some (1, ⟨82, by decide⟩)
  | 86 => some (4, ⟨82, by decide⟩) | 87 => some (3, ⟨83, by decide⟩) | 88 => some (3, ⟨84, by decide⟩)
  | 89 => some (1, ⟨86, by decide⟩) | 90 => some (1, ⟨87, by decide⟩) | 91 => some (4, ⟨87, by decide⟩)
  | 92 => some (2, ⟨88, by decide⟩) | 93 => some (3, ⟨89, by decide⟩) | 94 => some (1, ⟨91, by decide⟩)
  | 95 => some (5, ⟨91, by decide⟩) | 96 => some (0, ⟨92, by decide⟩) | 97 => some (2, ⟨93, by decide⟩)
  | 98 => some (3, ⟨94, by decide⟩) | 99 => some (1, ⟨95, by decide⟩) | 100 => some (0, ⟨97, by decide⟩)
  | 101 => some (2, ⟨98, by decide⟩) | 102 => some (3, ⟨99, by decide⟩) | 103 => some (0, ⟨101, by decide⟩)
  | 104 => some (2, ⟨102, by decide⟩) | 105 => some (4, ⟨102, by decide⟩) | 106 => some (0, ⟨104, by decide⟩)
  | 107 => some (2, ⟨105, by decide⟩) | 108 => some (0, ⟨107, by decide⟩) | 109 => some (3, ⟨107, by decide⟩)
  | 110 => some (0, ⟨109, by decide⟩) | 111 => some (1, ⟨109, by decide⟩) | 112 => some (0, ⟨111, by decide⟩)
  | 113 => some (2, ⟨110, by decide⟩) | 114 => some (2, ⟨112, by decide⟩) | 115 => some (3, ⟨114, by decide⟩)
  | 116 => some (4, ⟨115, by decide⟩) | 117 => some (5, ⟨116, by decide⟩) | 118 => some (6, ⟨117, by decide⟩)
  | 119 => some (7, ⟨118, by decide⟩)
  | _ => none

private def e8PosUp (i : Fin 8) (p : Fin 120) : Option (Bool × Fin 120) :=
  match i.val with
  | 0 =>
    match p.val with
    | 2 => some (true, ⟨8, by decide⟩) | 10 => some (true, ⟨15, by decide⟩) | 16 => some (true, ⟨22, by decide⟩)
    | 18 => some (true, ⟨23, by decide⟩) | 24 => some (true, ⟨29, by decide⟩) | 26 => some (true, ⟨30, by decide⟩)
    | 31 => some (true, ⟨36, by decide⟩) | 32 => some (true, ⟨37, by decide⟩) | 34 => some (true, ⟨38, by decide⟩)
    | 39 => some (true, ⟨44, by decide⟩) | 40 => some (true, ⟨45, by decide⟩) | 42 => some (true, ⟨46, by decide⟩)
    | 47 => some (true, ⟨51, by decide⟩) | 48 => some (true, ⟨52, by decide⟩) | 49 => some (true, ⟨53, by decide⟩)
    | 54 => some (true, ⟨58, by decide⟩) | 55 => some (true, ⟨59, by decide⟩) | 60 => some (true, ⟨65, by decide⟩)
    | 61 => some (true, ⟨66, by decide⟩) | 67 => some (true, ⟨72, by decide⟩) | 73 => some (true, ⟨78, by decide⟩)
    | 92 => some (true, ⟨96, by decide⟩) | 97 => some (true, ⟨100, by decide⟩) | 101 => some (true, ⟨103, by decide⟩)
    | 104 => some (true, ⟨106, by decide⟩) | 107 => some (true, ⟨108, by decide⟩) | 109 => some (true, ⟨110, by decide⟩)
    | 111 => some (true, ⟨112, by decide⟩)
    | _ => none
  | 1 =>
    match p.val with
    | 3 => some (true, ⟨9, by decide⟩) | 10 => some (true, ⟨16, by decide⟩) | 11 => some (true, ⟨17, by decide⟩)
    | 15 => some (true, ⟨22, by decide⟩) | 18 => some (true, ⟨24, by decide⟩) | 19 => some (true, ⟨25, by decide⟩)
    | 23 => some (true, ⟨29, by decide⟩) | 26 => some (true, ⟨32, by decide⟩) | 27 => some (true, ⟨33, by decide⟩)
    | 30 => some (true, ⟨37, by decide⟩) | 34 => some (true, ⟨40, by decide⟩) | 35 => some (true, ⟨41, by decide⟩)
    | 38 => some (true, ⟨45, by decide⟩) | 42 => some (true, ⟨49, by decide⟩) | 46 => some (true, ⟨53, by decide⟩)
    | 62 => some (true, ⟨68, by decide⟩) | 69 => some (true, ⟨74, by decide⟩) | 75 => some (true, ⟨79, by decide⟩)
    | 76 => some (true, ⟨80, by decide⟩) | 81 => some (true, ⟨84, by decide⟩) | 82 => some (true, ⟨85, by decide⟩)
    | 86 => some (true, ⟨89, by decide⟩) | 87 => some (true, ⟨90, by decide⟩) | 91 => some (true, ⟨94, by decide⟩)
    | 95 => some (true, ⟨99, by decide⟩) | 109 => some (true, ⟨111, by decide⟩) | 110 => some (true, ⟨112, by decide⟩)
    | 113 => some (true, ⟨114, by decide⟩)
    | _ => none
  | 2 =>
    match p.val with
    | 0 => some (false, ⟨8, by decide⟩) | 3 => some (true, ⟨10, by decide⟩) | 9 => some (true, ⟨16, by decide⟩)
    | 11 => some (true, ⟨18, by decide⟩) | 17 => some (true, ⟨24, by decide⟩) | 19 => some (true, ⟨26, by decide⟩)
    | 25 => some (true, ⟨32, by decide⟩) | 27 => some (true, ⟨34, by decide⟩) | 33 => some (true, ⟨40, by decide⟩)
    | 35 => some (true, ⟨42, by decide⟩) | 36 => some (true, ⟨43, by decide⟩) | 41 => some (true, ⟨49, by decide⟩)
    | 44 => some (true, ⟨50, by decide⟩) | 51 => some (true, ⟨56, by decide⟩) | 52 => some (true, ⟨57, by decide⟩)
    | 58 => some (true, ⟨63, by decide⟩) | 59 => some (true, ⟨64, by decide⟩) | 65 => some (true, ⟨70, by decide⟩)
    | 66 => some (true, ⟨71, by decide⟩) | 72 => some (true, ⟨77, by decide⟩) | 78 => some (true, ⟨83, by decide⟩)
    | 88 => some (true, ⟨92, by decide⟩) | 93 => some (true, ⟨97, by decide⟩) | 98 => some (true, ⟨101, by decide⟩)
    | 102 => some (true, ⟨104, by decide⟩) | 105 => some (true, ⟨107, by decide⟩) | 110 => some (true, ⟨113, by decide⟩)
    | 112 => some (true, ⟨114, by decide⟩)
    | _ => none
  | 3 =>
    match p.val with
    | 1 => some (false, ⟨9, by decide⟩) | 2 => some (false, ⟨10, by decide⟩) | 4 => some (true, ⟨11, by decide⟩)
    | 8 => some (false, ⟨15, by decide⟩) | 12 => some (true, ⟨19, by decide⟩) | 20 => some (true, ⟨27, by decide⟩)
    | 24 => some (true, ⟨31, by decide⟩) | 28 => some (true, ⟨35, by decide⟩) | 29 => some (true, ⟨36, by decide⟩)
    | 32 => some (true, ⟨39, by decide⟩) | 37 => some (true, ⟨44, by decide⟩) | 40 => some (true, ⟨48, by decide⟩)
    | 45 => some (true, ⟨52, by decide⟩) | 49 => some (true, ⟨55, by decide⟩) | 53 => some (true, ⟨59, by decide⟩)
    | 56 => some (true, ⟨62, by decide⟩) | 63 => some (true, ⟨69, by decide⟩) | 70 => some (true, ⟨75, by decide⟩)
    | 71 => some (true, ⟨76, by decide⟩) | 77 => some (true, ⟨82, by decide⟩) | 83 => some (true, ⟨87, by decide⟩)
    | 84 => some (true, ⟨88, by decide⟩) | 89 => some (true, ⟨93, by decide⟩) | 94 => some (true, ⟨98, by decide⟩)
    | 99 => some (true, ⟨102, by decide⟩) | 107 => some (true, ⟨109, by decide⟩) | 108 => some (true, ⟨110, by decide⟩)
    | 114 => some (true, ⟨115, by decide⟩)
    | _ => none
  | 4 =>
    match p.val with
    | 3 => some (false, ⟨11, by decide⟩) | 5 => some (true, ⟨12, by decide⟩) | 9 => some (false, ⟨17, by decide⟩)
    | 10 => some (false, ⟨18, by decide⟩) | 13 => some (true, ⟨20, by decide⟩) | 15 => some (false, ⟨23, by decide⟩)
    | 16 => some (false, ⟨24, by decide⟩) | 21 => some (true, ⟨28, by decide⟩) | 22 => some (false, ⟨29, by decide⟩)
    | 39 => some (true, ⟨47, by decide⟩) | 44 => some (true, ⟨51, by decide⟩) | 48 => some (true, ⟨54, by decide⟩)
    | 50 => some (true, ⟨56, by decide⟩) | 52 => some (true, ⟨58, by decide⟩) | 55 => some (true, ⟨61, by decide⟩)
    | 57 => some (true, ⟨63, by decide⟩) | 59 => some (true, ⟨66, by decide⟩) | 64 => some (true, ⟨71, by decide⟩)
    | 75 => some (true, ⟨81, by decide⟩) | 79 => some (true, ⟨84, by decide⟩) | 82 => some (true, ⟨86, by decide⟩)
    | 85 => some (true, ⟨89, by decide⟩) | 87 => some (true, ⟨91, by decide⟩) | 90 => some (true, ⟨94, by decide⟩)
    | 102 => some (true, ⟨105, by decide⟩) | 104 => some (true, ⟨107, by decide⟩) | 106 => some (true, ⟨108, by decide⟩)
    | 115 => some (true, ⟨116, by decide⟩)
    | _ => none
  | 5 =>
    match p.val with
    | 4 => some (false, ⟨12, by decide⟩) | 6 => some (true, ⟨13, by decide⟩) | 11 => some (false, ⟨19, by decide⟩)
    | 14 => some (true, ⟨21, by decide⟩) | 17 => some (false, ⟨25, by decide⟩) | 18 => some (false, ⟨26, by decide⟩)
    | 23 => some (false, ⟨30, by decide⟩) | 24 => some (false, ⟨32, by decide⟩) | 29 => some (false, ⟨37, by decide⟩)
    | 31 => some (false, ⟨39, by decide⟩) | 36 => some (false, ⟨44, by decide⟩) | 43 => some (false, ⟨50, by decide⟩)
    | 54 => some (true, ⟨60, by decide⟩) | 58 => some (true, ⟨65, by decide⟩) | 61 => some (true, ⟨67, by decide⟩)
    | 63 => some (true, ⟨70, by decide⟩) | 66 => some (true, ⟨72, by decide⟩) | 69 => some (true, ⟨75, by decide⟩)
    | 71 => some (true, ⟨77, by decide⟩) | 74 => some (true, ⟨79, by decide⟩) | 76 => some (true, ⟨82, by decide⟩)
    | 80 => some (true, ⟨85, by decide⟩) | 91 => some (true, ⟨95, by decide⟩) | 94 => some (true, ⟨99, by decide⟩)
    | 98 => some (true, ⟨102, by decide⟩) | 101 => some (true, ⟨104, by decide⟩) | 103 => some (true, ⟨106, by decide⟩)
    | 116 => some (true, ⟨117, by decide⟩)
    | _ => none
  | 6 =>
    match p.val with
    | 5 => some (false, ⟨13, by decide⟩) | 7 => some (true, ⟨14, by decide⟩) | 12 => some (false, ⟨20, by decide⟩)
    | 19 => some (false, ⟨27, by decide⟩) | 25 => some (false, ⟨33, by decide⟩) | 26 => some (false, ⟨34, by decide⟩)
    | 30 => some (false, ⟨38, by decide⟩) | 32 => some (false, ⟨40, by decide⟩) | 37 => some (false, ⟨45, by decide⟩)
    | 39 => some (false, ⟨48, by decide⟩) | 44 => some (false, ⟨52, by decide⟩) | 47 => some (false, ⟨54, by decide⟩)
    | 50 => some (false, ⟨57, by decide⟩) | 51 => some (false, ⟨58, by decide⟩) | 56 => some (false, ⟨63, by decide⟩)
    | 62 => some (false, ⟨69, by decide⟩) | 67 => some (true, ⟨73, by decide⟩) | 68 => some (false, ⟨74, by decide⟩)
    | 72 => some (true, ⟨78, by decide⟩) | 77 => some (true, ⟨83, by decide⟩) | 82 => some (true, ⟨87, by decide⟩)
    | 85 => some (true, ⟨90, by decide⟩) | 86 => some (true, ⟨91, by decide⟩) | 89 => some (true, ⟨94, by decide⟩)
    | 93 => some (true, ⟨98, by decide⟩) | 97 => some (true, ⟨101, by decide⟩) | 100 => some (true, ⟨103, by decide⟩)
    | 117 => some (true, ⟨118, by decide⟩)
    | _ => none
  | 7 =>
    match p.val with
    | 6 => some (false, ⟨14, by decide⟩) | 13 => some (false, ⟨21, by decide⟩) | 20 => some (false, ⟨28, by decide⟩)
    | 27 => some (false, ⟨35, by decide⟩) | 33 => some (false, ⟨41, by decide⟩) | 34 => some (false, ⟨42, by decide⟩)
    | 38 => some (false, ⟨46, by decide⟩) | 40 => some (false, ⟨49, by decide⟩) | 45 => some (false, ⟨53, by decide⟩)
    | 48 => some (false, ⟨55, by decide⟩) | 52 => some (false, ⟨59, by decide⟩) | 54 => some (false, ⟨61, by decide⟩)
    | 57 => some (false, ⟨64, by decide⟩) | 58 => some (false, ⟨66, by decide⟩) | 60 => some (false, ⟨67, by decide⟩)
    | 63 => some (false, ⟨71, by decide⟩) | 65 => some (false, ⟨72, by decide⟩) | 69 => some (false, ⟨76, by decide⟩)
    | 70 => some (false, ⟨77, by decide⟩) | 74 => some (false, ⟨80, by decide⟩) | 75 => some (false, ⟨82, by decide⟩)
    | 79 => some (false, ⟨85, by decide⟩) | 81 => some (false, ⟨86, by decide⟩) | 84 => some (false, ⟨89, by decide⟩)
    | 88 => some (false, ⟨93, by decide⟩) | 92 => some (false, ⟨97, by decide⟩) | 96 => some (false, ⟨100, by decide⟩)
    | 118 => some (true, ⟨119, by decide⟩)
    | _ => none
  | _ => none

private def e8AdjRemWitness (i : Fin 8) (p : Fin 120) : Fin 120 :=
  match i.val, p.val with
  | 1, 115 => ⟨113, by decide⟩ | 2, 31 => ⟨17, by decide⟩ | 2, 39 => ⟨25, by decide⟩ | 2, 48 => ⟨33, by decide⟩
  | 2, 55 => ⟨41, by decide⟩ | 3, 16 => ⟨2, by decide⟩ | 3, 43 => ⟨29, by decide⟩ | 3, 50 => ⟨37, by decide⟩
  | 3, 57 => ⟨45, by decide⟩ | 3, 64 => ⟨53, by decide⟩ | 3, 113 => ⟨108, by decide⟩ | 4, 31 => ⟨16, by decide⟩
  | 4, 62 => ⟨50, by decide⟩ | 4, 69 => ⟨57, by decide⟩ | 4, 76 => ⟨64, by decide⟩ | 4, 88 => ⟨79, by decide⟩
  | 4, 93 => ⟨85, by decide⟩ | 4, 98 => ⟨90, by decide⟩ | 4, 109 => ⟨104, by decide⟩ | 5, 47 => ⟨31, by decide⟩
  | 5, 81 => ⟨69, by decide⟩ | 5, 86 => ⟨76, by decide⟩ | 5, 105 => ⟨98, by decide⟩ | 6, 60 => ⟨47, by decide⟩
  | 6, 95 => ⟨86, by decide⟩ | 7, 73 => ⟨60, by decide⟩
  | _, _ => 0

private def e8RootHt (r : Fin 240) : ℤ := ∑ j : Fin 8, e8RootCoord r j

private theorem e8RootHt_ne_zero (r : Fin 240) : e8RootHt r ≠ 0 := by
  have h := forall_fin240_of_blocks (fun r => decide (e8RootHt r ≠ 0))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) r
  exact of_decide_eq_true h

private theorem e8Fin240ToPos_spec {r : Fin 240} (hr : 0 < e8RootHt r) :
    e8PosRoot (e8Fin240ToPos r) = r := by
  have h := forall_fin240_of_blocks
    (fun r => if decide (0 < e8RootHt r) then e8PosRoot (e8Fin240ToPos r) == r else true)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) r
  simp only [decide_eq_true hr, ↓reduceIte, beq_iff_eq] at h
  exact h

private theorem e8PosRoot_simple (i : Fin 8) :
    e8PosRoot (simplePosIdx i) = e8ESimpleIdx i := by
  fin_cases i <;> decide

private theorem e8PosParent_none_iff_simple (p : Fin 120) (hp : e8PosParent p = none) :
    p = simplePosIdx (simpleOfPos p) := by
  have hbool : ∀ x : Fin 120, (match e8PosParent x with
      | none => x == simplePosIdx (simpleOfPos x)
      | some _ => true) = true := by decide
  have h := hbool p
  rw [hp] at h
  exact eq_of_beq h

private theorem e8PosRoot_parent_add {p : Fin 120} {k : Fin 8} {p₀ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) :
    ∀ j : Fin 8,
      e8RootCoord (e8ESimpleIdx k) j + e8RootCoord (e8PosRoot p₀) j =
        e8RootCoord (e8PosRoot p) j := by
  have h := forall_fin120_of_blocks
    (fun p => match e8PosParent p with
      | none => true
      | some (k, p₀) => (List.finRange 8).all fun j =>
          e8RootCoord (e8ESimpleIdx k) j + e8RootCoord (e8PosRoot p₀) j ==
            e8RootCoord (e8PosRoot p) j)
    (by decide) (by decide) (by decide) (by decide) (by decide) p
  rw [hp] at h
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h

private theorem e8PosParent_lt_bool :
    ∀ p : Fin 120, (match e8PosParent p with
      | some (_, p₀) => decide (p₀.val < p.val)
      | none => true) = true := by decide

private theorem e8PosParent_lt {p : Fin 120} {k : Fin 8} {p₀ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) : p₀.val < p.val := by
  have h := e8PosParent_lt_bool p
  rw [hp] at h
  exact of_decide_eq_true h

private theorem e8PosParent_ht_lt_bool :
    ∀ p : Fin 120, (match e8PosParent p with
      | some (_, p₀) => decide (e8PosHeight p₀ < e8PosHeight p)
      | none => true) = true := by decide

private theorem e8PosParent_ht_lt {p : Fin 120} {k : Fin 8} {p₀ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) : e8PosHeight p₀ < e8PosHeight p := by
  have h := e8PosParent_ht_lt_bool p
  rw [hp] at h
  exact of_decide_eq_true h

private theorem e8PosParent_ht_succ_bool :
    ∀ p : Fin 120, (match e8PosParent p with
      | some (_, p₀) => decide (e8PosHeight p = e8PosHeight p₀ + 1)
      | none => true) = true := by decide

private theorem e8PosParent_ht_succ {p : Fin 120} {k : Fin 8} {p₀ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) : e8PosHeight p = e8PosHeight p₀ + 1 := by
  have h := e8PosParent_ht_succ_bool p
  rw [hp] at h
  exact of_decide_eq_true h

private theorem e8PosHeight_pos (p : Fin 120) : 1 ≤ e8PosHeight p := by
  revert p; decide

private theorem e8PosHeight_le_29 (p : Fin 120) : e8PosHeight p ≤ 29 := by
  revert p; decide

private theorem rootVec_mem_of_mem_rootSpace_ne_zero
    (S : LieSubalgebra ℝ SplitE8Lie) (r : Fin 240) {z : SplitE8Lie}
    (hz_rs : z ∈ LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r))
    (hz_ne : z ≠ 0) (hz_S : z ∈ S) : e8RootVec r ∈ S := by
  have hdim : Module.finrank ℝ (LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r)) = 1 :=
    finrank_splitE8Cartan_rootSpace_eq_one (e8MathlibRoot r)
  have hz_sub_ne : (⟨z, hz_rs⟩ : LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r)) ≠ 0 := by
    intro h0
    exact hz_ne (congrArg Subtype.val h0)
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' _ hz_sub_ne).mp hdim
      ⟨e8RootVec r, e8RootVec_mem_rootSpace r⟩
  have hc' : c • z = e8RootVec r := congrArg Subtype.val hc
  rw [← hc']
  exact S.smul_mem c hz_S

private theorem e8RootVec_mem_of_add
    (S : LieSubalgebra ℝ SplitE8Lie) (r₁ r₂ r₃ : Fin 240)
    (hadd : ∀ j : Fin 8, e8RootCoord r₁ j + e8RootCoord r₂ j = e8RootCoord r₃ j)
    (h₁ : e8RootVec r₁ ∈ S) (h₂ : e8RootVec r₂ ∈ S) :
    e8RootVec r₃ ∈ S := by
  have hwt_dual : e8RootWeight r₁ + e8RootWeight r₂ = e8RootWeight r₃ := by
    apply e8SimpleHBasis.ext
    intro i
    have he8 : (e8SimpleHBasis i : splitE8Cartan) =
        ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ :=
      Subtype.ext (e8SimpleHBasis_apply i)
    rw [LinearMap.add_apply, he8, e8RootWeight_simpleH, e8RootWeight_simpleH,
      e8RootWeight_simpleH]
    norm_cast
    simp only [e8RootEigenvalue, ← Finset.sum_add_distrib, ← mul_add, hadd]
  have hwt : ((e8MathlibWeight r₁ : splitE8Cartan → ℝ) +
      (e8MathlibWeight r₂ : splitE8Cartan → ℝ)) = (e8RootWeight r₃ : splitE8Cartan → ℝ) := by
    ext H
    exact congrArg (fun f : Module.Dual ℝ splitE8Cartan => f H) hwt_dual
  have hne_bot : LieAlgebra.rootSpace splitE8Cartan
      ((e8MathlibWeight r₁ : splitE8Cartan → ℝ) +
        (e8MathlibWeight r₂ : splitE8Cartan → ℝ)) ≠ ⊥ := by
    rw [hwt]
    exact e8RootSpace_ne_bot r₃
  obtain ⟨a, ha_rs, b, hb_rs, hab⟩ :=
    LieAlgebra.IsKilling.exists_mem_rootSpace_lie_ne_zero
      (LieSubalgebra.isNonZero_coe_root (e8MathlibRoot r₁)) hne_bot
  have haS : a ∈ S := by
    have hdim1 : Module.finrank ℝ (LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r₁)) = 1 :=
      finrank_splitE8Cartan_rootSpace_eq_one (e8MathlibRoot r₁)
    have hr1_ne : (⟨e8RootVec r₁, e8RootVec_mem_rootSpace r₁⟩ :
        LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r₁)) ≠ 0 := by
      intro h0
      exact e8RootVec_ne_zero r₁ (congrArg Subtype.val h0)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hr1_ne).mp hdim1 ⟨a, ha_rs⟩
    have hc' : c • e8RootVec r₁ = a := congrArg Subtype.val hc
    rw [← hc']
    exact S.smul_mem c h₁
  have hbS : b ∈ S := by
    have hdim2 : Module.finrank ℝ (LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r₂)) = 1 :=
      finrank_splitE8Cartan_rootSpace_eq_one (e8MathlibRoot r₂)
    have hr2_ne : (⟨e8RootVec r₂, e8RootVec_mem_rootSpace r₂⟩ :
        LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r₂)) ≠ 0 := by
      intro h0
      exact e8RootVec_ne_zero r₂ (congrArg Subtype.val h0)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hr2_ne).mp hdim2 ⟨b, hb_rs⟩
    have hc' : c • e8RootVec r₂ = b := congrArg Subtype.val hc
    rw [← hc']
    exact S.smul_mem c h₂
  have hab_rs : ⁅a, b⁆ ∈ LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r₃) := by
    rw [← hwt]
    exact LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace ha_rs hb_rs
  exact rootVec_mem_of_mem_rootSpace_ne_zero S r₃ hab_rs hab (S.lie_mem haS hbS)

/-- Any Lie subalgebra of `SplitE8Lie` containing the 24 simple Chevalley generators
equals the whole Lie algebra. -/
theorem splitE8_simple_generators_generate
    (S : LieSubalgebra ℝ SplitE8Lie)
    (hH : ∀ i : Fin 8, e8SimpleH i ∈ S)
    (hE : ∀ i : Fin 8, e8SimpleE i ∈ S)
    (hF : ∀ i : Fin 8, e8SimpleF i ∈ S) : S = ⊤ := by
  have heRoot : ∀ i : Fin 8, e8RootVec (e8ESimpleIdx i) ∈ S := hE
  have hfRoot : ∀ i : Fin 8, e8RootVec (e8FSimpleIdx i) ∈ S := by
    intro i
    have hne : e8FSimpleScale i ≠ 0 := by
      fin_cases i <;> norm_num [e8FSimpleScale]
    have hsm : (e8FSimpleScale i)⁻¹ • e8SimpleF i ∈ S := S.smul_mem _ (hF i)
    rwa [e8SimpleF_eq_rootVec, smul_smul, inv_mul_cancel₀ hne, one_smul] at hsm
  have hpos_ind : ∀ (n : ℕ) (p : Fin 120), e8PosHeight p ≤ n →
      e8RootVec (e8PosRoot p) ∈ S := by
    intro n
    induction n with
    | zero =>
      intro p hp
      have := e8PosHeight_pos p
      omega
    | succ n ih =>
      intro p hp
      cases hpar : e8PosParent p with
      | none =>
        rw [e8PosParent_none_iff_simple p hpar, e8PosRoot_simple]
        exact heRoot (simpleOfPos p)
      | some kp₀ =>
        rcases kp₀ with ⟨k, p₀⟩
        have hlt : e8PosHeight p₀ ≤ n := by
          have := e8PosParent_ht_succ hpar
          omega
        exact e8RootVec_mem_of_add S (e8ESimpleIdx k) (e8PosRoot p₀) (e8PosRoot p)
          (e8PosRoot_parent_add hpar) (heRoot k) (ih p₀ hlt)
  have hpos : ∀ r : Fin 240, 0 < e8RootHt r → e8RootVec r ∈ S := by
    intro r hr
    rw [← e8Fin240ToPos_spec hr]
    exact hpos_ind 29 (e8Fin240ToPos r) (e8PosHeight_le_29 _)
  have hneg_ind : ∀ (n : ℕ) (p : Fin 120), e8PosHeight p ≤ n →
      e8RootVec (e8RootNeg (e8PosRoot p)) ∈ S := by
    intro n
    induction n with
    | zero =>
      intro p hp
      have := e8PosHeight_pos p
      omega
    | succ n ih =>
      intro p hp
      cases hpar : e8PosParent p with
      | none =>
        rw [e8PosParent_none_iff_simple p hpar, e8PosRoot_simple, e8RootNeg_e8ESimpleIdx]
        exact hfRoot (simpleOfPos p)
      | some kp₀ =>
        rcases kp₀ with ⟨k, p₀⟩
        have hlt : e8PosHeight p₀ ≤ n := by
          have := e8PosParent_ht_succ hpar
          omega
        have hadd : ∀ j : Fin 8,
            e8RootCoord (e8FSimpleIdx k) j + e8RootCoord (e8RootNeg (e8PosRoot p₀)) j =
              e8RootCoord (e8RootNeg (e8PosRoot p)) j := by
          intro j
          rw [← e8RootNeg_e8ESimpleIdx k]
          have hn1 := congrFun (e8RootCoord_neg (e8ESimpleIdx k)) j
          have hn2 := congrFun (e8RootCoord_neg (e8PosRoot p₀)) j
          have hn3 := congrFun (e8RootCoord_neg (e8PosRoot p)) j
          simp only [Pi.neg_apply] at hn1 hn2 hn3
          rw [hn1, hn2, hn3]
          have hpadd := e8PosRoot_parent_add hpar j
          omega
        exact e8RootVec_mem_of_add S (e8FSimpleIdx k) (e8RootNeg (e8PosRoot p₀))
          (e8RootNeg (e8PosRoot p)) hadd (hfRoot k) (ih p₀ hlt)
  have hroots : ∀ r : Fin 240, e8RootVec r ∈ S := by
    intro r
    rcases lt_or_gt_of_ne (e8RootHt_ne_zero r) with hlt | hgt
    · have hpos_neg : 0 < e8RootHt (e8RootNeg r) := by
        dsimp only [e8RootHt] at hlt ⊢
        simp only [e8RootCoord_neg, Pi.neg_apply, Finset.sum_neg_distrib]
        omega
      have hmem := hneg_ind 29 (e8Fin240ToPos (e8RootNeg r)) (e8PosHeight_le_29 _)
      rw [e8Fin240ToPos_spec hpos_neg, e8RootNeg_involutive] at hmem
      exact hmem
    · exact hpos r hgt
  rw [eq_top_iff]
  intro x _
  have hrep := e8ChevalleyBasis.sum_repr x
  rw [← hrep, Fintype.sum_sum_type]
  simp only [e8ChevalleyBasis_inl, e8ChevalleyBasis_inr]
  refine S.add_mem (S.sum_mem fun i _ => S.smul_mem _ (hH i))
    (S.sum_mem fun r _ => S.smul_mem _ (hroots r))

/-- Corollary: the Lie subalgebra spanned by the 24 Chevalley generators is `⊤`. -/
theorem splitE8_simple_generators_lieSpan_eq_top :
    LieSubalgebra.lieSpan ℝ SplitE8Lie
      (Set.range e8SimpleH ∪ Set.range e8SimpleE ∪ Set.range e8SimpleF) = ⊤ := by
  apply splitE8_simple_generators_generate
  · intro i; exact LieSubalgebra.subset_lieSpan (Or.inl (Or.inl ⟨i, rfl⟩))
  · intro i; exact LieSubalgebra.subset_lieSpan (Or.inl (Or.inr ⟨i, rfl⟩))
  · intro i; exact LieSubalgebra.subset_lieSpan (Or.inr ⟨i, rfl⟩)

/-- The descended Serre quotient homomorphism `LieAlgebra.e₈ ℝ →ₗ⁅ℝ⁆ SplitE8Lie` is surjective. -/
theorem splitE8SerreQuotientMap_surjective :
    Function.Surjective splitE8SerreQuotientMap := by
  apply (LieHom.range_eq_top splitE8SerreQuotientMap).mp
  apply splitE8_simple_generators_generate splitE8SerreQuotientMap.range
  · intro i
    rw [LieHom.mem_range]
    exact ⟨Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)),
      splitE8SerreQuotientMap_H i⟩
  · intro i
    rw [LieHom.mem_range]
    exact ⟨Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)),
      splitE8SerreQuotientMap_E i⟩
  · intro i
    rw [LieHom.mem_range]
    exact ⟨Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)),
      splitE8SerreQuotientMap_F i⟩

/-! ## 3. Finite-Dimensionality (`≤ 248`) of `LieAlgebra.e₈ ℝ` via Triangular Spanning -/

private def e8SerreMk :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 8)) →ₗ⁅ℝ⁆ LieAlgebra.e₈ ℝ where
  toLinearMap := (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8)).toSubmodule.mkQ
  map_lie' := fun {_ _} => rfl

/-- The simple Cartan generators inside Mathlib's `LieAlgebra.e₈ ℝ`. -/
def e8SerreH (i : Fin 8) : LieAlgebra.e₈ ℝ :=
  e8SerreMk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i))

/-- The simple positive root generators inside Mathlib's `LieAlgebra.e₈ ℝ`. -/
def e8SerreE (i : Fin 8) : LieAlgebra.e₈ ℝ :=
  e8SerreMk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i))

/-- The simple negative root generators inside Mathlib's `LieAlgebra.e₈ ℝ`. -/
def e8SerreF (i : Fin 8) : LieAlgebra.e₈ ℝ :=
  e8SerreMk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i))

/-- Any Lie subalgebra of `LieAlgebra.e₈ ℝ` containing the 24 Chevalley generators
equals the whole Lie algebra. -/
theorem e8Serre_generators_generate (S : LieSubalgebra ℝ (LieAlgebra.e₈ ℝ))
    (hH : ∀ i, e8SerreH i ∈ S)
    (hE : ∀ i, e8SerreE i ∈ S)
    (hF : ∀ i, e8SerreF i ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let g : CartanMatrix.Generators (Fin 8) → S := fun gen =>
    match gen with
    | .H i => ⟨e8SerreH i, hH i⟩
    | .E i => ⟨e8SerreE i, hE i⟩
    | .F i => ⟨e8SerreF i, hF i⟩
  have hcomp : S.incl.comp (FreeLieAlgebra.lift ℝ g) = e8SerreMk := by
    apply FreeLieAlgebra.hom_ext
    intro gen
    cases gen with
    | H i => simp [g, e8SerreH]
    | E i => simp [g, e8SerreE]
    | F i => simp [g, e8SerreF]
  have hy : e8SerreMk y = S.incl (FreeLieAlgebra.lift ℝ g y) := by
    rw [← hcomp]
    rfl
  change e8SerreMk y ∈ S
  rw [hy]
  exact (FreeLieAlgebra.lift ℝ g y).2

private theorem e8SerreMk_mem_ideal_zero
    {x : FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 8))}
    (hx : x ∈ CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 8)) :
    e8SerreMk x = 0 := by
  change LieSubmodule.Quotient.mk x = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan hx

private theorem e8SerreH_comm (i j : Fin 8) : ⁅e8SerreH i, e8SerreH j⁆ = 0 := by
  have hx : CartanMatrix.Relations.HH ℝ (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 8) :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(i, j), rfl⟩))))
  have h := e8SerreMk_mem_ideal_zero hx
  change e8SerreMk
    ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H j)⁆ = 0 at h
  simpa [LieHom.map_lie, e8SerreH] using h

private theorem e8Serre_bracket_EF_same (i : Fin 8) :
    ⁅e8SerreE i, e8SerreF i⁆ = e8SerreH i := by
  have hx : CartanMatrix.Relations.EF ℝ (i, i) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 8) :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, i), rfl⟩))))
  have h := e8SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, ↓reduceIte] at h
  change e8SerreMk
    (⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)⁆ -
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = 0 at h
  rw [map_sub, LieHom.map_lie] at h
  exact sub_eq_zero.mp h

private theorem e8Serre_bracket_EF_ne {i j : Fin 8} (hij : i ≠ j) :
    ⁅e8SerreE i, e8SerreF j⁆ = 0 := by
  have hx : CartanMatrix.Relations.EF ℝ (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 8) :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))))
  have h := e8SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, hij, ↓reduceIte] at h
  change e8SerreMk
    ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
      FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F j)⁆ = 0 at h
  simpa [LieHom.map_lie, e8SerreE, e8SerreF] using h

private theorem e8Serre_bracket_HE (i j : Fin 8) :
    ⁅e8SerreH i, e8SerreE j⁆ = ((CartanMatrix.E 8 i j : ℤ) : ℝ) • e8SerreE j := by
  have hx : CartanMatrix.Relations.HE ℝ (CartanMatrix.E 8) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 8) :=
    Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩)))
  have h := e8SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply] at h
  rw [← Int.cast_smul_eq_zsmul ℝ, map_sub, LieHom.map_lie, map_smul] at h
  exact sub_eq_zero.mp h

private theorem e8Serre_bracket_HF (i j : Fin 8) :
    ⁅e8SerreH i, e8SerreF j⁆ = (-(CartanMatrix.E 8 i j : ℤ) : ℝ) • e8SerreF j := by
  have hx : CartanMatrix.Relations.HF ℝ (CartanMatrix.E 8) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 8) :=
    Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))
  have h := e8SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply] at h
  rw [← Int.cast_smul_eq_zsmul ℝ, map_add, LieHom.map_lie, map_smul] at h
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h

private theorem e8Serre_adE_iter {i j : Fin 8} (hij : i ≠ j) :
    Nat.iterate (fun x => ⁅e8SerreE i, x⁆)
      (1 - CartanMatrix.E 8 i j).toNat (e8SerreE j) = 0 := by
  have hx : CartanMatrix.Relations.adE ℝ (CartanMatrix.E 8) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 8) :=
    Or.inl (Or.inr ⟨(i, j), rfl⟩)
  have h := e8SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply] at h
  rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie, ← Function.iterate_succ_apply,
    Nat.succ_eq_add_one, e8_serre_exponent hij] at h
  exact h

private theorem e8Serre_adF_iter {i j : Fin 8} (hij : i ≠ j) :
    Nat.iterate (fun x => ⁅e8SerreF i, x⁆)
      (1 - CartanMatrix.E 8 i j).toNat (e8SerreF j) = 0 := by
  have hx : CartanMatrix.Relations.adF ℝ (CartanMatrix.E 8) (i, j) ∈
      CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 8) :=
    Or.inr ⟨(i, j), rfl⟩
  have h := e8SerreMk_mem_ideal_zero hx
  simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply] at h
  rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie, ← Function.iterate_succ_apply,
    Nat.succ_eq_add_one, e8_serre_exponent hij] at h
  exact h

private theorem e8Serre_adE_zero {i j : Fin 8} (hc : CartanMatrix.E 8 i j = 0) :
    ⁅e8SerreE i, e8SerreE j⁆ = 0 := by
  have hij : i ≠ j := by
    intro heq
    subst heq
    have hd := CartanMatrix.E_diag 8 i
    omega
  have h := e8Serre_adE_iter hij
  rw [hc] at h
  simpa using h

private theorem e8Serre_adE_negOne {i j : Fin 8} (hc : CartanMatrix.E 8 i j = -1) :
    ⁅e8SerreE i, ⁅e8SerreE i, e8SerreE j⁆⁆ = 0 := by
  have hij : i ≠ j := by
    intro heq
    subst heq
    have hd := CartanMatrix.E_diag 8 i
    omega
  have h := e8Serre_adE_iter hij
  rw [hc] at h
  simpa using h

private theorem e8Serre_adE_sq_gen (i j : Fin 8) :
    ⁅e8SerreE i, ⁅e8SerreE i, e8SerreE j⁆⁆ = 0 := by
  by_cases hij : i = j
  · subst hij
    simp [lie_self]
  · rcases CartanMatrix.isSimplyLaced_E 8 hij with h0 | h1
    · rw [e8Serre_adE_zero h0, lie_zero]
    · exact e8Serre_adE_negOne h1

/-! #### Chevalley involution on `LieAlgebra.e₈ ℝ` -/

private def e8SerreChevalleyGen
    (g : CartanMatrix.Generators (Fin 8)) : LieAlgebra.e₈ ℝ :=
  match g with
  | .H i => -e8SerreH i
  | .E i => e8SerreF i
  | .F i => e8SerreE i

private noncomputable def e8SerreChevalleyFree :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 8)) →ₗ⁅ℝ⁆ LieAlgebra.e₈ ℝ :=
  FreeLieAlgebra.lift ℝ e8SerreChevalleyGen

private theorem e8SerreChevalleyFree_serreIdeal :
    CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8) ≤ e8SerreChevalleyFree.ker := by
  classical
  rw [CartanMatrix.Relations.toIdeal, LieSubmodule.lieSpan_le]
  intro x hx
  simp only [CartanMatrix.Relations.toSet, Set.mem_union, Set.mem_range] at hx
  rcases hx with (((((⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) |
      ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
  · change e8SerreChevalleyFree
      ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i),
        FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H j)⁆ = 0
    simp [e8SerreChevalleyFree, e8SerreChevalleyGen, e8SerreH_comm]
  · change e8SerreChevalleyFree (CartanMatrix.Relations.EF ℝ (i, j)) = 0
    by_cases hij : i = j
    · subst hij
      simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, ↓reduceIte]
      change e8SerreChevalleyFree
        (⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
          FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)⁆ -
          FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = 0
      simp only [map_sub, LieHom.map_lie, e8SerreChevalleyFree,
        FreeLieAlgebra.lift_of_apply, e8SerreChevalleyGen]
      rw [← lie_skew (e8SerreF i) (e8SerreE i), e8Serre_bracket_EF_same, sub_neg_eq_add,
        neg_add_cancel]
    · simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, hij, ↓reduceIte]
      change e8SerreChevalleyFree
        ⁅FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i),
          FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F j)⁆ = 0
      simp only [LieHom.map_lie, e8SerreChevalleyFree, FreeLieAlgebra.lift_of_apply,
        e8SerreChevalleyGen]
      rw [← lie_skew (e8SerreF i) (e8SerreE j), e8Serre_bracket_EF_ne (Ne.symm hij), neg_zero]
  · change e8SerreChevalleyFree (CartanMatrix.Relations.HE ℝ (CartanMatrix.E 8) (i, j)) = 0
    simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply]
    rw [← Int.cast_smul_eq_zsmul ℝ, map_sub, LieHom.map_lie, map_smul]
    simp only [e8SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e8SerreChevalleyGen,
      neg_lie, e8Serre_bracket_HF, neg_smul, neg_neg, sub_self]
  · change e8SerreChevalleyFree (CartanMatrix.Relations.HF ℝ (CartanMatrix.E 8) (i, j)) = 0
    simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply]
    rw [← Int.cast_smul_eq_zsmul ℝ, map_add, LieHom.map_lie, map_smul]
    simp only [e8SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e8SerreChevalleyGen,
      neg_lie, e8Serre_bracket_HE, neg_add_cancel]
  · change e8SerreChevalleyFree (CartanMatrix.Relations.adE ℝ (CartanMatrix.E 8) (i, j)) = 0
    by_cases hij : i = j
    · subst hij
      simp [CartanMatrix.Relations.adE, Function.uncurry_apply_pair]
    · simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply]
      rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie, ← Function.iterate_succ_apply,
        Nat.succ_eq_add_one, e8_serre_exponent hij]
      simp only [e8SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e8SerreChevalleyGen]
      exact e8Serre_adF_iter hij
  · change e8SerreChevalleyFree (CartanMatrix.Relations.adF ℝ (CartanMatrix.E 8) (i, j)) = 0
    by_cases hij : i = j
    · subst hij
      simp [CartanMatrix.Relations.adF, Function.uncurry_apply_pair]
    · simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply]
      rw [ad_pow_apply_eq_iterate, map_iterate_ad, LieHom.map_lie, ← Function.iterate_succ_apply,
        Nat.succ_eq_add_one, e8_serre_exponent hij]
      simp only [e8SerreChevalleyFree, FreeLieAlgebra.lift_of_apply, e8SerreChevalleyGen]
      exact e8Serre_adE_iter hij

private noncomputable def e8SerreChevalleyHom :
    LieAlgebra.e₈ ℝ →ₗ⁅ℝ⁆ LieAlgebra.e₈ ℝ :=
  { (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8)).toSubmodule.liftQ
      e8SerreChevalleyFree.toLinearMap e8SerreChevalleyFree_serreIdeal with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y =>
          change e8SerreChevalleyFree ⁅x, y⁆ =
            ⁅e8SerreChevalleyFree x, e8SerreChevalleyFree y⁆
          exact LieHom.map_lie e8SerreChevalleyFree x y }

@[simp] private theorem e8SerreChevalleyHom_H (i : Fin 8) :
    e8SerreChevalleyHom (e8SerreH i) = -e8SerreH i := by
  change e8SerreChevalleyFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i)) = _
  simp [e8SerreChevalleyFree, e8SerreChevalleyGen]

@[simp] private theorem e8SerreChevalleyHom_E (i : Fin 8) :
    e8SerreChevalleyHom (e8SerreE i) = e8SerreF i := by
  change e8SerreChevalleyFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i)) = _
  simp [e8SerreChevalleyFree, e8SerreChevalleyGen]

@[simp] private theorem e8SerreChevalleyHom_F (i : Fin 8) :
    e8SerreChevalleyHom (e8SerreF i) = e8SerreE i := by
  change e8SerreChevalleyFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i)) = _
  simp [e8SerreChevalleyFree, e8SerreChevalleyGen]

private theorem e8SerreChevalleyHom_involutive (x : LieAlgebra.e₈ ℝ) :
    e8SerreChevalleyHom (e8SerreChevalleyHom x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hcomp : (e8SerreChevalleyHom.comp e8SerreChevalleyHom).comp e8SerreMk = e8SerreMk := by
    apply FreeLieAlgebra.hom_ext
    intro gen
    cases gen with
    | H i =>
      change e8SerreChevalleyHom (e8SerreChevalleyHom (e8SerreH i)) = e8SerreH i
      simp
    | E i =>
      change e8SerreChevalleyHom (e8SerreChevalleyHom (e8SerreE i)) = e8SerreE i
      simp
    | F i =>
      change e8SerreChevalleyHom (e8SerreChevalleyHom (e8SerreF i)) = e8SerreF i
      simp
  exact congrArg (fun f => f y) hcomp

/-- The Chevalley involution on `LieAlgebra.e₈ ℝ`, swapping `E_i ↔ F_i` and negating `H_i`. -/
noncomputable def e8SerreChevalleyInv :
    LieAlgebra.e₈ ℝ ≃ₗ⁅ℝ⁆ LieAlgebra.e₈ ℝ :=
  LieEquiv.ofBijective e8SerreChevalleyHom
    ⟨Function.LeftInverse.injective e8SerreChevalleyHom_involutive,
      Function.RightInverse.surjective e8SerreChevalleyHom_involutive⟩

@[simp] theorem e8SerreChevalleyInv_H (i : Fin 8) :
    e8SerreChevalleyInv (e8SerreH i) = -e8SerreH i :=
  e8SerreChevalleyHom_H i

@[simp] theorem e8SerreChevalleyInv_E (i : Fin 8) :
    e8SerreChevalleyInv (e8SerreE i) = e8SerreF i :=
  e8SerreChevalleyHom_E i

@[simp] theorem e8SerreChevalleyInv_F (i : Fin 8) :
    e8SerreChevalleyInv (e8SerreF i) = e8SerreE i :=
  e8SerreChevalleyHom_F i

@[simp] theorem e8SerreChevalleyInv_involutive (x : LieAlgebra.e₈ ℝ) :
    e8SerreChevalleyInv (e8SerreChevalleyInv x) = x :=
  e8SerreChevalleyHom_involutive x

/-! #### 120 positive root vectors in `LieAlgebra.e₈ ℝ` and `ad E_i` closure -/

/-- The 120 positive root vectors inside `LieAlgebra.e₈ ℝ`, built inductively
by height from the eight simple positive generators `e8SerreE i`. -/
noncomputable def e8SerrePosVec (p : Fin 120) : LieAlgebra.e₈ ℝ :=
  match hp : e8PosParent p with
  | none => e8SerreE (simpleOfPos p)
  | some (k, p₀) =>
    have _ : p₀.val < p.val := e8PosParent_lt hp
    ⁅e8SerreE k, e8SerrePosVec p₀⁆
termination_by p.val

private theorem e8_ht_le_one_simple {p : Fin 120} (hp : e8PosParent p = none) :
    e8SerrePosVec p = e8SerreE (simpleOfPos p) := by
  rw [e8SerrePosVec]
  split
  · rfl
  · next h => exact absurd (hp.symm.trans h) (by simp)

private theorem e8SerrePosVec_simple (i : Fin 8) :
    e8SerrePosVec (simplePosIdx i) = e8SerreE i := by
  fin_cases i <;>
    · rw [e8_ht_le_one_simple rfl]
      rfl

private theorem e8SerrePosVec_parent {p : Fin 120} {k : Fin 8} {p₀ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) :
    e8SerrePosVec p = ⁅e8SerreE k, e8SerrePosVec p₀⁆ := by
  rw [e8SerrePosVec]
  split
  · next h => exact absurd (hp.symm.trans h) (by simp)
  · next k' p₀' h =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hp.symm.trans h))
    rfl

private def isSelfParent (i : Fin 8) (p : Fin 120) : Bool :=
  match e8PosUp i p with
  | some (true, q) => e8PosParent q == some (i, p)
  | _ => false

private noncomputable def evalPosUp : Option (Bool × Fin 120) → LieAlgebra.e₈ ℝ
  | none => 0
  | some (true, q) => e8SerrePosVec q
  | some (false, q) => -e8SerrePosVec q

private lemma two_smul_bracket_eq_ad_sq {x z y : LieAlgebra.e₈ ℝ}
    (hxz : ⁅x, ⁅x, z⁆⁆ = 0) (hxy : ⁅x, ⁅x, y⁆⁆ = 0) :
    (2 : ℝ) • ⁅x, ⁅z, ⁅x, y⁆⁆⁆ = ⁅x, ⁅x, ⁅z, y⁆⁆⁆ := by
  have h1 : ⁅x, ⁅x, ⁅z, y⁆⁆⁆ =
      ⁅x, ⁅⁅x, z⁆, y⁆⁆ + ⁅x, ⁅z, ⁅x, y⁆⁆⁆ := by
    rw [leibniz_lie x z y, lie_add]
  have h2 : ⁅x, ⁅⁅x, z⁆, y⁆⁆ = ⁅⁅x, z⁆, ⁅x, y⁆⁆ := by
    rw [leibniz_lie x ⁅x, z⁆ y, hxz, zero_lie, zero_add]
  have h3 : ⁅⁅x, z⁆, ⁅x, y⁆⁆ = ⁅x, ⁅z, ⁅x, y⁆⁆⁆ := by
    rw [lie_lie x z ⁅x, y⁆, hxy, lie_zero, sub_zero]
  rw [h1, h2, h3, two_smul]

private lemma e8PosUp_ht_le_bool :
    ∀ (i : Fin 8) (p : Fin 120), (match e8PosUp i p with
      | some (_, q) => decide (e8PosHeight q ≤ e8PosHeight p + 1)
      | none => true) = true := by
  intro i p
  exact forall_fin8_fin120_of_blocks
    (fun i p => match e8PosUp i p with
      | some (_, q) => decide (e8PosHeight q ≤ e8PosHeight p + 1)
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) i p

private lemma e8PosUp_ht_le {i : Fin 8} {p : Fin 120} {s : Bool} {q : Fin 120}
    (hu : e8PosUp i p = some (s, q)) : e8PosHeight q ≤ e8PosHeight p + 1 := by
  have h := e8PosUp_ht_le_bool i p
  rw [hu] at h
  exact of_decide_eq_true h

private lemma e8_adSq_mid_up_none_bool :
    ∀ p : Fin 120, (match e8PosParent p with
      | some (k, p₀) => match e8PosParent p₀ with
        | some (m, p₁) =>
          if decide (CartanMatrix.E 8 k m ≠ 0 ∧ k ≠ m) then e8PosUp k p₁ == none else true
        | none => true
      | none => true) = true := by
  intro p
  exact forall_fin120_of_blocks
    (fun p => match e8PosParent p with
      | some (k, p₀) => match e8PosParent p₀ with
        | some (m, p₁) =>
          if decide (CartanMatrix.E 8 k m ≠ 0 ∧ k ≠ m) then e8PosUp k p₁ == none else true
        | none => true
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) p

private lemma e8_adSq_mid_up_none {p : Fin 120} {k : Fin 8} {p₀ : Fin 120}
    {m : Fin 8} {p₁ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) (hp₀ : e8PosParent p₀ = some (m, p₁))
    (hkm : CartanMatrix.E 8 k m ≠ 0) (hkmeq : k ≠ m) :
    e8PosUp k p₁ = none := by
  have h := e8_adSq_mid_up_none_bool p
  rw [hp] at h
  dsimp only at h
  rw [hp₀] at h
  simpa [hkm, hkmeq] using h

private lemma e8_adSq_end_up_none_bool :
    ∀ p : Fin 120, (match e8PosParent p with
      | some (k, p₀) => match e8PosParent p₀ with
        | some (_, p₁) => match e8PosUp k p₁ with
          | some (_, q) => e8PosUp k q == none
          | none => true
        | none => true
      | none => true) = true := by
  intro p
  exact forall_fin120_of_blocks
    (fun p => match e8PosParent p with
      | some (k, p₀) => match e8PosParent p₀ with
        | some (_, p₁) => match e8PosUp k p₁ with
          | some (_, q) => e8PosUp k q == none
          | none => true
        | none => true
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) p

private lemma e8_adSq_end_up_none {p : Fin 120} {k : Fin 8} {p₀ : Fin 120}
    {m : Fin 8} {p₁ : Fin 120} {s : Bool} {q : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) (hp₀ : e8PosParent p₀ = some (m, p₁))
    (hup : e8PosUp k p₁ = some (s, q)) :
    e8PosUp k q = none := by
  have h := e8_adSq_end_up_none_bool p
  rw [hp] at h
  dsimp only at h
  rw [hp₀] at h
  dsimp only at h
  rw [hup] at h
  exact eq_of_beq h

private lemma e8_diag_up_none_bool :
    ∀ p : Fin 120, (match e8PosParent p with
      | some (k, _) => e8PosUp k p == none
      | none => true) = true := by
  intro p
  exact forall_fin120_of_blocks
    (fun p => match e8PosParent p with
      | some (k, _) => e8PosUp k p == none
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) p

private lemma e8_diag_up_none {p : Fin 120} {k : Fin 8} {p₀ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) : e8PosUp k p = none := by
  have h := e8_diag_up_none_bool p
  rw [hp] at h
  exact eq_of_beq h

private lemma e8_comm_up_none_bool :
    ∀ (i : Fin 8) (p : Fin 120), (match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k = 0) && (e8PosUp i p₀ == none)
        then e8PosUp i p == none else true
      | none => true) = true := by
  intro i p
  exact forall_fin8_fin120_of_blocks
    (fun i p => match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k = 0) && (e8PosUp i p₀ == none)
        then e8PosUp i p == none else true
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) i p

private lemma e8_comm_up_none {p : Fin 120} {i k : Fin 8} {p₀ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : CartanMatrix.E 8 i k = 0) (hup0 : e8PosUp i p₀ = none) :
    e8PosUp i p = none := by
  have h := e8_comm_up_none_bool i p
  rw [hp] at h
  simpa [hik, hcart, hup0] using h

private lemma e8_comm_up_self_parent_bool :
    ∀ (i : Fin 8) (p : Fin 120), (match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k = 0) && isSelfParent i p then
          match e8PosUp i p₀ with
          | some (s₀, _) => s₀ == true
          | none => true
        else true
      | none => true) = true := by
  intro i p
  exact forall_fin8_fin120_of_blocks
    (fun i p => match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k = 0) && isSelfParent i p then
          match e8PosUp i p₀ with
          | some (s₀, _) => s₀ == true
          | none => true
        else true
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) i p

private lemma e8_comm_up_self_parent {p : Fin 120} {i k : Fin 8} {p₀ q₁ : Fin 120}
    {s₀ : Bool}
    (hp : e8PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : CartanMatrix.E 8 i k = 0) (hup0 : e8PosUp i p₀ = some (s₀, q₁))
    (hself : isSelfParent i p = true) :
    s₀ = true := by
  have h := e8_comm_up_self_parent_bool i p
  rw [hp] at h
  simpa [hik, hcart, hself, hup0] using h

private lemma e8_comm_up_other_parent_bool :
    ∀ (i : Fin 8) (p : Fin 120), (match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k = 0) && !(isSelfParent i p) then
          match e8PosUp i p₀ with
          | some (s₀, q₁) => match e8PosUp i p with
            | some (s, q) => (s == s₀) && (e8PosParent q == some (k, q₁))
            | none => false
          | none => true
        else true
      | none => true) = true := by
  intro i p
  exact forall_fin8_fin120_of_blocks
    (fun i p => match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k = 0) && !(isSelfParent i p) then
          match e8PosUp i p₀ with
          | some (s₀, q₁) => match e8PosUp i p with
            | some (s, q) => (s == s₀) && (e8PosParent q == some (k, q₁))
            | none => false
          | none => true
        else true
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) i p

private lemma e8_comm_up_other_parent {p : Fin 120} {i k : Fin 8} {p₀ q₁ : Fin 120}
    {s₀ : Bool}
    (hp : e8PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : CartanMatrix.E 8 i k = 0) (hup0 : e8PosUp i p₀ = some (s₀, q₁))
    (hnot : isSelfParent i p = false) :
    ∃ q, e8PosUp i p = some (s₀, q) ∧ e8PosParent q = some (k, q₁) := by
  have h := e8_comm_up_other_parent_bool i p
  rw [hp] at h
  dsimp only at h
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at h
  simp only [Bool.true_and, Bool.not_false, ↓reduceIte] at h
  rw [hup0] at h
  dsimp only at h
  cases hup : e8PosUp i p with
  | none => rw [hup] at h; dsimp only at h; contradiction
  | some sq =>
    rcases sq with ⟨s, q⟩
    rw [hup] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨q, by rw [h.1], h.2⟩

private lemma e8_cartan_symm_zero {i k : Fin 8}
    (h : CartanMatrix.E 8 i k = 0) : CartanMatrix.E 8 k i = 0 := by
  rw [(CartanMatrix.E_isSymm 8).apply i k, h]

private lemma e8_adj_up_none_bool :
    ∀ (i : Fin 8) (p : Fin 120), (match e8PosParent p with
      | some (k, _) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k ≠ 0) && !(isSelfParent i p)
        then e8PosUp i p == none else true
      | none => true) = true := by
  intro i p
  exact forall_fin8_fin120_of_blocks
    (fun i p => match e8PosParent p with
      | some (k, _) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k ≠ 0) && !(isSelfParent i p)
        then e8PosUp i p == none else true
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) i p

private lemma e8_adj_up_none {p : Fin 120} {i k : Fin 8} {p₀ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : CartanMatrix.E 8 i k ≠ 0) (hnot : isSelfParent i p = false) :
    e8PosUp i p = none := by
  have h := e8_adj_up_none_bool i p
  rw [hp] at h
  simpa [hik, hcart, hnot] using h

private lemma e8_adj_ht2_simple_bool :
    ∀ (i : Fin 8) (p : Fin 120), (match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k ≠ 0) && !(isSelfParent i p) then
          match e8PosParent p₀ with
          | none => simpleOfPos p₀ == i
          | some _ => true
        else true
      | none => true) = true := by
  intro i p
  exact forall_fin8_fin120_of_blocks
    (fun i p => match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k ≠ 0) && !(isSelfParent i p) then
          match e8PosParent p₀ with
          | none => simpleOfPos p₀ == i
          | some _ => true
        else true
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) i p

private lemma e8_adj_ht2_simple {p : Fin 120} {i k : Fin 8} {p₀ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : CartanMatrix.E 8 i k ≠ 0) (hnot : isSelfParent i p = false)
    (hp₀ : e8PosParent p₀ = none) :
    simpleOfPos p₀ = i := by
  have h := e8_adj_ht2_simple_bool i p
  rw [hp] at h
  dsimp only at h
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at h
  rw [hp₀] at h
  exact eq_of_beq h

private lemma e8_adj_mi_up_none_bool :
    ∀ (m : Fin 8) (p : Fin 120), (match e8PosParent p with
      | some (k, p₀) =>
        if decide (m ≠ k ∧ CartanMatrix.E 8 m k ≠ 0) && !(isSelfParent m p) then
          match e8PosParent p₀ with
          | some (m', p₁) =>
            if m' == m then (e8PosUp k p₁ == none) && (e8PosUp m p₀ == none) else true
          | none => true
        else true
      | none => true) = true := by
  intro m p
  exact forall_fin8_fin120_of_blocks
    (fun m p => match e8PosParent p with
      | some (k, p₀) =>
        if decide (m ≠ k ∧ CartanMatrix.E 8 m k ≠ 0) && !(isSelfParent m p) then
          match e8PosParent p₀ with
          | some (m', p₁) =>
            if m' == m then (e8PosUp k p₁ == none) && (e8PosUp m p₀ == none) else true
          | none => true
        else true
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) m p

private lemma e8_adj_mi_up_none {p : Fin 120} {m k : Fin 8} {p₀ p₁ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) (hmk : m ≠ k)
    (hcart : CartanMatrix.E 8 m k ≠ 0) (hnot : isSelfParent m p = false)
    (hp₀ : e8PosParent p₀ = some (m, p₁)) :
    e8PosUp k p₁ = none ∧ e8PosUp m p₀ = none := by
  have h := e8_adj_mi_up_none_bool m p
  rw [hp] at h
  dsimp only at h
  rw [decide_eq_true ⟨hmk, hcart⟩, hnot] at h
  rw [hp₀] at h
  simpa using h

private lemma e8_adj_comm_m_witness_bool :
    ∀ (i : Fin 8) (p : Fin 120), (match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k ≠ 0) && !(isSelfParent i p) then
          match e8PosParent p₀ with
          | some (m, p₁) =>
            if decide (m ≠ i ∧ CartanMatrix.E 8 k m = 0 ∧ CartanMatrix.E 8 i m = 0) then
              match e8PosUp k p₁ with
              | some (_, q) => e8PosUp i q == none
              | none => false
            else true
          | none => true
        else true
      | none => true) = true := by
  intro i p
  exact forall_fin8_fin120_of_blocks
    (fun i p => match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k ≠ 0) && !(isSelfParent i p) then
          match e8PosParent p₀ with
          | some (m, p₁) =>
            if decide (m ≠ i ∧ CartanMatrix.E 8 k m = 0 ∧ CartanMatrix.E 8 i m = 0) then
              match e8PosUp k p₁ with
              | some (_, q) => e8PosUp i q == none
              | none => false
            else true
          | none => true
        else true
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) i p

private lemma e8_adj_comm_m_witness {p : Fin 120} {i k m : Fin 8} {p₀ p₁ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : CartanMatrix.E 8 i k ≠ 0) (hnot : isSelfParent i p = false)
    (hp₀ : e8PosParent p₀ = some (m, p₁)) (hmi : m ≠ i)
    (hcomm : CartanMatrix.E 8 k m = 0 ∧ CartanMatrix.E 8 i m = 0) :
    ∃ s q, e8PosUp k p₁ = some (s, q) ∧ e8PosUp i q = none := by
  have h := e8_adj_comm_m_witness_bool i p
  rw [hp] at h
  dsimp only at h
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at h
  simp only [Bool.true_and, Bool.not_false, ↓reduceIte] at h
  rw [hp₀] at h
  dsimp only at h
  rw [decide_eq_true ⟨hmi, hcomm⟩] at h
  simp only [↓reduceIte] at h
  cases hupk : e8PosUp k p₁ with
  | none => rw [hupk] at h; dsimp only at h; contradiction
  | some sq =>
    rcases sq with ⟨s, q⟩
    rw [hupk] at h
    dsimp only at h
    exact ⟨s, q, rfl, eq_of_beq h⟩

private lemma e8_adj_rem_witness_ok_bool :
    ∀ (i : Fin 8) (p : Fin 120), (match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k ≠ 0) && !(isSelfParent i p) then
          match e8PosParent p₀ with
          | some (m, _) =>
            if decide (m ≠ i ∧ ¬(CartanMatrix.E 8 k m = 0 ∧ CartanMatrix.E 8 i m = 0)) then
              let r := e8AdjRemWitness i p
              decide (e8PosHeight r < e8PosHeight p₀) &&
                (match e8PosUp i r with | some (_, q) => q == p₀ | none => false) &&
                (e8PosUp k r == none) && (e8PosUp i p₀ == none)
            else true
          | none => true
        else true
      | none => true) = true := by
  intro i p
  exact forall_fin8_fin120_of_blocks
    (fun i p => match e8PosParent p with
      | some (k, p₀) =>
        if decide (i ≠ k ∧ CartanMatrix.E 8 i k ≠ 0) && !(isSelfParent i p) then
          match e8PosParent p₀ with
          | some (m, _) =>
            if decide (m ≠ i ∧ ¬(CartanMatrix.E 8 k m = 0 ∧ CartanMatrix.E 8 i m = 0)) then
              let r := e8AdjRemWitness i p
              decide (e8PosHeight r < e8PosHeight p₀) &&
                (match e8PosUp i r with | some (_, q) => q == p₀ | none => false) &&
                (e8PosUp k r == none) && (e8PosUp i p₀ == none)
            else true
          | none => true
        else true
      | none => true)
    (by decide) (by decide) (by decide) (by decide) (by decide) i p

private lemma e8_adj_rem_witness_ok {p : Fin 120} {i k m : Fin 8} {p₀ p₁ : Fin 120}
    (hp : e8PosParent p = some (k, p₀)) (hik : i ≠ k)
    (hcart : CartanMatrix.E 8 i k ≠ 0) (hnot : isSelfParent i p = false)
    (hp₀ : e8PosParent p₀ = some (m, p₁)) (hmi : m ≠ i)
    (hnc : ¬(CartanMatrix.E 8 k m = 0 ∧ CartanMatrix.E 8 i m = 0)) :
    let r := e8AdjRemWitness i p
    e8PosHeight r < e8PosHeight p₀ ∧
      (∃ s_r : Bool, e8PosUp i r = some (s_r, p₀)) ∧
      e8PosUp k r = none ∧ e8PosUp i p₀ = none := by
  have h := e8_adj_rem_witness_ok_bool i p
  rw [hp] at h
  dsimp only at h
  rw [decide_eq_true ⟨hik, hcart⟩, hnot] at h
  simp only [Bool.true_and, Bool.not_false, ↓reduceIte] at h
  rw [hp₀] at h
  dsimp only at h
  rw [decide_eq_true
    (p := m ≠ i ∧ ¬(CartanMatrix.E 8 k m = 0 ∧ CartanMatrix.E 8 i m = 0)) ⟨hmi, hnc⟩] at h
  simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨h_lt, h_up⟩, h_kr⟩, h_ip0⟩
  dsimp only
  refine ⟨h_lt, ?_, h_kr, h_ip0⟩
  cases hu : e8PosUp i (e8AdjRemWitness i p) with
  | none => rw [hu] at h_up; contradiction
  | some sq =>
    rcases sq with ⟨s_r, q⟩
    rw [hu] at h_up
    dsimp only at h_up
    have hqp : q = p₀ := eq_of_beq h_up
    subst hqp
    exact ⟨s_r, rfl⟩

private lemma e8_pos_base_ht1_simple (i j : Fin 8) :
    ⁅e8SerreE i, e8SerrePosVec (simplePosIdx j)⁆ = evalPosUp (e8PosUp i (simplePosIdx j)) := by
  by_cases hij : i = j
  · subst hij
    have hdiag : ∀ a : Fin 8, e8PosUp a (simplePosIdx a) = none := by decide
    rw [e8SerrePosVec_simple, hdiag i, evalPosUp, lie_self]
  · by_cases h0 : CartanMatrix.E 8 i j = 0
    · have hzero : e8PosUp i (simplePosIdx j) = none := by
        have hb : ∀ a b : Fin 8,
            (if decide (CartanMatrix.E 8 a b = 0) then
              e8PosUp a (simplePosIdx b) == none else true) = true := by decide
        have h' := hb i j
        simpa [h0] using h'
      rw [e8SerrePosVec_simple, hzero, evalPosUp]
      exact e8Serre_adE_zero h0
    · have htrich : ∀ a b : Fin 8,
          (if decide (a ≠ b ∧ CartanMatrix.E 8 a b ≠ 0) then
            (match e8PosUp a (simplePosIdx b) with
              | some (true, q) => e8PosParent q == some (a, simplePosIdx b)
              | some (false, q) => e8PosParent q == some (b, simplePosIdx a)
              | none => false) else true) = true := by decide
      have ht := htrich i j
      rw [decide_eq_true ⟨hij, h0⟩] at ht
      simp only [↓reduceIte] at ht
      cases hup : e8PosUp i (simplePosIdx j) with
      | none => rw [hup] at ht; contradiction
      | some sq =>
        rcases sq with ⟨s, q⟩
        cases s
        · rw [hup] at ht
          rw [e8SerrePosVec_simple j, ← lie_skew, ← e8SerrePosVec_simple i]
          dsimp only [evalPosUp]
          exact congrArg Neg.neg (e8SerrePosVec_parent (eq_of_beq ht)).symm
        · rw [hup] at ht
          dsimp only [evalPosUp]
          exact (e8SerrePosVec_parent (eq_of_beq ht)).symm

private lemma e8_pos_base_ht1 (i : Fin 8) (p : Fin 120) (hp : e8PosParent p = none) :
    ⁅e8SerreE i, e8SerrePosVec p⁆ = evalPosUp (e8PosUp i p) := by
  have hsp := e8PosParent_none_iff_simple p hp
  conv_lhs => rw [hsp]
  conv_rhs => rw [hsp]
  exact e8_pos_base_ht1_simple i (simpleOfPos p)

private lemma e8_ad_sq_posVec_eq_zero (n : ℕ)
    (ih : ∀ q : Fin 120, e8PosHeight q ≤ n → ∀ j : Fin 8,
      ⁅e8SerreE j, e8SerrePosVec q⁆ = evalPosUp (e8PosUp j q))
    (p : Fin 120) (hn : e8PosHeight p ≤ n + 1) (k : Fin 8) (p₀ : Fin 120)
    (hp : e8PosParent p = some (k, p₀)) :
    ⁅e8SerreE k, e8SerrePosVec p⁆ = 0 := by
  rw [e8SerrePosVec_parent hp]
  have hlt0 : e8PosHeight p₀ ≤ n :=
    Nat.le_of_lt_succ (lt_of_lt_of_le (e8PosParent_ht_lt hp) hn)
  cases hp₀ : e8PosParent p₀ with
  | none =>
    rw [e8_ht_le_one_simple hp₀]
    exact e8Serre_adE_sq_gen k (simpleOfPos p₀)
  | some kp1 =>
    rcases kp1 with ⟨m, p₁⟩
    have hlt1 : e8PosHeight p₁ < e8PosHeight p₀ := e8PosParent_ht_lt hp₀
    have hlt1n : e8PosHeight p₁ ≤ n := by omega
    rw [e8SerrePosVec_parent hp₀]
    have had : ⁅e8SerreE k, ⁅e8SerreE k, ⁅e8SerreE m, e8SerrePosVec p₁⁆⁆⁆ =
        ⁅⁅e8SerreE k, ⁅e8SerreE k, e8SerreE m⁆⁆, e8SerrePosVec p₁⁆ +
        (2 : ℝ) • ⁅⁅e8SerreE k, e8SerreE m⁆, ⁅e8SerreE k, e8SerrePosVec p₁⁆⁆ +
        ⁅e8SerreE m, ⁅e8SerreE k, ⁅e8SerreE k, e8SerrePosVec p₁⁆⁆⁆ := by
      rw [leibniz_lie (e8SerreE k) (e8SerreE m) (e8SerrePosVec p₁), lie_add]
      rw [leibniz_lie (e8SerreE k) ⁅e8SerreE k, e8SerreE m⁆ (e8SerrePosVec p₁)]
      rw [leibniz_lie (e8SerreE k) (e8SerreE m) ⁅e8SerreE k, e8SerrePosVec p₁⁆]
      rw [two_smul]
      abel
    rw [had, e8Serre_adE_sq_gen k m, zero_lie, zero_add]
    have hmid : ⁅⁅e8SerreE k, e8SerreE m⁆, ⁅e8SerreE k, e8SerrePosVec p₁⁆⁆ = 0 := by
      by_cases hkm : CartanMatrix.E 8 k m = 0
      · rw [e8Serre_adE_zero hkm, zero_lie]
      · by_cases hkm_eq : k = m
        · subst hkm_eq; simp [lie_self]
        · have hup := e8_adSq_mid_up_none hp hp₀ hkm hkm_eq
          rw [ih p₁ hlt1n k, hup, evalPosUp, lie_zero]
    have hend : ⁅e8SerreE k, ⁅e8SerreE k, e8SerrePosVec p₁⁆⁆ = 0 := by
      rw [ih p₁ hlt1n k]
      cases hup : e8PosUp k p₁ with
      | none => simp [evalPosUp]
      | some sq =>
        rcases sq with ⟨s, q⟩
        have hq_ht : e8PosHeight q ≤ e8PosHeight p₁ + 1 := e8PosUp_ht_le hup
        have hq_le : e8PosHeight q ≤ n := by
          have := e8PosParent_ht_succ hp₀
          omega
        have hup2 := e8_adSq_end_up_none hp hp₀ hup
        cases s <;> simp [evalPosUp, ih q hq_le k, hup2]
    rw [hmid, smul_zero, zero_add, hend, lie_zero]

private theorem e8Serre_adE_posVec :
    ∀ (n : ℕ) (p : Fin 120), e8PosHeight p ≤ n → ∀ i : Fin 8,
      ⁅e8SerreE i, e8SerrePosVec p⁆ = evalPosUp (e8PosUp i p) := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have := e8PosHeight_pos p
    omega
  | succ n ih =>
    intro p hn i
    cases hp : e8PosParent p with
    | none => exact e8_pos_base_ht1 i p hp
    | some kp₀ =>
      rcases kp₀ with ⟨k, p₀⟩
      have hlt0 : e8PosHeight p₀ ≤ n := by
        have := e8PosParent_ht_succ hp
        omega
      by_cases hik : i = k
      · subst hik
        rw [e8_diag_up_none hp, evalPosUp]
        exact e8_ad_sq_posVec_eq_zero n ih p hn i p₀ hp
      · by_cases hcart : CartanMatrix.E 8 i k = 0
        · rw [e8SerrePosVec_parent hp]
          rw [leibniz_lie (e8SerreE i) (e8SerreE k) (e8SerrePosVec p₀)]
          rw [e8Serre_adE_zero hcart, zero_lie, zero_add, ih p₀ hlt0 i]
          cases hup0 : e8PosUp i p₀ with
          | none =>
            rw [e8_comm_up_none hp hik hcart hup0, evalPosUp, lie_zero]
          | some sq1 =>
            rcases sq1 with ⟨s₀, q₁⟩
            cases hself : isSelfParent i p
            · rcases e8_comm_up_other_parent hp hik hcart hup0 hself with ⟨q, hup, hparq⟩
              rw [hup]
              cases s₀ <;> simp [evalPosUp, lie_neg, e8SerrePosVec_parent hparq]
            · have hself' := hself
              unfold isSelfParent at hself'
              cases hup : e8PosUp i p with
              | none => rw [hup] at hself'; contradiction
              | some sq =>
                rcases sq with ⟨s, q⟩
                rw [hup] at hself'
                cases s
                · contradiction
                · have hparq : e8PosParent q = some (i, p) := by simpa using hself'
                  have hs1 := e8_comm_up_self_parent hp hik hcart hup0 hself
                  subst hs1
                  rw [evalPosUp, evalPosUp]
                  calc ⁅e8SerreE k, e8SerrePosVec q₁⁆
                      = ⁅e8SerreE k, ⁅e8SerreE i, e8SerrePosVec p₀⁆⁆ := by
                          have := ih p₀ hlt0 i
                          rw [hup0, evalPosUp] at this
                          rw [this]
                    _ = ⁅e8SerreE i, ⁅e8SerreE k, e8SerrePosVec p₀⁆⁆ := by
                          rw [leibniz_lie (e8SerreE k) (e8SerreE i) (e8SerrePosVec p₀)]
                          rw [e8Serre_adE_zero (e8_cartan_symm_zero hcart), zero_lie, zero_add]
                    _ = ⁅e8SerreE i, e8SerrePosVec p⁆ := by rw [e8SerrePosVec_parent hp]
                    _ = e8SerrePosVec q := (e8SerrePosVec_parent hparq).symm
        · have hcart1 : CartanMatrix.E 8 i k = -1 :=
            (CartanMatrix.isSimplyLaced_E 8 hik).resolve_left hcart
          cases hself : isSelfParent i p
          · have hup := e8_adj_up_none hp hik hcart hself
            rw [hup, evalPosUp]
            cases hp₀ : e8PosParent p₀ with
            | none =>
              have hsi := e8_adj_ht2_simple hp hik hcart hself hp₀
              rw [e8SerrePosVec_parent hp, e8_ht_le_one_simple hp₀, hsi]
              rw [← lie_skew (e8SerreE k) (e8SerreE i), lie_neg,
                e8Serre_adE_negOne hcart1, neg_zero]
            | some mp₁ =>
              rcases mp₁ with ⟨m, p₁⟩
              have hlt1n : e8PosHeight p₁ ≤ n := by
                have := e8PosParent_ht_lt hp₀
                omega
              by_cases hmi : m = i
              · subst hmi
                obtain ⟨hup_kp1, hup_mp0⟩ := e8_adj_mi_up_none hp hik hcart hself hp₀
                rw [e8SerrePosVec_parent hp, e8SerrePosVec_parent hp₀]
                have h1 : ⁅e8SerreE m, ⁅e8SerreE m, e8SerrePosVec p₁⁆⁆ = 0 := by
                  rw [← e8SerrePosVec_parent hp₀, ih p₀ hlt0 m, hup_mp0, evalPosUp]
                have h2 : ⁅e8SerreE m, ⁅e8SerreE m, ⁅e8SerreE k, e8SerrePosVec p₁⁆⁆⁆ = 0 := by
                  rw [ih p₁ hlt1n k, hup_kp1, evalPosUp, lie_zero, lie_zero]
                have h2sm := two_smul_bracket_eq_ad_sq (e8Serre_adE_negOne hcart1) h1
                rw [h2] at h2sm
                exact (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
              · by_cases hcomm_km : CartanMatrix.E 8 k m = 0 ∧ CartanMatrix.E 8 i m = 0
                · rw [e8SerrePosVec_parent hp, e8SerrePosVec_parent hp₀]
                  rw [leibniz_lie (e8SerreE k) (e8SerreE m) (e8SerrePosVec p₁),
                    e8Serre_adE_zero hcomm_km.1, zero_lie, zero_add]
                  rw [leibniz_lie (e8SerreE i) (e8SerreE m) ⁅e8SerreE k, e8SerrePosVec p₁⁆,
                    e8Serre_adE_zero hcomm_km.2, zero_lie, zero_add]
                  obtain ⟨s, q, hupk, hupi⟩ :=
                    e8_adj_comm_m_witness hp hik hcart hself hp₀ hmi hcomm_km
                  have hq_le : e8PosHeight q ≤ n := by
                    have hq_ht := e8PosUp_ht_le hupk
                    have hp0_ht := e8PosParent_ht_succ hp₀
                    omega
                  have hres : ⁅e8SerreE i, ⁅e8SerreE k, e8SerrePosVec p₁⁆⁆ = 0 := by
                    rw [ih p₁ hlt1n k, hupk]
                    cases s <;> simp [evalPosUp, lie_neg, ih q hq_le i, hupi]
                  rw [hres, lie_zero]
                · obtain ⟨hr_lt, ⟨s_r, hu_ir⟩, hu_kr, hu_ip0⟩ :=
                    e8_adj_rem_witness_ok hp hik hcart hself hp₀ hmi hcomm_km
                  set r := e8AdjRemWitness i p
                  have hr_le : e8PosHeight r ≤ n := by omega
                  have hir := ih r hr_le i
                  rw [hu_ir] at hir
                  have hkr : ⁅e8SerreE k, e8SerrePosVec r⁆ = 0 := by
                    have h := ih r hr_le k
                    rw [hu_kr, evalPosUp] at h
                    exact h
                  have hip0 : ⁅e8SerreE i, e8SerrePosVec p₀⁆ = 0 := by
                    have h := ih p₀ hlt0 i
                    rw [hu_ip0, evalPosUp] at h
                    exact h
                  rw [e8SerrePosVec_parent hp]
                  cases s_r
                  · dsimp only [evalPosUp] at hir
                    have hp0_eq : e8SerrePosVec p₀ = -⁅e8SerreE i, e8SerrePosVec r⁆ := by
                      rw [hir, neg_neg]
                    have hsq : ⁅e8SerreE i, ⁅e8SerreE i, e8SerrePosVec r⁆⁆ = 0 := by
                      rw [← neg_eq_zero, ← lie_neg, ← hp0_eq, hip0]
                    have h2sm := two_smul_bracket_eq_ad_sq (e8Serre_adE_negOne hcart1) hsq
                    rw [hkr, lie_zero, lie_zero] at h2sm
                    have h0 := (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
                    rw [hp0_eq, lie_neg, lie_neg, h0]
                    norm_num
                  · dsimp only [evalPosUp] at hir
                    have hp0_eq : e8SerrePosVec p₀ = ⁅e8SerreE i, e8SerrePosVec r⁆ := hir.symm
                    have hsq : ⁅e8SerreE i, ⁅e8SerreE i, e8SerrePosVec r⁆⁆ = 0 := by
                      rw [← hp0_eq, hip0]
                    have h2sm := two_smul_bracket_eq_ad_sq (e8Serre_adE_negOne hcart1) hsq
                    rw [hkr, lie_zero, lie_zero] at h2sm
                    rw [hp0_eq]
                    exact (smul_eq_zero.mp h2sm).resolve_left (by norm_num)
          · unfold isSelfParent at hself
            cases hup : e8PosUp i p with
            | none => rw [hup] at hself; contradiction
            | some sq =>
              rcases sq with ⟨s, q⟩
              rw [hup] at hself
              cases s
              · contradiction
              · have hparq : e8PosParent q = some (i, p) := by simpa using hself
                rw [evalPosUp, e8SerrePosVec_parent hparq]

/-! #### 248-dimensional spanning submodule and triangular decomposition -/

private noncomputable def e8SerrePosSpan : Submodule ℝ (LieAlgebra.e₈ ℝ) :=
  Submodule.span ℝ (Set.range e8SerrePosVec)

private noncomputable def e8SerreCartan : Submodule ℝ (LieAlgebra.e₈ ℝ) :=
  Submodule.span ℝ (Set.range e8SerreH)

private noncomputable def e8SerreNegVec (p : Fin 120) : LieAlgebra.e₈ ℝ :=
  e8SerreChevalleyInv (e8SerrePosVec p)

private noncomputable def e8SerreNegSpan : Submodule ℝ (LieAlgebra.e₈ ℝ) :=
  Submodule.span ℝ (Set.range e8SerreNegVec)

private noncomputable def e8SerreSpan248 : Submodule ℝ (LieAlgebra.e₈ ℝ) :=
  e8SerreNegSpan ⊔ e8SerreCartan ⊔ e8SerrePosSpan

private theorem e8SerrePosVec_mem_posSpan (p : Fin 120) :
    e8SerrePosVec p ∈ e8SerrePosSpan :=
  Submodule.subset_span ⟨p, rfl⟩

private theorem e8SerreE_mem_posSpan (i : Fin 8) :
    e8SerreE i ∈ e8SerrePosSpan := by
  rw [← e8SerrePosVec_simple i]
  exact e8SerrePosVec_mem_posSpan _

private theorem e8SerreH_mem_cartan (i : Fin 8) :
    e8SerreH i ∈ e8SerreCartan :=
  Submodule.subset_span ⟨i, rfl⟩

private theorem e8SerreF_mem_negSpan (i : Fin 8) :
    e8SerreF i ∈ e8SerreNegSpan := by
  have h : e8SerreF i = e8SerreNegVec (simplePosIdx i) := by
    simp [e8SerreNegVec, e8SerrePosVec_simple]
  rw [h]
  exact Submodule.subset_span ⟨simplePosIdx i, rfl⟩

private theorem evalPosUp_mem_posSpan (o : Option (Bool × Fin 120)) :
    evalPosUp o ∈ e8SerrePosSpan := by
  cases o with
  | none => exact e8SerrePosSpan.zero_mem
  | some bq =>
    rcases bq with ⟨b, q⟩
    cases b with
    | true => exact e8SerrePosVec_mem_posSpan q
    | false => exact e8SerrePosSpan.neg_mem (e8SerrePosVec_mem_posSpan q)

private theorem e8Serre_adE_posVec_mem (i : Fin 8) (p : Fin 120) :
    ⁅e8SerreE i, e8SerrePosVec p⁆ ∈ e8SerrePosSpan := by
  rw [e8Serre_adE_posVec 29 p (e8PosHeight_le_29 p) i]
  exact evalPosUp_mem_posSpan _

private theorem e8Serre_adE_posSpan_mem (i : Fin 8) {y : LieAlgebra.e₈ ℝ}
    (hy : y ∈ e8SerrePosSpan) : ⁅e8SerreE i, y⁆ ∈ e8SerrePosSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e8SerrePosSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e8SerrePosSpan.smul_mem c ha
  | mem _ hp =>
    rcases hp with ⟨p, rfl⟩
    exact e8Serre_adE_posVec_mem i p

private theorem e8Serre_adE_cartan_mem (i : Fin 8) {y : LieAlgebra.e₈ ℝ}
    (hy : y ∈ e8SerreCartan) : ⁅e8SerreE i, y⁆ ∈ e8SerrePosSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e8SerrePosSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e8SerrePosSpan.smul_mem c ha
  | mem _ hj =>
    rcases hj with ⟨j, rfl⟩
    rw [← lie_skew (e8SerreE i) (e8SerreH j), e8Serre_bracket_HE, ← neg_smul]
    exact e8SerrePosSpan.smul_mem _ (e8SerreE_mem_posSpan i)

private theorem e8Serre_adH_posVec_mem (i : Fin 8) :
    ∀ p : Fin 120, ⁅e8SerreH i, e8SerrePosVec p⁆ ∈ e8SerrePosSpan := by
  intro p
  induction hp_val : p.val using Nat.strong_induction_on generalizing p with
  | h n ih =>
    subst hp_val
    cases hp : e8PosParent p with
    | none =>
      rw [e8_ht_le_one_simple hp, e8Serre_bracket_HE]
      exact e8SerrePosSpan.smul_mem _ (e8SerreE_mem_posSpan _)
    | some kp₀ =>
      rcases kp₀ with ⟨k, p₀⟩
      have hlt : p₀.val < p.val := e8PosParent_lt hp
      rw [e8SerrePosVec_parent hp,
        leibniz_lie (e8SerreH i) (e8SerreE k) (e8SerrePosVec p₀),
        e8Serre_bracket_HE, smul_lie]
      refine e8SerrePosSpan.add_mem ?_ ?_
      · exact e8SerrePosSpan.smul_mem _ (e8Serre_adE_posVec_mem k p₀)
      · exact e8Serre_adE_posSpan_mem k (ih p₀.val hlt p₀ rfl)

private theorem e8Serre_adF_posVec_mem (i : Fin 8) :
    ∀ (n : ℕ) (p : Fin 120), e8PosHeight p ≤ n →
      ⁅e8SerreF i, e8SerrePosVec p⁆ ∈ e8SerrePosSpan ⊔ e8SerreCartan := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have := e8PosHeight_pos p
    omega
  | succ n ih =>
    intro p hp
    cases hpar : e8PosParent p with
    | none =>
      rw [e8_ht_le_one_simple hpar, ← lie_skew (e8SerreF i) (e8SerreE (simpleOfPos p))]
      by_cases hij : simpleOfPos p = i
      · rw [hij, e8Serre_bracket_EF_same]
        exact Submodule.mem_sup_right (e8SerreCartan.neg_mem (e8SerreH_mem_cartan i))
      · rw [e8Serre_bracket_EF_ne hij, neg_zero]
        exact (e8SerrePosSpan ⊔ e8SerreCartan).zero_mem
    | some kp₀ =>
      rcases kp₀ with ⟨k, p₀⟩
      have hlt : e8PosHeight p₀ ≤ n := by
        have := e8PosParent_ht_succ hpar
        omega
      rw [e8SerrePosVec_parent hpar,
        leibniz_lie (e8SerreF i) (e8SerreE k) (e8SerrePosVec p₀)]
      refine (e8SerrePosSpan ⊔ e8SerreCartan).add_mem ?_ ?_
      · rw [← lie_skew (e8SerreF i) (e8SerreE k)]
        by_cases hik : k = i
        · rw [hik, e8Serre_bracket_EF_same, neg_lie]
          exact Submodule.mem_sup_left
            (e8SerrePosSpan.neg_mem (e8Serre_adH_posVec_mem i p₀))
        · rw [e8Serre_bracket_EF_ne hik, neg_zero, zero_lie]
          exact (e8SerrePosSpan ⊔ e8SerreCartan).zero_mem
      · have hih := ih p₀ hlt
        rw [Submodule.mem_sup] at hih
        rcases hih with ⟨u, hu, v, hv, huv⟩
        rw [← huv, lie_add]
        exact Submodule.mem_sup_left
          (e8SerrePosSpan.add_mem (e8Serre_adE_posSpan_mem k hu)
            (e8Serre_adE_cartan_mem k hv))

private def submoduleLieNormalizer (S : Submodule ℝ (LieAlgebra.e₈ ℝ)) :
    LieSubalgebra ℝ (LieAlgebra.e₈ ℝ) where
  carrier := { x | ∀ y ∈ S, ⁅x, y⁆ ∈ S }
  zero_mem' y _ := by simp
  add_mem' hx hy y hyS := by rw [add_lie]; exact S.add_mem (hx y hyS) (hy y hyS)
  smul_mem' c x hx y hyS := by rw [smul_lie]; exact S.smul_mem c (hx y hyS)
  lie_mem' hx₁ hx₂ y hyS := by
    rw [lie_lie]
    exact S.sub_mem (hx₁ _ (hx₂ y hyS)) (hx₂ _ (hx₁ y hyS))

private theorem chevalley_posSpan_mem_negSpan {x : LieAlgebra.e₈ ℝ}
    (hx : x ∈ e8SerrePosSpan) : e8SerreChevalleyInv x ∈ e8SerreNegSpan := by
  induction hx using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [map_add]; exact e8SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [map_smul]; exact e8SerreNegSpan.smul_mem c ha
  | mem _ hq =>
    rcases hq with ⟨q, rfl⟩
    exact Submodule.subset_span ⟨q, rfl⟩

private theorem chevalley_mem_span248_of_pos_cartan {x : LieAlgebra.e₈ ℝ}
    (hx : x ∈ e8SerrePosSpan ⊔ e8SerreCartan) :
    e8SerreChevalleyInv x ∈ e8SerreSpan248 := by
  rw [Submodule.mem_sup] at hx
  rcases hx with ⟨u, hu, v, hv, rfl⟩
  rw [map_add]
  refine Submodule.mem_sup_left (Submodule.add_mem _ ?_ ?_)
  · exact Submodule.mem_sup_left (chevalley_posSpan_mem_negSpan hu)
  · apply Submodule.mem_sup_right
    induction hv using Submodule.span_induction with
    | zero => simp
    | add _ _ _ _ ha hb => rw [map_add]; exact e8SerreCartan.add_mem ha hb
    | smul c _ _ ha => rw [map_smul]; exact e8SerreCartan.smul_mem c ha
    | mem _ hj =>
      rcases hj with ⟨j, rfl⟩
      rw [e8SerreChevalleyInv_H]
      exact e8SerreCartan.neg_mem (e8SerreH_mem_cartan j)

private theorem e8Serre_adH_negSpan_mem (i : Fin 8) {y : LieAlgebra.e₈ ℝ}
    (hy : y ∈ e8SerreNegSpan) : ⁅e8SerreH i, y⁆ ∈ e8SerreNegSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e8SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e8SerreNegSpan.smul_mem c ha
  | mem _ hp =>
    rcases hp with ⟨p, rfl⟩
    have heq : ⁅e8SerreH i, e8SerreNegVec p⁆ =
        -e8SerreChevalleyInv ⁅e8SerreH i, e8SerrePosVec p⁆ := by
      rw [LieEquiv.map_lie, e8SerreChevalleyInv_H, neg_lie, neg_neg]
      rfl
    rw [heq]
    exact e8SerreNegSpan.neg_mem (chevalley_posSpan_mem_negSpan (e8Serre_adH_posVec_mem i p))

private theorem e8Serre_adH_cartan_mem (i : Fin 8) {y : LieAlgebra.e₈ ℝ}
    (hy : y ∈ e8SerreCartan) : ⁅e8SerreH i, y⁆ ∈ e8SerreCartan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e8SerreCartan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e8SerreCartan.smul_mem c ha
  | mem _ hj =>
    rcases hj with ⟨j, rfl⟩
    rw [e8SerreH_comm]
    exact e8SerreCartan.zero_mem

private theorem e8Serre_adH_posSpan_mem (i : Fin 8) {y : LieAlgebra.e₈ ℝ}
    (hy : y ∈ e8SerrePosSpan) : ⁅e8SerreH i, y⁆ ∈ e8SerrePosSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e8SerrePosSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e8SerrePosSpan.smul_mem c ha
  | mem _ hp =>
    rcases hp with ⟨p, rfl⟩
    exact e8Serre_adH_posVec_mem i p

private theorem e8Serre_adE_negSpan_mem (i : Fin 8) {y : LieAlgebra.e₈ ℝ}
    (hy : y ∈ e8SerreNegSpan) : ⁅e8SerreE i, y⁆ ∈ e8SerreSpan248 := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e8SerreSpan248.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e8SerreSpan248.smul_mem c ha
  | mem _ hp =>
    rcases hp with ⟨p, rfl⟩
    have heq : ⁅e8SerreE i, e8SerreNegVec p⁆ =
        e8SerreChevalleyInv ⁅e8SerreF i, e8SerrePosVec p⁆ := by
      rw [LieEquiv.map_lie, e8SerreChevalleyInv_F]; rfl
    rw [heq]
    exact chevalley_mem_span248_of_pos_cartan
      (e8Serre_adF_posVec_mem i 29 p (e8PosHeight_le_29 p))

private theorem e8Serre_adF_negSpan_mem (i : Fin 8) {y : LieAlgebra.e₈ ℝ}
    (hy : y ∈ e8SerreNegSpan) : ⁅e8SerreF i, y⁆ ∈ e8SerreNegSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e8SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e8SerreNegSpan.smul_mem c ha
  | mem _ hp =>
    rcases hp with ⟨p, rfl⟩
    have heq : ⁅e8SerreF i, e8SerreNegVec p⁆ =
        e8SerreChevalleyInv ⁅e8SerreE i, e8SerrePosVec p⁆ := by
      rw [LieEquiv.map_lie, e8SerreChevalleyInv_E]; rfl
    rw [heq]
    exact chevalley_posSpan_mem_negSpan (e8Serre_adE_posVec_mem i p)

private theorem e8Serre_adF_cartan_mem (i : Fin 8) {y : LieAlgebra.e₈ ℝ}
    (hy : y ∈ e8SerreCartan) : ⁅e8SerreF i, y⁆ ∈ e8SerreNegSpan := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e8SerreNegSpan.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e8SerreNegSpan.smul_mem c ha
  | mem _ hj =>
    rcases hj with ⟨j, rfl⟩
    rw [← lie_skew (e8SerreF i) (e8SerreH j), e8Serre_bracket_HF, ← neg_smul]
    exact e8SerreNegSpan.smul_mem _ (e8SerreF_mem_negSpan i)

private theorem e8Serre_adF_posSpan_mem (i : Fin 8) {y : LieAlgebra.e₈ ℝ}
    (hy : y ∈ e8SerrePosSpan) : ⁅e8SerreF i, y⁆ ∈ e8SerreSpan248 := by
  induction hy using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ha hb => rw [lie_add]; exact e8SerreSpan248.add_mem ha hb
  | smul c _ _ ha => rw [lie_smul]; exact e8SerreSpan248.smul_mem c ha
  | mem _ hp =>
    rcases hp with ⟨p, rfl⟩
    have hmem := e8Serre_adF_posVec_mem i 29 p (e8PosHeight_le_29 p)
    rw [Submodule.mem_sup] at hmem
    rcases hmem with ⟨u, hu, v, hv, huv⟩
    rw [← huv]
    exact e8SerreSpan248.add_mem (Submodule.mem_sup_right hu)
      (Submodule.mem_sup_left (Submodule.mem_sup_right hv))

private theorem e8Serre_span248_ad_invariant (x : LieAlgebra.e₈ ℝ)
    (hx : x ∈ (Set.range e8SerreH ∪ Set.range e8SerreE ∪ Set.range e8SerreF)) :
    x ∈ submoduleLieNormalizer e8SerreSpan248 := by
  intro y hy
  have hy' : y ∈ e8SerreNegSpan ⊔ e8SerreCartan ⊔ e8SerrePosSpan := hy
  rcases Submodule.mem_sup.mp hy' with ⟨y₁, hy₁, y₃, hy₃, rfl⟩
  rcases Submodule.mem_sup.mp hy₁ with ⟨y_neg, hy_neg, y_car, hy_car, rfl⟩
  rw [lie_add, lie_add]
  rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact e8SerreSpan248.add_mem
      (e8SerreSpan248.add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left (e8Serre_adH_negSpan_mem i hy_neg)))
        (Submodule.mem_sup_left (Submodule.mem_sup_right (e8Serre_adH_cartan_mem i hy_car))))
      (Submodule.mem_sup_right (e8Serre_adH_posSpan_mem i hy₃))
  · exact e8SerreSpan248.add_mem
      (e8SerreSpan248.add_mem
        (e8Serre_adE_negSpan_mem i hy_neg)
        (Submodule.mem_sup_right (e8Serre_adE_cartan_mem i hy_car)))
      (Submodule.mem_sup_right (e8Serre_adE_posSpan_mem i hy₃))
  · exact e8SerreSpan248.add_mem
      (e8SerreSpan248.add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left (e8Serre_adF_negSpan_mem i hy_neg)))
        (Submodule.mem_sup_left (Submodule.mem_sup_left (e8Serre_adF_cartan_mem i hy_car))))
      (e8Serre_adF_posSpan_mem i hy₃)

private theorem e8Serre_span248_eq_top : e8SerreSpan248 = ⊤ := by
  have hnorm : submoduleLieNormalizer e8SerreSpan248 = ⊤ := by
    apply e8Serre_generators_generate
    · intro i
      exact e8Serre_span248_ad_invariant _ (Or.inl (Or.inl ⟨i, rfl⟩))
    · intro i
      exact e8Serre_span248_ad_invariant _ (Or.inl (Or.inr ⟨i, rfl⟩))
    · intro i
      exact e8Serre_span248_ad_invariant _ (Or.inr ⟨i, rfl⟩)
  let S_lie : LieSubalgebra ℝ (LieAlgebra.e₈ ℝ) :=
    { e8SerreSpan248 with
      lie_mem' := fun {x y} _ hy => by
        have hx_norm : x ∈ submoduleLieNormalizer e8SerreSpan248 := by rw [hnorm]; trivial
        exact hx_norm y hy }
  have htop : S_lie = ⊤ := by
    apply e8Serre_generators_generate
    · intro i
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (e8SerreH_mem_cartan i))
    · intro i
      exact Submodule.mem_sup_right (e8SerreE_mem_posSpan i)
    · intro i
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (e8SerreF_mem_negSpan i))
  exact congrArg LieSubalgebra.toSubmodule htop

private noncomputable def e8SerreSpanVec :
    Fin 8 ⊕ Fin 120 ⊕ Fin 120 → LieAlgebra.e₈ ℝ :=
  Sum.elim e8SerreH (Sum.elim e8SerrePosVec e8SerreNegVec)

private theorem e8SerreSpanVec_span_eq_top :
    Submodule.span ℝ (Set.range e8SerreSpanVec) = ⊤ := by
  rw [← e8Serre_span248_eq_top]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨idx, rfl⟩
    rcases idx with i | p | p
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (e8SerreH_mem_cartan i))
    · exact Submodule.mem_sup_right (e8SerrePosVec_mem_posSpan p)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨p, rfl⟩))
  · refine sup_le (sup_le ?_ ?_) ?_
    · dsimp only [e8SerreNegSpan]
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr (Sum.inr p), rfl⟩
    · dsimp only [e8SerreCartan]
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · dsimp only [e8SerrePosSpan]
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span ⟨Sum.inr (Sum.inl p), rfl⟩

/-- `LieAlgebra.e₈ ℝ` is finite-dimensional, spanned by the 248 Chevalley elements. -/
instance e8Serre_finiteDimensional : FiniteDimensional ℝ (LieAlgebra.e₈ ℝ) := by
  have : Module.Finite ℝ (Submodule.span ℝ (Set.range e8SerreSpanVec)) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range e8SerreSpanVec)
  exact Module.Finite.equiv
    ((LinearEquiv.ofEq _ ⊤ e8SerreSpanVec_span_eq_top).trans Submodule.topEquiv)

/-- The Serre presentation of `E₈` over `ℝ` has dimension at most `248`. -/
theorem finrank_e8_serre_le : Module.finrank ℝ (LieAlgebra.e₈ ℝ) ≤ 248 := by
  have h := finrank_le_of_span_eq_top e8SerreSpanVec_span_eq_top
  simpa using h

/-! ## 4. Isomorphism, Exact Dimension (`248`), and Simplicity of `LieAlgebra.e₈ ℝ` -/

/-- The descended Serre quotient homomorphism `LieAlgebra.e₈ ℝ →ₗ⁅ℝ⁆ SplitE8Lie`
is injective. -/
theorem splitE8SerreQuotientMap_injective :
    Function.Injective splitE8SerreQuotientMap := by
  let f := splitE8SerreQuotientMap.toLinearMap
  have hrange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr splitE8SerreQuotientMap_surjective
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, finrank_splitE8Lie] at hrank
  have hle : Module.finrank ℝ (LieAlgebra.e₈ ℝ) ≤ 248 := finrank_e8_serre_le
  have hker0 : Module.finrank ℝ (LinearMap.ker f) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker0)

/-- **E₈ Serre Isomorphism**: Mathlib's Serre quotient `LieAlgebra.e₈ ℝ` is isomorphic
as a real Lie algebra to the split `𝔈₈(8)` Magic-Square algebra `SplitE8Lie`. -/
noncomputable def splitE8SerreEquiv :
    LieAlgebra.e₈ ℝ ≃ₗ⁅ℝ⁆ SplitE8Lie :=
  LieEquiv.ofBijective splitE8SerreQuotientMap
    ⟨splitE8SerreQuotientMap_injective, splitE8SerreQuotientMap_surjective⟩

/-- Mathlib's Serre presentation `LieAlgebra.e₈ ℝ` has exact dimension `248`. -/
theorem finrank_e8_serre : Module.finrank ℝ (LieAlgebra.e₈ ℝ) = 248 := by
  rw [LinearEquiv.finrank_eq splitE8SerreEquiv.toLinearEquiv, finrank_splitE8Lie]

/-- Mathlib's Serre presentation `LieAlgebra.e₈ ℝ` is a simple real Lie algebra. -/
instance e8Serre_isSimple : LieAlgebra.IsSimple ℝ (LieAlgebra.e₈ ℝ) where
  eq_bot_or_eq_top I := by
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top
        (I.map (splitE8SerreEquiv : LieAlgebra.e₈ ℝ →ₗ⁅ℝ⁆ SplitE8Lie)) with
      hbot | htop
    · exact Or.inl (LieIdeal.bot_of_map_eq_bot splitE8SerreEquiv.injective hbot)
    · right
      rw [eq_top_iff]
      intro x _
      have hx : (splitE8SerreEquiv : LieAlgebra.e₈ ℝ →ₗ⁅ℝ⁆ SplitE8Lie) x ∈
          I.map (splitE8SerreEquiv : LieAlgebra.e₈ ℝ →ₗ⁅ℝ⁆ SplitE8Lie) := by
        rw [htop]
        trivial
      obtain ⟨y, hy⟩ := LieIdeal.mem_map_of_surjective splitE8SerreEquiv.surjective hx
      have hyx : (y : LieAlgebra.e₈ ℝ) = x := splitE8SerreEquiv.injective hy
      rw [← hyx]
      exact y.2
  non_abelian := by
    rw [lie_abelian_iff_equiv_lie_abelian splitE8SerreEquiv]
    exact LieAlgebra.IsSimple.non_abelian ℝ

end InfoGeometry.Algebra
