/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
import InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Native Mathlib Positivity and Categorical Colimit for the Krein–Zorn Tower

Bridges the finite-stage star-ring identities in
`InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis` to native Mathlib
structures:
1. **Order-theoretic positivity (`StarOrderedRing`)**:
   - `towerTrace_star_mul_self_nonneg`: in any `[Ring B] [PartialOrder B]
     [IsOrderedAddMonoid B] [StarRing B] [StarOrderedRing B]`, `0 ≤ towerTrace (star A * A)`
     for every `A : ClTower B n`.
   - `positive_sector_krein_pairing_nonneg`: on any self-adjoint `+1`-sector
     projection `P` (`kroneckerGamma γ₀ n * P = P`), the Krein pairing
     `towerTrace (kreinAdjoint γ₀ n (P * X * P) * (P * X * P))` is genuinely `≥ 0`.
   - `zorn_twisted_hs_trace_nonneg`: `0 ≤ Matrix.trace ((gamma1Op * vecOp u₁ u₂ u₃)ᴴ * ...)`.
   - `wick_rotated_dirac_trace_nonneg`: `0 ≤ Matrix.trace (D_Eᴴ * D_E)`.
2. **Native Mathlib `CategoryTheory.Limits.colimit` in `RingCat`**:
   - `diagEmbedRingHom` and `clTowerHom` for `m ≤ n`.
   - `clTowerFunctor : ℕ ⥤ RingCat`, `ClTowerColimit B := colimit (clTowerFunctor B)`,
     and `clTowerColimit_ι_comp`.
   - `clTowerHom_kreinAdjoint`: `clTowerHom` commutes with `kreinAdjoint` at all
     scales `m ≤ n`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
open InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction
open InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis

namespace InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge

universe u

section StarOrderedPositivity

variable {B : Type u} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
  [StarRing B] [StarOrderedRing B]

/-- Native Mathlib `StarOrderedRing` positivity of `towerTrace (star A * A)` at every
depth `n : ℕ`. -/
theorem towerTrace_star_mul_self_nonneg :
    ∀ {n : ℕ} (A : ClTower B n), (0 : B) ≤ towerTrace (star A * A)
  | 0, A => star_mul_self_nonneg A
  | _ + 1, A => by
      dsimp [towerTrace]
      have h00 : (star A * A) 0 0 = star (A 0 0) * A 0 0 + star (A 1 0) * A 1 0 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      have h11 : (star A * A) 1 1 = star (A 0 1) * A 0 1 + star (A 1 1) * A 1 1 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [h00, h11, towerTrace_add, towerTrace_add]
      exact add_nonneg
        (add_nonneg (towerTrace_star_mul_self_nonneg (A 0 0))
          (towerTrace_star_mul_self_nonneg (A 1 0)))
        (add_nonneg (towerTrace_star_mul_self_nonneg (A 0 1))
          (towerTrace_star_mul_self_nonneg (A 1 1)))

/-- Ghost-excised Krein pairing on any `+1`-sector self-adjoint projection `P` is
non-negative in any `StarOrderedRing`. -/
theorem positive_sector_krein_pairing_nonneg
    {γ₀ : B} (hγ₀_star : star γ₀ = γ₀)
    (n : ℕ) (P X : ClTower B n)
    (hP_star : star P = P)
    (hP_pos : kroneckerGamma γ₀ n * P = P) :
    (0 : B) ≤ towerTrace (kreinAdjoint γ₀ n (P * X * P) * (P * X * P)) := by
  have h := (positive_sector_ghost_excision hγ₀_star n P X X hP_star hP_pos).2.2.2
  rw [h]
  exact towerTrace_star_mul_self_nonneg (P * X * P)

/-- Krein-twisted Hilbert-Schmidt trace of the Zorn 3-vector operator is non-negative
in any `StarOrderedRing`. -/
theorem zorn_twisted_hs_trace_nonneg (u₁ u₂ u₃ : B) :
    let V : Matrix (Fin 2) (Fin 2) B := vecOp u₁ u₂ u₃
    (0 : B) ≤ Matrix.trace ((gamma1Op * V)ᴴ * (gamma1Op * V)) := by
  intro V
  rw [(zorn_vecOp_krein_signature_and_twisted_positivity u₁ u₂ u₃).2.2.2.2.2]
  rw [two_smul]
  have hsum : (0 : B) ≤ star u₁ * u₁ + star u₂ * u₂ + star u₃ * u₃ :=
    add_nonneg (add_nonneg (star_mul_self_nonneg u₁) (star_mul_self_nonneg u₂))
      (star_mul_self_nonneg u₃)
  exact add_nonneg hsum hsum

/-- Hilbert-Schmidt trace of the Wick-rotated Dirac operator square is non-negative
in any `StarOrderedRing`. -/
theorem wick_rotated_dirac_trace_nonneg (Dp Dm U : B) :
    let D_E := gamma1Op * kreinDiracOp Dp Dm U
    (0 : B) ≤ Matrix.trace (D_Eᴴ * D_E) := by
  intro D_E
  have htr : Matrix.trace (D_Eᴴ * D_E) =
      (star (D_E 0 0) * D_E 0 0 + star (D_E 1 0) * D_E 1 0) +
        (star (D_E 0 1) * D_E 0 1 + star (D_E 1 1) * D_E 1 1) := by
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  rw [htr]
  exact add_nonneg
    (add_nonneg (star_mul_self_nonneg (D_E 0 0)) (star_mul_self_nonneg (D_E 1 0)))
    (add_nonneg (star_mul_self_nonneg (D_E 0 1)) (star_mul_self_nonneg (D_E 1 1)))

end StarOrderedPositivity

section RingCatColimit

open CategoryTheory CategoryTheory.Limits

variable {B : Type u} [Ring B]

/-- `diagEmbed` as a unital `RingHom` `ClTower B n →+* ClTower B (n + 1)`. -/
def diagEmbedRingHom (n : ℕ) : ClTower B n →+* ClTower B (n + 1) where
  toFun := diagEmbed
  map_one' := by apply ext_fin2 <;> simp [diagEmbed]
  map_mul' X Y := by apply ext_fin2 <;> simp [diagEmbed]
  map_zero' := by apply ext_fin2 <;> simp [diagEmbed]
  map_add' X Y := by apply ext_fin2 <;> simp [diagEmbed]

private def clTowerCast (B : Type u) [Ring B] {m n : ℕ} (h : m = n) :
    ClTower B m →+* ClTower B n := by
  subst h
  exact RingHom.id (ClTower B m)

@[simp] private lemma clTowerCast_rfl (B : Type u) [Ring B] {m : ℕ} (h : m = m)
    (x : ClTower B m) :
    (clTowerCast B h) x = x := rfl

/-- Directed system of unital ring homomorphisms `ClTower B m →+* ClTower B n`
for `m ≤ n`. -/
def clTowerHom (B : Type u) [Ring B] : ∀ {m n : ℕ}, m ≤ n → (ClTower B m →+* ClTower B n)
  | _, 0, h =>
      clTowerCast B (Nat.le_zero.mp h)
  | m, n + 1, h =>
      if h_eq : m = n + 1 then
        clTowerCast B h_eq
      else
        (diagEmbedRingHom n).comp (clTowerHom B (Nat.le_of_lt_succ (lt_of_le_of_ne h h_eq)))

lemma clTowerHom_refl (n : ℕ) (x : ClTower B n) :
    clTowerHom B (le_refl n) x = x := by
  cases n with
  | zero => rfl
  | succ n => simp [clTowerHom]; rfl

lemma clTowerHom_step {m n : ℕ} (h : m ≤ n) (x : ClTower B m) :
    clTowerHom B (Nat.le_succ_of_le h) x = diagEmbed (clTowerHom B h x) := by
  have hne : m ≠ n + 1 := Nat.ne_of_lt (Nat.lt_succ_of_le h)
  simp [clTowerHom, hne, diagEmbedRingHom]

lemma clTowerHom_trans {m k n : ℕ} (hmk : m ≤ k) (hkn : k ≤ n) (x : ClTower B m) :
    clTowerHom B (le_trans hmk hkn) x = clTowerHom B hkn (clTowerHom B hmk x) := by
  induction n with
  | zero =>
      obtain rfl : k = 0 := Nat.le_zero.mp hkn
      obtain rfl : m = 0 := Nat.le_zero.mp hmk
      rfl
  | succ n ih =>
      by_cases hkn_eq : k = n + 1
      · subst hkn_eq
        rw [clTowerHom_refl]
      · have hkn_lt : k ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hkn hkn_eq)
        rw [clTowerHom_step (le_trans hmk hkn_lt) x]
        rw [clTowerHom_step hkn_lt (clTowerHom B hmk x)]
        exact congrArg diagEmbed (ih hkn_lt)

/-- Native Mathlib `RingCat` functor `ℕ ⥤ RingCat` for the `ClTower B` system. -/
noncomputable def clTowerFunctor (B : Type u) [Ring B] : ℕ ⥤ RingCat where
  obj n := RingCat.of (ClTower B n)
  map {m n} f := RingCat.ofHom (clTowerHom B (leOfHom f))
  map_id n := by
    ext x
    exact clTowerHom_refl n x
  map_comp {m k n} f g := by
    ext x
    exact clTowerHom_trans (leOfHom f) (leOfHom g) x

/-- Native Mathlib `CategoryTheory.Limits.colimit` of `clTowerFunctor B` in `RingCat`. -/
noncomputable abbrev ClTowerColimit (B : Type u) [Ring B] : RingCat :=
  colimit (clTowerFunctor B)

/-- Colimit cocone compatibility for `clTowerHom` into `ClTowerColimit B`. -/
theorem clTowerColimit_ι_comp {m n : ℕ} (h : m ≤ n) (x : ClTower B m) :
    (colimit.ι (clTowerFunctor B) n).hom (clTowerHom B h x) =
      (colimit.ι (clTowerFunctor B) m).hom x := by
  have hw := colimit.w (clTowerFunctor B) (homOfLE h)
  exact congrArg (fun f => f.hom x) hw

/-- `clTowerHom` commutes with `kreinAdjoint` across all scales `m ≤ n`. -/
theorem clTowerHom_kreinAdjoint [StarRing B]
    (γ₀ : B) : ∀ {m n : ℕ} (h : m ≤ n) (x : ClTower B m),
    clTowerHom B h (kreinAdjoint γ₀ m x) = kreinAdjoint γ₀ n (clTowerHom B h x)
  | m, 0, h, x => by
      obtain rfl : m = 0 := Nat.le_zero.mp h
      rfl
  | m, n + 1, h, x => by
      by_cases h_eq : m = n + 1
      · subst h_eq
        simp [clTowerHom]
        rfl
      · have h_lt : m ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne h h_eq)
        have ih := clTowerHom_kreinAdjoint γ₀ h_lt x
        rw [clTowerHom_step h_lt (kreinAdjoint γ₀ m x)]
        rw [clTowerHom_step h_lt x]
        rw [ih]
        exact (diagEmbed_kreinAdjoint_and_trace_bott_scaling γ₀ n (clTowerHom B h_lt x)
          (clTowerHom B h_lt x)).1.symm

end RingCatColimit

section YangMillsSpectralActionPositivity

variable {B : Type u} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
  [StarRing B] [StarOrderedRing B]

/-- The finite-stage Yang--Mills--Higgs quartic trace from the spectral-action
owner is nonnegative in a native `StarOrderedRing`. This connects its exact
noncommutative sum-of-squares formula to Mathlib's order structure; it does not
assert positivity for arbitrary matrix traces or an analytic action. -/
theorem unified_yang_mills_higgs_spectral_action_nonneg
    (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁ := d₁ + A₁
    let D₂ := d₂ + A₂
    let D₃ := d₃ + A₃
    let D := (diracZornOp m (-m) D₁ D₂ D₃ D₁ D₂ D₃ : NestedMat B)
    (0 : B) ≤ trace4 ((D ^ 2)ᴴ * D ^ 2) := by
  let D₁ := d₁ + A₁
  let D₂ := d₂ + A₂
  let D₃ := d₃ + A₃
  let Δ := m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)
  let F₂₃ := ymFieldStrength d₂ d₃ A₂ A₃
  let F₃₁ := ymFieldStrength d₃ d₁ A₃ A₁
  let F₁₂ := ymFieldStrength d₁ d₂ A₁ A₂
  let D := (diracZornOp m (-m) D₁ D₂ D₃ D₁ D₂ D₃ : NestedMat B)
  dsimp only [D, D₁, D₂, D₃]
  rw [unified_yang_mills_higgs_dirac_spectral_action m d₁ d₂ d₃ A₁ A₂ A₃
    h23 h31 h12]
  apply nsmul_nonneg
  exact add_nonneg
    (add_nonneg (star_mul_self_nonneg _)
      (add_nonneg (add_nonneg (star_mul_self_nonneg _) (star_mul_self_nonneg _))
        (star_mul_self_nonneg _)))
    (add_nonneg (add_nonneg (star_mul_self_nonneg _) (star_mul_self_nonneg _))
      (star_mul_self_nonneg _))

end YangMillsSpectralActionPositivity

end InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
