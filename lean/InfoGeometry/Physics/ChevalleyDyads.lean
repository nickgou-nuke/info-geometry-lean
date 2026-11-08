/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ChevalleySpinorIdeal
import Mathlib.RingTheory.Idempotents
import InfoGeometry.Core.FinitePeirceMatrix

/-!
# Chevalley Dyads: Kets, Bras, and Matrix Units in Cℓ(1,1)

This module formalizes Claude Chevalley's identification of matrix dyads
`|I⟩⟨J|` with Clifford left and right ideals `p_I e₀ n_J`, at the categorical
level (endomorphisms in a preadditive category), composing with the existing
categorical Chevalley algebra of `ChevalleySpinorIdeal`.

## Causal Poset of Archetypes

```
1. CAR pair (n, p) — root: n²=0, p²=0, np+pn=𝟙
2. Vacuum idempotent e₀ = n≫p — e₀²=e₀, n≫e₀=0, e₀≫p=0
3. Kets and bras — |0⟩=e₀, |1⟩=p≫e₀=p, ⟨0|=e₀, ⟨1|=e₀≫n=n
4. Dyadic matrix units — E00=|0⟩⟨0|, E01=|0⟩⟨1|, E10=|1⟩⟨0|, E11=|1⟩⟨1|
5. Closed forms — E00=n≫p, E01=n, E10=p, E11=p≫n
6. 16 multiplication laws — E_ij≫E_kl = δ_jk E_il
7. Resolution of unity — E00+E11=𝟙
8. Generator reconstruction — n=E01, p=E10, τ₃=E00-E11, τ₁=E01+E10
9. Universal operator expansion — A = Σ E_ij≫A≫E_kl
```

All results are genuine definitions, lemmas, and theorems with complete proofs.
-/

namespace InfoGeometry.Physics.ChevalleyDyads

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Physics.Chevalley

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. The Vacuum Idempotent -/

/-- The primitive vacuum idempotent `e₀ = n ≫ p`. -/
@[inline]
def e0 {X : C} (n p : X ⟶ X) : X ⟶ X := n ≫ p

/-- Annihilation kills the vacuum on the left: `n ≫ e₀ = 0`. -/
theorem n_annihilates_vacuum {X : C} (n p : X ⟶ X) (hn : n ≫ n = 0) :
    n ≫ e0 n p = 0 := by
  show n ≫ (n ≫ p) = 0
  rw [← Category.assoc, hn, zero_comp]

/-- Creation kills the vacuum on the right: `e₀ ≫ p = 0`. -/
theorem vacuum_annihilates_p {X : C} (n p : X ⟶ X) (hp : p ≫ p = 0) :
    e0 n p ≫ p = 0 := by
  show (n ≫ p) ≫ p = 0
  rw [Category.assoc, hp, comp_zero]

/-- Creation acting on the vacuum gives the single-particle state: `p ≫ e₀ = p`. -/
theorem p_comp_e0 {X : C} (n p : X ⟶ X)
    (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    p ≫ e0 n p = p := by
  show p ≫ (n ≫ p) = p
  have h_pn : p ≫ n = 𝟙 X - n ≫ p := by rw [← hcar]; abel
  rw [← Category.assoc, h_pn, Preadditive.sub_comp, Category.id_comp,
      Category.assoc, hp, comp_zero, sub_zero]

/-- Annihilation acting on the vacuum bra gives the dual bra: `e₀ ≫ n = n`. -/
theorem e0_comp_n {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    e0 n p ≫ n = n := by
  show (n ≫ p) ≫ n = n
  have h_pn : p ≫ n = 𝟙 X - n ≫ p := by rw [← hcar]; abel
  rw [Category.assoc, h_pn, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, hn, zero_comp, sub_zero]

/-- The vacuum operator is idempotent: `e₀ ≫ e₀ = e₀`. -/
theorem e0_idempotent {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    e0 n p ≫ e0 n p = e0 n p := cat_P_plus_sq n p hn hcar

/-! ### 2. Minimal Left and Right Ideals (Kets and Bras) -/

/-- Vacuum ket `|0⟩ = e₀`. -/
@[inline]
def ket0 {X : C} (n p : X ⟶ X) : X ⟶ X := e0 n p

/-- Excited ket `|1⟩ = p ≫ e₀`. -/
@[inline]
def ket1 {X : C} (n p : X ⟶ X) : X ⟶ X := p ≫ e0 n p

/-- Vacuum bra `⟨0| = e₀`. -/
@[inline]
def bra0 {X : C} (n p : X ⟶ X) : X ⟶ X := e0 n p

/-- Excited bra `⟨1| = e₀ ≫ n`. -/
@[inline]
def bra1 {X : C} (n p : X ⟶ X) : X ⟶ X := e0 n p ≫ n

/-- Ket identification: `|1⟩ = p`. -/
theorem ket1_eq_p {X : C} (n p : X ⟶ X)
    (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    ket1 n p = p := p_comp_e0 n p hp hcar

/-- Bra identification: `⟨1| = n`. -/
theorem bra1_eq_n {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    bra1 n p = n := e0_comp_n n p hn hcar

/-! ### 3. Dyadic Matrix Units -/

/-- General dyad constructor `|u⟩⟨v| = u ≫ v`. -/
@[inline]
def dyad {X : C} (u v : X ⟶ X) : X ⟶ X := u ≫ v

/-- Matrix unit `E₀₀ = |0⟩⟨0|`. -/
@[inline]
def E00 {X : C} (n p : X ⟶ X) : X ⟶ X := dyad (ket0 n p) (bra0 n p)

/-- Matrix unit `E₀₁ = |0⟩⟨1|`. -/
@[inline]
def E01 {X : C} (n p : X ⟶ X) : X ⟶ X := dyad (ket0 n p) (bra1 n p)

/-- Matrix unit `E₁₀ = |1⟩⟨0|`. -/
@[inline]
def E10 {X : C} (n p : X ⟶ X) : X ⟶ X := dyad (ket1 n p) (bra0 n p)

/-- Matrix unit `E₁₁ = |1⟩⟨1|`. -/
@[inline]
def E11 {X : C} (n p : X ⟶ X) : X ⟶ X := dyad (ket1 n p) (bra1 n p)

/-! ### 4. Closed Form Identifications -/

/-- `E₀₀ = n ≫ p`. -/
theorem E00_eq_np {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E00 n p = n ≫ p := e0_idempotent n p hn hcar

/-- `E₀₁ = n`. -/
theorem E01_eq_n {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E01 n p = n := by
  show e0 n p ≫ (e0 n p ≫ n) = n
  rw [e0_comp_n n p hn hcar, e0_comp_n n p hn hcar]

/-- `E₁₀ = p`. -/
theorem E10_eq_p {X : C} (n p : X ⟶ X)
    (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E10 n p = p := by
  show (p ≫ e0 n p) ≫ e0 n p = p
  rw [p_comp_e0 n p hp hcar, p_comp_e0 n p hp hcar]

/-- `E₁₁ = p ≫ n`. -/
theorem E11_eq_pn {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E11 n p = p ≫ n := by
  show (p ≫ e0 n p) ≫ (e0 n p ≫ n) = p ≫ n
  rw [p_comp_e0 n p hp hcar, e0_comp_n n p hn hcar]

/-! ### 5. All 16 Matrix Unit Multiplication Laws -/

/-- `E₀₀ ≫ E₀₀ = E₀₀`. -/
theorem E00_mul_E00 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E00 n p ≫ E00 n p = E00 n p := by
  rw [E00_eq_np n p hn hcar]
  exact e0_idempotent n p hn hcar

/-- `E₀₀ ≫ E₀₁ = E₀₁`. -/
theorem E00_mul_E01 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E00 n p ≫ E01 n p = E01 n p := by
  rw [E00_eq_np n p hn hcar, E01_eq_n n p hn hcar]
  exact e0_comp_n n p hn hcar

/-- `E₀₀ ≫ E₁₀ = 0`. -/
theorem E00_mul_E10 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E00 n p ≫ E10 n p = 0 := by
  rw [E00_eq_np n p hn hcar, E10_eq_p n p hp hcar]
  exact vacuum_annihilates_p n p hp

/-- `E₀₀ ≫ E₁₁ = 0`. -/
theorem E00_mul_E11 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E00 n p ≫ E11 n p = 0 := by
  rw [E00_eq_np n p hn hcar, E11_eq_pn n p hn hp hcar]
  show (n ≫ p) ≫ (p ≫ n) = 0
  rw [Category.assoc, ← Category.assoc p p n, hp, zero_comp, comp_zero]

/-- `E₀₁ ≫ E₀₀ = 0`. -/
theorem E01_mul_E00 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E01 n p ≫ E00 n p = 0 := by
  rw [E01_eq_n n p hn hcar, E00_eq_np n p hn hcar]
  exact n_annihilates_vacuum n p hn

/-- `E₀₁ ≫ E₀₁ = 0`. -/
theorem E01_mul_E01 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E01 n p ≫ E01 n p = 0 := by
  rw [E01_eq_n n p hn hcar]
  exact hn

/-- `E₀₁ ≫ E₁₀ = E₀₀`. -/
theorem E01_mul_E10 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E01 n p ≫ E10 n p = E00 n p := by
  rw [E01_eq_n n p hn hcar, E10_eq_p n p hp hcar, E00_eq_np n p hn hcar]

/-- `E₀₁ ≫ E₁₁ = E₀₁`. -/
theorem E01_mul_E11 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E01 n p ≫ E11 n p = E01 n p := by
  rw [E01_eq_n n p hn hcar, E11_eq_pn n p hn hp hcar]
  show n ≫ (p ≫ n) = n
  rw [← Category.assoc]
  exact e0_comp_n n p hn hcar

/-- `E₁₀ ≫ E₀₀ = E₁₀`. -/
theorem E10_mul_E00 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E10 n p ≫ E00 n p = E10 n p := by
  rw [E10_eq_p n p hp hcar, E00_eq_np n p hn hcar]
  exact p_comp_e0 n p hp hcar

/-- `E₁₀ ≫ E₀₁ = E₁₁`. -/
theorem E10_mul_E01 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E10 n p ≫ E01 n p = E11 n p := by
  rw [E10_eq_p n p hp hcar, E01_eq_n n p hn hcar, E11_eq_pn n p hn hp hcar]

/-- `E₁₀ ≫ E₁₀ = 0`. -/
theorem E10_mul_E10 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E10 n p ≫ E10 n p = 0 := by
  rw [E10_eq_p n p hp hcar]
  exact hp

/-- `E₁₀ ≫ E₁₁ = 0`. -/
theorem E10_mul_E11 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E10 n p ≫ E11 n p = 0 := by
  rw [E10_eq_p n p hp hcar, E11_eq_pn n p hn hp hcar]
  show p ≫ (p ≫ n) = 0
  rw [← Category.assoc, hp, zero_comp]

/-- `E₁₁ ≫ E₀₀ = 0`. -/
theorem E11_mul_E00 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E11 n p ≫ E00 n p = 0 := by
  rw [E11_eq_pn n p hn hp hcar, E00_eq_np n p hn hcar]
  show (p ≫ n) ≫ (n ≫ p) = 0
  rw [Category.assoc, ← Category.assoc n n p, hn, zero_comp, comp_zero]

/-- `E₁₁ ≫ E₀₁ = 0`. -/
theorem E11_mul_E01 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E11 n p ≫ E01 n p = 0 := by
  rw [E11_eq_pn n p hn hp hcar, E01_eq_n n p hn hcar]
  show (p ≫ n) ≫ n = 0
  rw [Category.assoc, hn, comp_zero]

/-- `E₁₁ ≫ E₁₀ = E₁₀`. -/
theorem E11_mul_E10 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E11 n p ≫ E10 n p = E10 n p := by
  rw [E11_eq_pn n p hn hp hcar, E10_eq_p n p hp hcar]
  show (p ≫ n) ≫ p = p
  rw [Category.assoc]
  exact p_comp_e0 n p hp hcar

/-- `E₁₁ ≫ E₁₁ = E₁₁`. -/
theorem E11_mul_E11 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E11 n p ≫ E11 n p = E11 n p := by
  rw [E11_eq_pn n p hn hp hcar]
  exact cat_P_minus_sq n p hp hcar

/-! ### 6. Resolution of Unity and Generator Reconstruction -/

/-- Resolution of unity: `E₀₀ + E₁₁ = 𝟙 X`. -/
theorem resolution_of_unity {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    E00 n p + E11 n p = 𝟙 X := by
  rw [E00_eq_np n p hn hcar, E11_eq_pn n p hn hp hcar]
  exact hcar

/-- The annihilation operator is the transition dyad: `n = E₀₁`. -/
theorem n_is_E01 {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    n = E01 n p := by
  rw [E01_eq_n n p hn hcar]

/-- The creation operator is the transition dyad: `p = E₁₀`. -/
theorem p_is_E10 {X : C} (n p : X ⟶ X)
    (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    p = E10 n p := by
  rw [E10_eq_p n p hp hcar]

/-- The charge grading decomposes into diagonal dyads: `n≫p - p≫n = E₀₀ - E₁₁`. -/
theorem tau3_is_diagonal_dyads {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    n ≫ p - p ≫ n = E00 n p - E11 n p := by
  rw [E00_eq_np n p hn hcar, E11_eq_pn n p hn hp hcar]

/-- The particle-hole exchange decomposes into off-diagonal dyads: `n + p = E₀₁ + E₁₀`. -/
theorem tau1_is_off_diagonal_dyads {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    n + p = E01 n p + E10 n p := by
  rw [E01_eq_n n p hn hcar, E10_eq_p n p hp hcar]

/-! ### 7. Universal Operator Dyadic Expansion -/

/-- Any endomorphism decomposes into the four coordinate dyads via the resolution
of unity: `A = E₀₀≫A≫E₀₀ + E₀₀≫A≫E₁₁ + E₁₁≫A≫E₀₀ + E₁₁≫A≫E₁₁`. -/
theorem operator_dyadic_expansion {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X)
    (A : X ⟶ X) :
    A = E00 n p ≫ A ≫ E00 n p +
        E00 n p ≫ A ≫ E11 n p +
        E11 n p ≫ A ≫ E00 n p +
        E11 n p ≫ A ≫ E11 n p := by
  have h_id := resolution_of_unity n p hn hp hcar
  calc A = (E00 n p + E11 n p) ≫ A ≫ (E00 n p + E11 n p) := by
        rw [h_id, Category.id_comp, Category.comp_id]
    _ = E00 n p ≫ A ≫ E00 n p +
          E00 n p ≫ A ≫ E11 n p +
          E11 n p ≫ A ≫ E00 n p +
          E11 n p ≫ A ≫ E11 n p := by
          simp only [Preadditive.add_comp, Preadditive.comp_add]
          abel

/-! ### 8. CAR endomorphisms as constrained Peirce matrices

The endomorphism ring uses the convention `f * g = g ≫ f`.  Passing to its
opposite makes multiplication agree with categorical composition.  The
existing finite Peirce matrix owner then gives coordinates in the four
projector corners.  These are constrained block matrices, not unrestricted
matrices over `ℤ` and not yet matrices over a single corner ring.
-/

/-- Endomorphism scalars with multiplication ordered as categorical composition. -/
abbrev EndOp (X : C) := (End X)ᵐᵒᵖ

/-- The two CAR projectors, viewed in the composition-ordered endomorphism ring. -/
def carPeirceIdempotents {X : C} (n p : X ⟶ X) : Fin 2 → EndOp X :=
  ![(MulOpposite.op (n ≫ p) : EndOp X),
    (MulOpposite.op (p ≫ n) : EndOp X)]

/-- The CAR projectors form a complete orthogonal pair in the opposite endomorphism ring. -/
theorem carPeirceIdempotents_complete {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    CompleteOrthogonalIdempotents (carPeirceIdempotents n p) := by
  have h01 : (n ≫ p) ≫ (p ≫ n) = 0 := by
    calc
      (n ≫ p) ≫ (p ≫ n) = n ≫ (p ≫ p) ≫ n := by simp only [Category.assoc]
      _ = 0 := by rw [hp]; simp
  have h10 : (p ≫ n) ≫ (n ≫ p) = 0 := by
    calc
      (p ≫ n) ≫ (n ≫ p) = p ≫ (n ≫ n) ≫ p := by simp only [Category.assoc]
      _ = 0 := by rw [hn]; simp
  change CompleteOrthogonalIdempotents
    ![(MulOpposite.op (n ≫ p) : EndOp X),
      (MulOpposite.op (p ≫ n) : EndOp X)]
  rw [CompleteOrthogonalIdempotents.pair_iff'ₛ]
  refine ⟨?_, ?_, ?_⟩
  · change MulOpposite.op ((n ≫ p) ≫ (p ≫ n)) = 0
    exact congrArg MulOpposite.op h01
  · change MulOpposite.op ((p ≫ n) ≫ (n ≫ p)) = 0
    exact congrArg MulOpposite.op h10
  · change MulOpposite.op (n ≫ p + p ≫ n) = MulOpposite.op (𝟙 X)
    exact congrArg MulOpposite.op hcar

/-- The CAR pair gives the canonical linear coordinates in its four Peirce corners.

This reuses `FinitePeirceMatrix.cornerEquiv`; the target records the actual
corner constraints on each matrix entry. -/
noncomputable def carPeirceCoordinates {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    EndOp X ≃ₗ[ℤ]
      InfoGeometry.Core.FinitePeirceMatrix.cornerSpace (K := ℤ)
        (carPeirceIdempotents n p) :=
  InfoGeometry.Core.FinitePeirceMatrix.cornerEquiv
    (K := ℤ) (carPeirceIdempotents n p)
    (carPeirceIdempotents_complete n p hn hp hcar)

/-- Each coordinate is cut out by its corresponding pair of CAR projectors. -/
theorem carPeirceCoordinates_apply {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) (A : EndOp X) (i j : Fin 2) :
    (carPeirceCoordinates n p hn hp hcar A).1 i j =
      carPeirceIdempotents n p i * A * carPeirceIdempotents n p j := rfl

/-- Peirce matrix coordinates preserve operator multiplication. -/
theorem carPeirceCoordinates_mul {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) (A B : EndOp X) :
    (carPeirceCoordinates n p hn hp hcar (A * B)).1 =
      (carPeirceCoordinates n p hn hp hcar A).1 *
        (carPeirceCoordinates n p hn hp hcar B).1 := by
  exact InfoGeometry.Core.FinitePeirceMatrix.blocks_mul (carPeirceIdempotents n p)
    (carPeirceIdempotents_complete n p hn hp hcar) A B

/-- The identity has the diagonal CAR projectors as its Peirce coordinates. -/
theorem carPeirceCoordinates_one {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    (carPeirceCoordinates n p hn hp hcar 1).1 =
      Matrix.diagonal (carPeirceIdempotents n p) := by
  exact InfoGeometry.Core.FinitePeirceMatrix.blocks_one (carPeirceIdempotents n p)
    (carPeirceIdempotents_complete n p hn hp hcar)

end InfoGeometry.Physics.ChevalleyDyads
