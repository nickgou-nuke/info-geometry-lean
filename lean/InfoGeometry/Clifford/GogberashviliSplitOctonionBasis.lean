import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Algebra.Zorn.ConcreteComposition

/-!
# Gogberashvili split-octonion basis with εₙₘₖ multiplication table

This module defines the **explicit Gogberashvili basis** `{1, J₀, J₁, J₂, j₀, j₁, j₂, I}`
on the canonical Zorn algebra (8D), and proves the multiplication table from
Gogberashvili & Sakhelashvili, *Advances in Mathematical Physics* 2015, eq. (5):

```
Jₙ Jₘ = -Jₘ Jₙ = -εₙₘₖ jₖ
jₙ jₘ = -jₘ jₙ = -εₙₘₖ jₖ
jₘ Jₙ = -Jₙ jₘ = -εₙₘₖ Jₖ
Jₙ I = -I Jₙ = -jₙ
jₙ I = -I jₙ = -Jₙ
```

with squares `Jₙ² = +1`, `jₙ² = -1`, `I² = +1`.

The basis elements are explicit linear combinations in the 8D Zorn coordinates:
* Scalar `1` = (1, 1, 0, 0, 0, 0, 0, 0)
* `Jₙ` = (0, 0, eₙ, eₙ)   [r=0, s=0, upper=eₙ, lower=eₙ]
* `jₙ` = (0, 0, eₙ, -eₙ)  [r=0, s=0, upper=eₙ, lower=-eₙ]
* `I`  = (1, -1, 0, 0)    [r=1, s=-1, upper=0, lower=0]

All proofs are by `norm_num` on the concrete Zorn multiplication from `ConcreteComposition.lean`.
-/

noncomputable section

namespace InfoGeometry.Clifford.GogberashviliSplitOctonionBasis

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open Fin
open Matrix

/-- Levi-Civita symbol εₙₘₖ on `Fin 3`. -/
def eps3 (i j k : Fin 3) : ℝ :=
  match i.val, j.val, k.val with
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 1, 0, 2 => -1
  | 0, 2, 1 => -1
  | 2, 1, 0 => -1
  | _, _, _ => 0

/-- Negation of a Zorn cell (since there is no `Neg` instance). -/
def negZ (X : ZornCell ℝ) : ZornCell ℝ :=
  ⟨-X.r, -X.s, -X.x1, -X.x2, -X.x3, -X.y1, -X.y2, -X.y3⟩

/-- Scalar multiplication on ZornCell ℝ. -/
def smulZ (c : ℝ) (X : ZornCell ℝ) : ZornCell ℝ :=
  ⟨c * X.r, c * X.s, c * X.x1, c * X.x2, c * X.x3, c * X.y1, c * X.y2, c * X.y3⟩

instance instSMulZornCellReal : SMul ℝ (ZornCell ℝ) where
  smul := smulZ

/-- Componentwise addition on ZornCell ℝ. -/
def addZ (X Y : ZornCell ℝ) : ZornCell ℝ :=
  ⟨X.r + Y.r, X.s + Y.s, X.x1 + Y.x1, X.x2 + Y.x2, X.x3 + Y.x3, X.y1 + Y.y1, X.y2 + Y.y2, X.y3 + Y.y3⟩

instance instAddZornCellReal : Add (ZornCell ℝ) where
  add := addZ

/-- Zero Zorn cell. -/
def zeroZ : ZornCell ℝ :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

instance instZeroZornCellReal : Zero (ZornCell ℝ) where
  zero := zeroZ

instance instOfNatZornCellReal : OfNat (ZornCell ℝ) 0 where
  ofNat := zeroZ

lemma zero_val : (0 : ZornCell ℝ) = zeroZ := rfl
lemma addZ_val (X Y : ZornCell ℝ) : X + Y = addZ X Y := rfl
lemma smulZ_val (c : ℝ) (X : ZornCell ℝ) : c • X = smulZ c X := rfl

/-- Canonical Zorn scalar unit `1 = (1, 1, 0, 0, 0, 0, 0, 0)`. -/
def oneZ : ZornCell ℝ :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

/-- Pseudoscalar `I = (1, -1, 0, 0, 0, 0, 0, 0)`. -/
def I : ZornCell ℝ :=
  ⟨1, -1, 0, 0, 0, 0, 0, 0⟩

/-- Vector-like unit `Jₙ` for `n : Fin 3`. -/
def J (n : Fin 3) : ZornCell ℝ :=
  match n with
  | ⟨0, _⟩ => ⟨0, 0, 1, 0, 0, 1, 0, 0⟩  -- J₀ = (0, 0, 1, 0, 0, 1, 0, 0)
  | ⟨1, _⟩ => ⟨0, 0, 0, 1, 0, 0, 1, 0⟩  -- J₁ = (0, 0, 0, 1, 0, 0, 1, 0)
  | ⟨2, _⟩ => ⟨0, 0, 0, 0, 1, 0, 0, 1⟩  -- J₂ = (0, 0, 0, 0, 1, 0, 0, 1)

/-- Pseudovector-like unit `jₙ` for `n : Fin 3`. -/
def j (n : Fin 3) : ZornCell ℝ :=
  match n with
  | ⟨0, _⟩ => ⟨0, 0, 1, 0, 0, -1, 0, 0⟩  -- j₀ = (0, 0, 1, 0, 0, -1, 0, 0)
  | ⟨1, _⟩ => ⟨0, 0, 0, 1, 0, 0, -1, 0⟩  -- j₁ = (0, 0, 0, 1, 0, 0, -1, 0)
  | ⟨2, _⟩ => ⟨0, 0, 0, 0, 1, 0, 0, -1⟩  -- j₂ = (0, 0, 0, 0, 1, 0, 0, -1)

/-- Helper: sum over Fin 3. -/
def sumFin3 (f : Fin 3 → ZornCell ℝ) : ZornCell ℝ :=
  f 0 + f 1 + f 2

/-- Check equality of two Zorn cells by components. -/
lemma zorn_ext {X Y : ZornCell ℝ}
    (hr : X.r = Y.r) (hs : X.s = Y.s)
    (hx1 : X.x1 = Y.x1) (hx2 : X.x2 = Y.x2) (hx3 : X.x3 = Y.x3)
    (hy1 : X.y1 = Y.y1) (hy2 : X.y2 = Y.y2) (hy3 : X.y3 = Y.y3) : X = Y := by
  cases X; cases Y; simp_all

/-!
### Squares: Jₙ² = +1, jₙ² = -1, I² = +1
-/

theorem J_sq (n : Fin 3) : J n * J n = oneZ := by
  fin_cases n
  all_goals
    change mulZ (J _) (J _) = oneZ
    unfold J
    split <;> rename_i heq <;> cases heq
    apply zorn_ext <;> dsimp only [ZornCell.mulZ, oneZ] <;> norm_num

theorem j_sq (n : Fin 3) : j n * j n = negZ oneZ := by
  fin_cases n
  all_goals
    change mulZ (j _) (j _) = negZ oneZ
    unfold j
    split <;> rename_i heq <;> cases heq
    apply zorn_ext <;> dsimp only [ZornCell.mulZ, negZ, oneZ] <;> norm_num

theorem I_sq : I * I = oneZ := by
  change mulZ I I = oneZ
  apply zorn_ext <;> dsimp only [ZornCell.mulZ, I, oneZ] <;> norm_num

/-
### Anticommutation: Jₙ Jₘ = -Jₘ Jₙ for n ≠ m, etc.
-/

theorem J_anticomm (n m : Fin 3) (h : n ≠ m) : J n * J m = negZ (J m * J n) := by
  fin_cases n <;> fin_cases m <;> (revert h; dsimp only; intro h) <;> (try contradiction)
  all_goals
    change mulZ (J _) (J _) = negZ (mulZ (J _) (J _))
    unfold J
    split <;> rename_i heq <;> cases heq
    apply zorn_ext <;> dsimp only [ZornCell.mulZ, negZ] <;> norm_num

theorem j_anticomm (n m : Fin 3) (h : n ≠ m) : j n * j m = negZ (j m * j n) := by
  fin_cases n <;> fin_cases m <;> (revert h; dsimp only; intro h) <;> (try contradiction)
  all_goals
    change mulZ (j _) (j _) = negZ (mulZ (j _) (j _))
    unfold j
    split <;> rename_i heq <;> cases heq
    apply zorn_ext <;> dsimp only [ZornCell.mulZ, negZ] <;> norm_num

/-
### Cross products with εₙₘₖ

The full multiplication table uses the Levi-Civita symbol.
-/

theorem J_mul_J (n m : Fin 3) (h : n ≠ m) : J n * J m = negZ (sumFin3 (fun k => (eps3 n m k : ℝ) • j k)) := by
  fin_cases n <;> fin_cases m <;> (revert h; dsimp only; intro h) <;> (try contradiction)
  all_goals
    change mulZ (J _) (J _) = negZ (sumFin3 (fun k => (eps3 _ _ k : ℝ) • j k))
    unfold J j eps3 sumFin3
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, eps3] <;> norm_num

theorem j_mul_j (n m : Fin 3) (h : n ≠ m) : j n * j m = negZ (sumFin3 (fun k => (eps3 n m k : ℝ) • j k)) := by
  fin_cases n <;> fin_cases m <;> (revert h; dsimp only; intro h) <;> (try contradiction)
  all_goals
    change mulZ (j _) (j _) = negZ (sumFin3 (fun k => (eps3 _ _ k : ℝ) • j k))
    unfold j eps3 sumFin3
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, eps3] <;> norm_num

theorem j_mul_J (n m : Fin 3) (h : n ≠ m) : j m * J n = negZ (sumFin3 (fun k => (eps3 n m k : ℝ) • J k)) := by
  fin_cases n <;> fin_cases m <;> (revert h; dsimp only; intro h) <;> (try contradiction)
  all_goals
    change mulZ (j _) (J _) = negZ (sumFin3 (fun k => (eps3 _ _ k : ℝ) • J k))
    unfold J j eps3 sumFin3
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, eps3] <;> norm_num

/-
### Mixed products with I

Jₙ I = -jₙ
I Jₙ = jₙ
jₙ I = -Jₙ
I jₙ = Jₙ
-/

theorem J_mul_I (n : Fin 3) : J n * I = negZ (j n) := by
  fin_cases n
  all_goals
    change mulZ (J _) I = negZ (j _)
    unfold J j I
    apply zorn_ext <;> dsimp only [ZornCell.mulZ, negZ, J, j, I] <;> norm_num

theorem I_mul_J (n : Fin 3) : I * J n = j n := by
  fin_cases n
  all_goals
    change mulZ I (J _) = j _
    unfold I J j
    apply zorn_ext <;> dsimp only [ZornCell.mulZ, I, J, j] <;> norm_num

theorem j_mul_I (n : Fin 3) : j n * I = negZ (J n) := by
  fin_cases n
  all_goals
    change mulZ (j _) I = negZ (J _)
    unfold j J I
    apply zorn_ext <;> dsimp only [ZornCell.mulZ, negZ, j, J, I] <;> norm_num

theorem I_mul_j (n : Fin 3) : I * j n = J n := by
  fin_cases n
  all_goals
    change mulZ I (j _) = J _
    unfold I j J
    apply zorn_ext <;> dsimp only [ZornCell.mulZ, I, j, J] <;> norm_num

/-
### Zero divisors (Gogberashvili Appendix E)

Dₙ⁺ = (1 + Jₙ)/2  (idempotent)
Dₙ⁻ = (1 - Jₙ)/2  (idempotent)
Gₙ⁺ = (I + jₙ)/2  (nilpotent)
Gₙ⁻ = (I - jₙ)/2  (nilpotent)
-/

noncomputable def D_plus (n : Fin 3) : ZornCell ℝ := (1 / 2 : ℝ) • (oneZ + J n)
noncomputable def D_minus (n : Fin 3) : ZornCell ℝ := (1 / 2 : ℝ) • (oneZ + negZ (J n))
noncomputable def G_plus (n : Fin 3) : ZornCell ℝ := (1 / 2 : ℝ) • (I + j n)
noncomputable def G_minus (n : Fin 3) : ZornCell ℝ := (1 / 2 : ℝ) • (I + negZ (j n))

theorem D_plus_idempotent (n : Fin 3) : D_plus n * D_plus n = D_plus n := by
  fin_cases n
  all_goals
    change mulZ (D_plus _) (D_plus _) = D_plus _
    unfold D_plus oneZ J
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, oneZ, J] <;> norm_num

theorem D_minus_idempotent (n : Fin 3) : D_minus n * D_minus n = D_minus n := by
  fin_cases n
  all_goals
    change mulZ (D_minus _) (D_minus _) = D_minus _
    unfold D_minus oneZ J
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, oneZ, J] <;> norm_num

theorem D_plus_mul_D_minus (n : Fin 3) : D_plus n * D_minus n = 0 := by
  fin_cases n
  all_goals
    change mulZ (D_plus _) (D_minus _) = 0
    unfold D_plus D_minus oneZ J
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, oneZ, J] <;> norm_num

theorem D_minus_mul_D_plus (n : Fin 3) : D_minus n * D_plus n = 0 := by
  fin_cases n
  all_goals
    change mulZ (D_minus _) (D_plus _) = 0
    unfold D_minus D_plus oneZ J
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, oneZ, J] <;> norm_num

theorem G_plus_nilpotent (n : Fin 3) : G_plus n * G_plus n = 0 := by
  fin_cases n
  all_goals
    change mulZ (G_plus _) (G_plus _) = 0
    unfold G_plus I j
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, I, j] <;> norm_num

theorem G_minus_nilpotent (n : Fin 3) : G_minus n * G_minus n = 0 := by
  fin_cases n
  all_goals
    change mulZ (G_minus _) (G_minus _) = 0
    unfold G_minus I j
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, I, j] <;> norm_num

theorem G_plus_mul_G_minus (n : Fin 3) : G_plus n * G_minus n = D_minus n := by
  fin_cases n
  all_goals
    change mulZ (G_plus _) (G_minus _) = D_minus _
    unfold G_plus G_minus D_minus I j J oneZ
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, I, j, J, oneZ] <;> norm_num

theorem G_minus_mul_G_plus (n : Fin 3) : G_minus n * G_plus n = D_plus n := by
  fin_cases n
  all_goals
    change mulZ (G_minus _) (G_plus _) = D_plus _
    unfold G_minus G_plus D_plus I j J oneZ
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, I, j, J, oneZ] <;> norm_num

theorem D_plus_add_D_minus (n : Fin 3) :
    D_plus n + D_minus n = oneZ := by
  fin_cases n
  all_goals
    change addZ (D_plus _) (D_minus _) = oneZ
    unfold D_plus D_minus oneZ J
    apply zorn_ext <;> dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ, negZ, smulZ, addZ, zeroZ, oneZ, J] <;> norm_num

theorem G_ladder_anticommutator (n : Fin 3) :
    G_plus n * G_minus n + G_minus n * G_plus n = oneZ := by
  rw [G_plus_mul_G_minus, G_minus_mul_G_plus]
  calc
    D_minus n + D_plus n = D_plus n + D_minus n := by
      fin_cases n
      all_goals
        change addZ (D_minus _) (D_plus _) = addZ (D_plus _) (D_minus _)
        unfold D_minus D_plus oneZ J
        apply zorn_ext <;>
          dsimp only [zero_val, addZ_val, smulZ_val, ZornCell.mulZ,
            negZ, smulZ, addZ, zeroZ, oneZ, J] <;> norm_num
    _ = oneZ := D_plus_add_D_minus n

/-
### Consolidated synthesis lemma

All Gogberashvili basis identities in one statement.
-/

theorem gogberashvili_basis_synthesis :
    (∀ n : Fin 3, J n * J n = oneZ) ∧
    (∀ n : Fin 3, j n * j n = negZ oneZ) ∧
    I * I = oneZ ∧
    (∀ n m : Fin 3, n ≠ m → J n * J m = negZ (J m * J n)) ∧
    (∀ n m : Fin 3, n ≠ m → J n * J m = negZ (sumFin3 (fun k => (eps3 n m k : ℝ) • j k))) ∧
    (∀ n m : Fin 3, n ≠ m → j n * j m = negZ (sumFin3 (fun k => (eps3 n m k : ℝ) • j k))) ∧
    (∀ n m : Fin 3, n ≠ m → j m * J n = negZ (sumFin3 (fun k => (eps3 n m k : ℝ) • J k))) ∧
    (∀ n : Fin 3, J n * I = negZ (j n)) ∧
    (∀ n : Fin 3, I * J n = j n) ∧
    (∀ n : Fin 3, j n * I = negZ (J n)) ∧
    (∀ n : Fin 3, I * j n = J n) ∧
    (∀ n : Fin 3, D_plus n * D_plus n = D_plus n) ∧
    (∀ n : Fin 3, D_minus n * D_minus n = D_minus n) ∧
    (∀ n : Fin 3, D_plus n * D_minus n = 0) ∧
    (∀ n : Fin 3, G_plus n * G_plus n = 0) ∧
    (∀ n : Fin 3, G_minus n * G_minus n = 0) ∧
    (∀ n : Fin 3, G_plus n * G_minus n = D_minus n) := by
  refine ⟨J_sq, j_sq, I_sq, ?_, ?_, ?_, ?_, J_mul_I, I_mul_J, j_mul_I, I_mul_j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- J anticommutation
    intro n m h
    exact J_anticomm n m h
  · -- J_mul_J cross products
    intro n m h
    exact J_mul_J n m h
  · -- j_mul_j cross products
    intro n m h
    exact j_mul_j n m h
  · -- j_mul_J cross products
    intro n m h
    exact j_mul_J n m h
  · -- D_plus idempotent
    intro n
    exact D_plus_idempotent n
  · -- D_minus idempotent
    intro n
    exact D_minus_idempotent n
  · -- D_plus * D_minus = 0
    intro n
    exact D_plus_mul_D_minus n
  · -- G_plus nilpotent
    intro n
    exact G_plus_nilpotent n
  · -- G_minus nilpotent
    intro n
    exact G_minus_nilpotent n
  · -- G_plus * G_minus = D_minus
    intro n
    exact G_plus_mul_G_minus n

end InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
