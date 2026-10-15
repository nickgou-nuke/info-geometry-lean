/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Tactic.Abel
import InfoGeometry.Physics.ChevalleySpinorIdeal
import InfoGeometry.Physics.ChevalleyDyads

/-!
# CAR Grading Involution and Its Induced Endomorphism Conjugation

This module proves algebraic consequences of a CAR pair `(n, p)` in a
preadditive category.

From the CAR axioms `n² = 0`, `p² = 0`, `np + pn = 𝟙` the split involution

$$\varepsilon = [n, p] = np - pn = 2np - \mathbb{1}$$

is an endomorphism satisfying `η ≫ η = 𝟙`. The definition
`A ↦ η ≫ A ≫ η` is an involutive algebraic conjugation. A preadditive
category has no specified star operation, inner product, or positivity notion,
so these results alone do not assert self-adjointness or a Krein-space metric.

## Causal Poset of Archetypes

```
[ℬ₀: CAR nilpotents]  n² = 0, p² = 0, np + pn = 𝟙
    ↓
[ℬ₁: split involution]  ε = [n, p] = 2np - 𝟙,  ε² = 𝟙
    ↓
[η: grading involution]  η ≫ η = 𝟙
    ↓
[A^‡: Dirac conjugation]  A ↦ ηAη,  involutive
    ↓
[off-diagonal flip]  (E₀₁)^‡ = -E₀₁,  (E₁₀)^‡ = -E₁₀,  E₀₀^‡ = E₀₀
```

All results are genuine definitions, lemmas, and theorems with complete proofs.
-/

namespace InfoGeometry.Physics.ChevalleyKreinDirac

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Physics.Chevalley
open InfoGeometry.Physics.ChevalleyDyads

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. Basic CAR Consequences -/

/-- `pn = 𝟙 - np`. -/
theorem excited_eq_one_minus_vacuum {X : C} (n p : X ⟶ X)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    p ≫ n = 𝟙 X - n ≫ p := by
  rw [← hcar]
  abel

/-- `(n ≫ p) ≫ n = n` — the vacuum idempotent absorbs the nilpotent. -/
theorem vacuum_absorb_n {X : C} (n p : X ⟶ X) (hn : n ≫ n = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    (n ≫ p) ≫ n = n :=
  e0_comp_n n p hn hcar

/-- `p ≫ (n ≫ p) = p` — the excited idempotent absorbs the nilpotent. -/
theorem excited_absorb_p {X : C} (n p : X ⟶ X) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    p ≫ (n ≫ p) = p :=
  p_comp_e0 n p hp hcar

/-- `(p ≫ n) ≫ (p ≫ n) = p ≫ n` — the excited idempotent is idempotent. -/
theorem excited_sq_idem {X : C} (n p : X ⟶ X) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    (p ≫ n) ≫ (p ≫ n) = p ≫ n :=
  cat_P_minus_sq n p hp hcar

/-- `(n ≫ p) ≫ (n ≫ p) = n ≫ p` — the vacuum idempotent is idempotent. -/
theorem vacuum_sq_idem {X : C} (n p : X ⟶ X) (hn : n ≫ n = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    (n ≫ p) ≫ (n ≫ p) = n ≫ p :=
  cat_P_plus_sq n p hn hcar

/-! ### 2. The Krein Metric -/

/-- The CAR grading involution `η = ε = [n, p]`. With extra star and
positivity data it may serve as a fundamental symmetry; those data are not
part of the present categorical assumptions. -/
@[inline]
def kreinMetric {X : C} (n p : X ⟶ X) : X ⟶ X :=
  n ≫ p - p ≫ n

/-- The Krein metric is the split involution `2P - 𝟙` with `P = np`. -/
theorem kreinMetric_eq_two_P_minus_one {X : C} (n p : X ⟶ X)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    kreinMetric n p = (2 : ℤ) • (n ≫ p) - 𝟙 X := by
  dsimp [kreinMetric]
  rw [excited_eq_one_minus_vacuum n p hcar, two_zsmul]
  abel

/-- `η ≫ n = n`. -/
theorem kreinMetric_comp_n {X : C} (n p : X ⟶ X) (hn : n ≫ n = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    kreinMetric n p ≫ n = n := by
  dsimp [kreinMetric]
  rw [Preadditive.sub_comp]
  have h1 : (n ≫ p) ≫ n = n := e0_comp_n n p hn hcar
  have h2 : (p ≫ n) ≫ n = 0 := by
    rw [Category.assoc, hn, comp_zero]
  rw [h1, h2, sub_zero]

/-- `η ≫ p = -p`. -/
theorem kreinMetric_comp_p {X : C} (n p : X ⟶ X) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    kreinMetric n p ≫ p = -p := by
  dsimp [kreinMetric]
  rw [Preadditive.sub_comp]
  have h1 : (n ≫ p) ≫ p = 0 := vacuum_annihilates_p n p hp
  have h2 : (p ≫ n) ≫ p = p := by
    rw [Category.assoc]
    exact p_comp_e0 n p hp hcar
  rw [h1, h2, zero_sub]

/-- `n ≫ η = -n`. -/
theorem n_comp_kreinMetric {X : C} (n p : X ⟶ X) (hn : n ≫ n = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    n ≫ kreinMetric n p = -n := by
  dsimp [kreinMetric]
  rw [Preadditive.comp_sub]
  have h1 : n ≫ (n ≫ p) = 0 := by
    rw [← Category.assoc, hn, zero_comp]
  have h2 : n ≫ (p ≫ n) = n := by
    rw [← Category.assoc]
    exact e0_comp_n n p hn hcar
  rw [h1, h2, zero_sub]

/-- `p ≫ η = p`. -/
theorem p_comp_kreinMetric {X : C} (n p : X ⟶ X) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    p ≫ kreinMetric n p = p := by
  dsimp [kreinMetric]
  rw [Preadditive.comp_sub]
  have h1 : p ≫ (n ≫ p) = p := p_comp_e0 n p hp hcar
  have h2 : p ≫ (p ≫ n) = 0 := by
    rw [← Category.assoc, hp, zero_comp]
  rw [h1, h2, sub_zero]

/-- `η ≫ (n ≫ p) = n ≫ p` — the Krein metric fixes the vacuum idempotent on the left. -/
theorem kreinMetric_comp_vacuum {X : C} (n p : X ⟶ X) (hn : n ≫ n = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    kreinMetric n p ≫ (n ≫ p) = n ≫ p := by
  rw [← Category.assoc, kreinMetric_comp_n n p hn hcar]

/-- The CAR grading involution squares to the identity. This is an algebraic
involution statement, not a self-adjointness assertion. -/
theorem kreinMetric_sq {X : C} (n p : X ⟶ X) (hn : n ≫ n = 0) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    kreinMetric n p ≫ kreinMetric n p = 𝟙 X := by
  dsimp [kreinMetric]
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_sub]
  have h1 : (n ≫ p) ≫ (n ≫ p) = n ≫ p := cat_P_plus_sq n p hn hcar
  have h2 : (n ≫ p) ≫ (p ≫ n) = 0 := by
    rw [Category.assoc, ← Category.assoc p p n, hp, zero_comp, comp_zero]
  have h3 : (p ≫ n) ≫ (n ≫ p) = 0 := by
    rw [Category.assoc, ← Category.assoc n n p, hn, zero_comp, comp_zero]
  have h4 : (p ≫ n) ≫ (p ≫ n) = p ≫ n := cat_P_minus_sq n p hp hcar
  rw [h1, h2, h3, h4, sub_zero, zero_sub, sub_neg_eq_add]
  exact hcar

/-! ### 3. Dirac Conjugation -/

/-- The inner conjugation `A ↦ η ≫ A ≫ η` induced by the CAR grading
involution. It is not defined using an adjoint operation. -/
@[inline]
def diracConj {X : C} (n p : X ⟶ X) (A : X ⟶ X) : X ⟶ X :=
  kreinMetric n p ≫ A ≫ kreinMetric n p

/-- **Dirac conjugation is involutive**: `(A^‡)^‡ = A`. -/
theorem diracConj_involutive {X : C} (n p : X ⟶ X) (hn : n ≫ n = 0)
    (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) (A : X ⟶ X) :
    diracConj n p (diracConj n p A) = A := by
  dsimp [diracConj]
  have hη := kreinMetric_sq n p hn hp hcar
  simp only [Category.assoc]
  rw [← Category.assoc (kreinMetric n p) (kreinMetric n p), hη, Category.id_comp]
  rw [Category.comp_id]

/-- **Off-diagonal flip I**: `n^‡ = -n`. -/
theorem diracConj_negates_n {X : C} (n p : X ⟶ X) (hn : n ≫ n = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    diracConj n p n = -n := by
  dsimp [diracConj]
  rw [n_comp_kreinMetric n p hn hcar, Preadditive.comp_neg,
      kreinMetric_comp_n n p hn hcar]

/-- **Off-diagonal flip II**: `p^‡ = -p`. -/
theorem diracConj_negates_p {X : C} (n p : X ⟶ X) (hp : p ≫ p = 0)
    (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    diracConj n p p = -p := by
  dsimp [diracConj]
  rw [p_comp_kreinMetric n p hp hcar,
      kreinMetric_comp_p n p hp hcar]

/-- **Off-diagonal flip III**: the Dirac conjugation negates the transition
dyads `E₀₁ = |0⟩⟨1| = n` and `E₁₀ = |1⟩⟨0| = p`. -/
theorem diracConj_flips_transition_dyads {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    diracConj n p (E01 n p) = -E01 n p ∧ diracConj n p (E10 n p) = -E10 n p := by
  rw [E01_eq_n n p hn hcar, E10_eq_p n p hp hcar]
  exact ⟨diracConj_negates_n n p hn hcar, diracConj_negates_p n p hp hcar⟩

/-- The Dirac conjugation preserves the vacuum idempotent: `E₀₀^‡ = E₀₀`. -/
theorem diracConj_preserves_vacuum {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    diracConj n p (E00 n p) = E00 n p := by
  dsimp [diracConj]
  rw [E00_eq_np n p hn hcar]
  rw [Category.assoc n p (kreinMetric n p), p_comp_kreinMetric n p hp hcar,
      kreinMetric_comp_vacuum n p hn hcar]

/-- Master theorem: the Krein metric is an involution, the Dirac conjugation
is involutive, and it flips exactly the off-diagonal transition dyads while
preserving the vacuum idempotent. -/
theorem master_krein_dirac_soundness {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    (kreinMetric n p ≫ kreinMetric n p = 𝟙 X) ∧
    (∀ A : X ⟶ X, diracConj n p (diracConj n p A) = A) ∧
    (diracConj n p (E01 n p) = -E01 n p ∧ diracConj n p (E10 n p) = -E10 n p) ∧
    (diracConj n p (E00 n p) = E00 n p) := by
  refine ⟨kreinMetric_sq n p hn hp hcar,
          fun A => diracConj_involutive n p hn hp hcar A,
          diracConj_flips_transition_dyads n p hn hp hcar,
          diracConj_preserves_vacuum n p hn hp hcar⟩

end InfoGeometry.Physics.ChevalleyKreinDirac
