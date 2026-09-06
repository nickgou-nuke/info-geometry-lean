import Mathlib.Tactic
import InfoGeometry.Canonical.CuntzMapKreinBridge

/-!
# Cuntz Map — Discrete Modular Step and Fixed Readouts

`Φ(X) = S_L * X * S_L^* + S_R * X * S_R^*`.

This file proves the finite algebraic fixed-readout consequences of the
symmetric branch law. It does not prove uniqueness of a KMS state, norm
contraction, Ruelle--Perron--Frobenius classification, or equality with a
continuous modular flow.

#### BUCKET 1: CLOSED FINITE THEOREMS
Unitality, one-step fixed readout, iterated fixed readout, and finite orbit-sum
readout under explicit half-branch hypotheses.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT MAP EQUALITY
The modular-step readout is used only through an explicit pointwise equality.

#### BUCKET 3: OPEN CLOSURE DEBT
Uniqueness, contraction, complete positivity, and continuous modular-flow
classification.
-/

set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.CuntzMapFixedPoint

open InfoGeometry.Canonical.CuntzMapKreinBridge

variable {Op : Type*} [Ring Op] [StarRing Op]

/-! ### 1. The Cuntz Map Φ -/

def cuntzMap (S_left S_right : Op) (X : Op) : Op :=
  CuntzMapKreinBridge.cuntzMapTwo S_left S_right X

theorem cuntzMap_add
    (S_left S_right X Y : Op) :
    cuntzMap S_left S_right (X + Y) =
      cuntzMap S_left S_right X + cuntzMap S_left S_right Y := by
  exact CuntzMapKreinBridge.cuntzMapTwo_additive S_left S_right X Y

theorem cuntzMap_zero (S_left S_right : Op) :
    cuntzMap S_left S_right 0 = 0 := by
  exact CuntzMapKreinBridge.cuntzMapTwo_zero S_left S_right

theorem cuntzMap_iterate_add
    (S_left S_right X Y : Op) (n : ℕ) :
    Nat.iterate (cuntzMap S_left S_right) n (X + Y) =
      Nat.iterate (cuntzMap S_left S_right) n X +
        Nat.iterate (cuntzMap S_left S_right) n Y := by
  revert X Y
  induction n with
  | zero => intro X Y; rfl
  | succ n ih =>
      intro X Y
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      rw [cuntzMap_add]
      rw [ih]

theorem cuntzMap_unital (S_left S_right : Op) (h_range : S_left * star S_left + S_right * star S_right = 1) :
    cuntzMap S_left S_right 1 = 1 := by
  exact CuntzMapKreinBridge.cuntzMapTwo_one_of_partition
    (S_left := S_left) (S_right := S_right) h_range

theorem cuntzMap_iterate_mul_of_cuntz_relations
    (S_left S_right X Y : Op)
    (hLL : star S_left * S_left = 1)
    (hRR : star S_right * S_right = 1)
    (hLR : star S_left * S_right = 0)
    (hRL : star S_right * S_left = 0)
    (n : ℕ) :
    Nat.iterate (cuntzMap S_left S_right) n (X * Y) =
      Nat.iterate (cuntzMap S_left S_right) n X *
        Nat.iterate (cuntzMap S_left S_right) n Y := by
  revert X Y
  induction n with
  | zero => intro X Y; rfl
  | succ n ih =>
      intro X Y
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      have hmul :
          cuntzMap S_left S_right (X * Y) =
            cuntzMap S_left S_right X * cuntzMap S_left S_right Y := by
        have hLL' :
            S_left * X * star S_left * S_left * Y * star S_left =
              S_left * X * Y * star S_left := by
          rw [mul_assoc (S_left * X) (star S_left) S_left, hLL]
          simp [mul_assoc]
        have hLR' :
            S_left * X * star S_left * S_right * Y * star S_right = 0 := by
          rw [mul_assoc (S_left * X) (star S_left) S_right, hLR]
          simp
        have hRL' :
            S_right * X * star S_right * S_left * Y * star S_left = 0 := by
          rw [mul_assoc (S_right * X) (star S_right) S_left, hRL]
          simp
        have hRR' :
            S_right * X * star S_right * S_right * Y * star S_right =
              S_right * X * Y * star S_right := by
          rw [mul_assoc (S_right * X) (star S_right) S_right, hRR]
          simp [mul_assoc]
        simp only [cuntzMap, CuntzMapKreinBridge.cuntzMapTwo,
          add_mul, mul_add]
        simp only [← mul_assoc]
        rw [hLL', hRL', hLR', hRR']
        simp
      rw [hmul]
      rw [ih]

theorem cuntzMap_iterate_star
    (S_left S_right X : Op) (n : ℕ) :
    Nat.iterate (cuntzMap S_left S_right) n (star X) =
      star (Nat.iterate (cuntzMap S_left S_right) n X) := by
  have hstar : ∀ Y : Op,
      cuntzMap S_left S_right (star Y) =
        star (cuntzMap S_left S_right Y) := by
    intro Y
    simp [cuntzMap, CuntzMapKreinBridge.cuntzMapTwo,
      star_add, star_mul, mul_assoc]
  revert X
  induction n with
  | zero => intro X; rfl
  | succ n ih =>
      intro X
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        hstar, ih]

theorem cuntzMap_iterate_zero
    (S_left S_right : Op) (n : ℕ) :
    Nat.iterate (cuntzMap S_left S_right) n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, cuntzMap_zero S_left S_right, ih]

theorem cuntzMap_iterate_one_of_partition
    (S_left S_right : Op)
    (h_range : S_left * star S_left + S_right * star S_right = 1)
    (n : ℕ) :
    Nat.iterate (cuntzMap S_left S_right) n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,
        cuntzMap_unital S_left S_right h_range, ih]

/-! ### 2. Symmetric additive readout -/

namespace KMSSymmetricState

variable {S_left S_right : Op}

/-- `φ (Φ X) = φ X` under the explicit symmetric branch-scaling laws. -/
theorem cuntzMap_fixed_point
    (φ : Op →+ ℝ)
    (half_L : ∀ X, φ (S_left * X * star S_left) = (1 / 2 : ℝ) * φ X)
    (half_R : ∀ X, φ (S_right * X * star S_right) = (1 / 2 : ℝ) * φ X)
    (X : Op) :
    φ (cuntzMap S_left S_right X) = φ X := by
  simpa [cuntzMap] using
    CuntzMapKreinBridge.real_additive_readout_fixed_of_half_branch_scaling
      (φ := φ) (S_left := S_left) (S_right := S_right) (X := X)
      (half_L X) (half_R X)

/-- Every finite iterate of the transfer map preserves the readout. -/
theorem cuntzMap_iterate_fixed_point
    (φ : Op →+ ℝ)
    (half_L : ∀ X, φ (S_left * X * star S_left) = (1 / 2 : ℝ) * φ X)
    (half_R : ∀ X, φ (S_right * X * star S_right) = (1 / 2 : ℝ) * φ X)
    (X : Op) (n : ℕ) :
    φ (Nat.iterate (cuntzMap S_left S_right) n X) = φ X := by
  revert X
  induction' n with k ih
  · intro X
    rfl
  · intro X
    rw [Function.iterate_succ_apply]
    rw [ih (cuntzMap S_left S_right X)]
    exact cuntzMap_fixed_point φ half_L half_R X

/-- `φ(Σ_{k=0}^{N-1} Φ^k(X)) = N * φ(X)`: finite orbit-sum readout. -/
theorem cuntzMap_sum_iterate_fixed_point
    (φ : Op →+ ℝ)
    (half_L : ∀ X, φ (S_left * X * star S_left) = (1 / 2 : ℝ) * φ X)
    (half_R : ∀ X, φ (S_right * X * star S_right) = (1 / 2 : ℝ) * φ X)
    (X : Op) (N : ℕ) :
    φ (Finset.sum (Finset.range N)
      (fun k => Nat.iterate (cuntzMap S_left S_right) k X)) =
    (N : ℝ) * φ X := by
  induction' N with n ih
  · have hφ0 : φ 0 = 0 := by
      exact φ.map_zero
    simp [hφ0]
  · rw [Finset.sum_range_succ,
      φ.map_add (Finset.sum (Finset.range n) _)
        (Nat.iterate (cuntzMap S_left S_right) n X),
      ih,
      cuntzMap_iterate_fixed_point φ half_L half_R X n]
    push_cast; ring

end KMSSymmetricState

end InfoGeometry.Canonical.CuntzMapFixedPoint
