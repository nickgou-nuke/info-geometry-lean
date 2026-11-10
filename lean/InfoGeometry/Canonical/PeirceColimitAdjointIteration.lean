/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Peirce adjoint recurrence on the unbounded Clifford operator colimit

The existing recursive-commutator owner supplies the ordered iterates and
their compatibility with every finite tensor-head bond and canonical map into
the algebraic direct limit. This bridge adds the Peirce-specific consequence:
the cubic adjoint identity implies a recurrence at every positive finite
commutator grade. The stage index is a head cutoff; the theorem's carrier is
the direct-limit operator ring itself.

## BUCKET 1: Proved
The positive-grade recurrence follows from the existing cubic Peirce identity.

## BUCKET 2: Conditional
The recurrence assumes that `P` is idempotent.

## BUCKET 3: Open boundary
No analytic infinite commutator series or topological completion is asserted.
-/

namespace InfoGeometry.Canonical.PeirceColimitAdjointIteration

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- The inner commutator is additive in its input and preserves integer
scalar multiples. -/
private theorem commutator_zsmul (H X : Limit) (c : ℤ) :
    InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator H (c • X) =
      c • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator H X := by
  have hAdd : ∀ Y Z : Limit,
      InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator H (Y + Z) =
        InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator H Y +
          InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator H Z := by
    intro Y Z
    simp only [InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator,
      mul_add, add_mul]
    abel
  let f : Limit →+ Limit := AddMonoidHom.mk'
    (fun Y => InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator H Y) hAdd
  exact f.map_zsmul c X

/-- The Peirce involution's cubic inner-commutator identity propagates to every
positive grade of the recursive commutator sequence in the algebraic direct
limit of the Clifford tensor tower. -/
theorem limit_invS_iteratedCommutator_recurrence
    (P X : Limit) (hP : P * P = P) (n : ℕ) (hn : 1 ≤ n) :
    InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
        (invS P) (n + 2) X =
      (4 : ℤ) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
        (invS P) n X := by
  have hbase := invS_commutator_cubic_and_scaled_peirce_channels
    (P := P) hP X
  have h₁ : InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
        (invS P) (1 + 2) X =
      (4 : ℤ) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
        (invS P) 1 X := by
    change InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P)
          (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) X)) =
      (4 : ℤ) • InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) X
    exact hbase.1
  refine Nat.le_induction (m := 1) h₁ ?_ n hn
  intro k hk ih
  calc
    InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
        (invS P) ((k + 1) + 2) X =
        InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator (invS P)
          (InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
            (invS P) (k + 2) X) := by simp [InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator]
    _ = InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator (invS P)
        ((4 : ℤ) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
          (invS P) k X) := by rw [ih]
    _ = (4 : ℤ) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
        (invS P) (k + 1) X := by
          calc
            InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator (invS P)
                ((4 : ℤ) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
                  (invS P) k X) =
                (4 : ℤ) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.commutator (invS P)
                  (InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
                    (invS P) k X) := commutator_zsmul (invS P) _ 4
            _ = (4 : ℤ) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
                (invS P) (k + 1) X := by
                  rfl

/-- Repeated application of the two-grade recurrence gives a geometric
progression separately on the odd and even commutator grades. The powers are
integer scalar multiples in the same algebraic direct-limit operator ring. -/
theorem limit_invS_iteratedCommutator_parity_closed_forms
    (P X : Limit) (hP : P * P = P) (k : ℕ) :
    InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
        (invS P) (2 * k + 1) X =
      ((4 : ℤ) ^ k) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
        (invS P) 1 X ∧
    InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
        (invS P) (2 * k + 2) X =
      ((4 : ℤ) ^ k) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
        (invS P) 2 X := by
  have hscale (Y : Limit) (m : ℕ) :
      (4 : ℤ) • ((4 : ℤ) ^ m • Y) = (4 : ℤ) ^ (m + 1) • Y := by
    calc
      (4 : ℤ) • ((4 : ℤ) ^ m • Y) = (4 * (4 : ℤ) ^ m) • Y := smul_smul _ _ _
      _ = ((4 : ℤ) ^ m * 4) • Y := by rw [mul_comm]
      _ = (4 : ℤ) ^ (m + 1) • Y := by rw [pow_succ]
  constructor
  · induction k with
    | zero => simp [InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator]
    | succ k ih =>
        have hrec := limit_invS_iteratedCommutator_recurrence P X hP (2 * k + 1) (by omega)
        calc
          InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
              (invS P) (2 * (k + 1) + 1) X =
            InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
              (invS P) ((2 * k + 1) + 2) X := rfl
          _ = (4 : ℤ) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
                (invS P) (2 * k + 1) X := hrec
          _ = (4 : ℤ) • ((4 : ℤ) ^ k •
                InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
                  (invS P) 1 X) := by rw [ih]
          _ = (4 : ℤ) ^ (k + 1) •
                InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
                  (invS P) 1 X := hscale _ _
  · induction k with
    | zero => simp [InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator]
    | succ k ih =>
        have hrec := limit_invS_iteratedCommutator_recurrence P X hP (2 * k + 2) (by omega)
        calc
          InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
              (invS P) (2 * (k + 1) + 2) X =
            InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
              (invS P) ((2 * k + 2) + 2) X := rfl
          _ = (4 : ℤ) • InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
                (invS P) (2 * k + 2) X := hrec
          _ = (4 : ℤ) • ((4 : ℤ) ^ k •
                InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
                  (invS P) 2 X) := by rw [ih]
          _ = (4 : ℤ) ^ (k + 1) •
                InfoGeometry.Clifford.Cl11RecursiveCommutatorColimit.iteratedCommutator
                  (invS P) 2 X := hscale _ _

end InfoGeometry.Canonical.PeirceColimitAdjointIteration
