/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# All-order adjoint grades in the Peirce operator colimit

The finite matrix heads of the `Cl(1,1)` tensor tower are stage carriers; the
operator carrier below is their algebraic direct limit `Limit`.  This file
proves that iterated inner commutators are compatible with every ring map in
the tower and that the grading adjoint action on `Limit` obeys its recurrence
at every positive order.  No fixed matrix dimension is imposed on `Limit`.
-/

namespace InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-- The `k`th iterated inner commutator by `H`, with order preserved. -/
def commutatorIterate {B : Type*} [Ring B] (H X : B) : ℕ → B
  | 0 => X
  | k + 1 => comm H (commutatorIterate H X k)

/-- Ring homomorphisms preserve every iterated inner commutator, by induction
on its grade. -/
theorem commutatorIterate_map
    {B D : Type*} [Ring B] [Ring D] (f : B →+* D) (H X : B) (k : ℕ) :
    f (commutatorIterate H X k) =
      commutatorIterate (f H) (f X) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [commutatorIterate, comm, map_sub, map_mul, ih]

/-- The one-step Clifford tensor-head embedding preserves all iterated
commutator grades on operators in that head. -/
theorem stageEmbed_commutatorIterate (n k : ℕ) (H X : Stage n) :
    InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n
        (commutatorIterate H X k) =
      commutatorIterate
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n H)
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n X) k := by
  exact commutatorIterate_map
    (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n).toRingHom H X k

/-- Every canonical head-to-limit map preserves all iterated commutator
grades.  The result is stated in the direct-limit operator ring. -/
theorem ofStage_commutatorIterate (n k : ℕ) (H X : Stage n) :
    ofStage n (commutatorIterate H X k) =
      commutatorIterate (ofStage n H) (ofStage n X) k := by
  exact commutatorIterate_map (ofStage n) H X k

/-- Any iterated stage-bonding map preserves the entire commutator-grade
sequence, not just its first or second term. -/
theorem bondMap_commutatorIterate {n m k : ℕ} (hnm : n ≤ m)
    (H X : Stage n) :
    bondMap stageBond n m hnm (commutatorIterate H X k) =
      commutatorIterate (bondMap stageBond n m hnm H)
        (bondMap stageBond n m hnm X) k := by
  exact commutatorIterate_map (bondMap stageBond n m hnm) H X k

private theorem comm_zsmul {B : Type*} [Ring B] (H X : B) (c : ℤ) :
    comm H (c • X) = c • comm H X := by
  let ad : B →+ B :=
    { toFun := fun Y => comm H Y
      map_zero' := by simp [comm]
      map_add' := by
        intro Y Z
        simp only [comm, mul_add, add_mul]
        abel }
  exact map_zsmul ad X c

/-- On the direct-limit operator ring, the Peirce grading adjoint action has
period-two recurrence at every positive commutator grade:
`ad_S^(n+2)(X) = 4 • ad_S^n(X)`.  The cubic identity is the base case; the
proof inducts over all higher grades. -/
theorem limit_invS_commutatorIterate_recurrence
    (P X : Limit) (hP : P * P = P) (n : ℕ) (hn : 1 ≤ n) :
    commutatorIterate (invS P) X (n + 2) =
      (4 : ℤ) • commutatorIterate (invS P) X n := by
  have hbase := invS_commutator_cubic_and_scaled_peirce_channels
    (P := P) hP X
  have h₁ : commutatorIterate (invS P) X (1 + 2) =
      (4 : ℤ) • commutatorIterate (invS P) X 1 := by
    simpa [commutatorIterate] using hbase.1
  refine Nat.le_induction h₁ ?_ n hn
  intro k hk ih
  calc
    commutatorIterate (invS P) X ((k + 1) + 2) =
        comm (invS P) (commutatorIterate (invS P) X (k + 2)) := by
          simp [commutatorIterate, Nat.add_assoc]
    _ = comm (invS P)
        ((4 : ℤ) • commutatorIterate (invS P) X k) := by rw [ih]
    _ = (4 : ℤ) • commutatorIterate (invS P) X (k + 1) := by
          rw [comm_zsmul]

end InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
