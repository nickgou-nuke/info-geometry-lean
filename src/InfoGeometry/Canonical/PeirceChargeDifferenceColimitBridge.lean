/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceTelegrapherVirasoroColimitBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChargeDifferenceReconstruction

/-! The integral charge-difference identities at a tensor-tower stage and
after its canonical embedding into the direct limit. -/

namespace InfoGeometry.Canonical.PeirceChargeDifferenceColimitBridge

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The first charge iteration is natural under ring homomorphisms. -/
theorem map_kantorDelta1 {B D : Type*} [Ring B] [Ring D]
    (f : B →+* D) (P A C X : B) :
    f (kantorDelta1 P A C X) = kantorDelta1 (f P) (f A) (f C) (f X) := by
  simp only [kantorDelta1, superChargeP, kantorTotal, kantorGp2, kantorGp1,
    kantorG0, kantorGm1, kantorGm2, kantorTriple, InfoGeometry.OperatorAlgebra.PeirceSpine.comm, conePlus, coneMinus,
    map_add, map_sub, map_mul, map_one]

/-- The third charge iteration is natural under ring homomorphisms. -/
theorem map_kantorDelta3 {B D : Type*} [Ring B] [Ring D]
    (f : B →+* D) (P A C X : B) :
    f (kantorDelta3 P A C X) = kantorDelta3 (f P) (f A) (f C) (f X) := by
  simp only [kantorDelta3, kantorDelta2, kantorDelta1, superChargeP, kantorTotal,
    kantorGp2, kantorGp1, kantorG0, kantorGm1, kantorGm2, kantorTriple, InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
    conePlus, coneMinus, map_add, map_sub, map_mul, map_one]

/-- Naturality of the polynomial that extracts the charge-one difference. -/
theorem map_charge_one_difference {B D : Type*} [Ring B] [Ring D]
    (f : B →+* D) (P A C X : B) :
    f ((4 : ℤ) • kantorDelta1 P A C X - kantorDelta3 P A C X) =
      (4 : ℤ) • kantorDelta1 (f P) (f A) (f C) (f X) -
        kantorDelta3 (f P) (f A) (f C) (f X) := by
  rw [map_sub, map_zsmul, map_kantorDelta1, map_kantorDelta3]

/-- Naturality of the polynomial that extracts the charge-two difference. -/
theorem map_charge_two_difference {B D : Type*} [Ring B] [Ring D]
    (f : B →+* D) (P A C X : B) :
    f (kantorDelta3 P A C X - kantorDelta1 P A C X) =
      kantorDelta3 (f P) (f A) (f C) (f X) -
        kantorDelta1 (f P) (f A) (f C) (f X) := by
  rw [map_sub, map_kantorDelta3, map_kantorDelta1]

/-- Bonding a stage and then entering the limit gives the same third charge
iteration as entering the limit directly. -/
theorem bonded_delta3_coherence {n m : ℕ} (hnm : n ≤ m) (P A C X : Stage n) :
    kantorDelta3 (ofStage m (bondMap stageBond n m hnm P))
      (ofStage m (bondMap stageBond n m hnm A))
      (ofStage m (bondMap stageBond n m hnm C))
      (ofStage m (bondMap stageBond n m hnm X)) =
    kantorDelta3 (ofStage n P) (ofStage n A) (ofStage n C) (ofStage n X) := by
  have hc (Y : Stage n) : ofStage m (bondMap stageBond n m hnm Y) = ofStage n Y := by
    exact directLimitOf_bondMap stageBond n m hnm Y
  rw [hc P, hc A, hc C, hc X]

theorem stage_and_limit_charge_differences {n : ℕ} {P : Stage n}
    (hP : P * P = P) (A C X : Stage n) :
    ((4 : ℤ) • kantorDelta1 P A C X - kantorDelta3 P A C X =
      (3 : ℤ) • (kantorGp1 P A X - kantorGm1 P C X)) ∧
    ((4 : ℤ) • kantorDelta1 (ofStage n P) (ofStage n A) (ofStage n C) (ofStage n X) -
        kantorDelta3 (ofStage n P) (ofStage n A) (ofStage n C) (ofStage n X) =
      (3 : ℤ) • (kantorGp1 (ofStage n P) (ofStage n A) (ofStage n X) -
        kantorGm1 (ofStage n P) (ofStage n C) (ofStage n X))) ∧
    (kantorDelta3 (ofStage n P) (ofStage n A) (ofStage n C) (ofStage n X) -
        kantorDelta1 (ofStage n P) (ofStage n A) (ofStage n C) (ofStage n X) =
      (6 : ℤ) • (kantorGp2 (ofStage n P) (ofStage n A) (ofStage n X) -
        kantorGm2 (ofStage n P) (ofStage n C) (ofStage n X))) := by
  have hlim : ofStage n P * ofStage n P = ofStage n P := by
    rw [← map_mul, hP]
  exact ⟨(kantor_odd_charge_differences hP A C X).1,
    kantor_odd_charge_differences hlim (ofStage n A) (ofStage n C) (ofStage n X)⟩

end InfoGeometry.Canonical.PeirceChargeDifferenceColimitBridge
