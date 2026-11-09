/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.EndomorphismCharge

/-!
# Integer charge sectors and composition

These are actual submodules of the full noncommutative endomorphism ring.
Composition and commutator add charges. No directness of the collection of
sectors is claimed in arbitrary characteristic.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
variable {B : Type*} [Ring B]
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Charge n is the kernel of Δ - n id. -/
def chargeSector (P : B) (n : ℤ) : Submodule ℤ (Module.End ℤ B) :=
  LinearMap.ker (endomorphismCharge P - n • LinearMap.id)

theorem mem_chargeSector (P : B) (n : ℤ) (K : Module.End ℤ B) :
    K ∈ chargeSector P n ↔ endomorphismCharge P K = n • K := by
  change endomorphismCharge P K - n • K = 0 ↔ _
  exact sub_eq_zero

/-- Charge is a derivation of endomorphism composition. -/
theorem endomorphismCharge_mul (P : B) (K L : Module.End ℤ B) :
    endomorphismCharge P (K * L) =
      endomorphismCharge P K * L + K * endomorphismCharge P L := by
  change comm (LieAlgebra.ad ℤ B P) (K * L) =
    comm (LieAlgebra.ad ℤ B P) K * L + K * comm (LieAlgebra.ad ℤ B P) L
  simp only [comm, sub_mul, mul_sub, mul_assoc]
  abel

theorem mul_mem_chargeSector {P : B} {m n : ℤ} {K L : Module.End ℤ B}
    (hK : K ∈ chargeSector P m) (hL : L ∈ chargeSector P n) :
    K * L ∈ chargeSector P (m + n) := by
  rw [mem_chargeSector] at *
  rw [endomorphismCharge_mul, hK, hL, smul_mul_assoc, mul_smul_comm, add_smul]

theorem comm_mem_chargeSector {P : B} {m n : ℤ} {K L : Module.End ℤ B}
    (hK : K ∈ chargeSector P m) (hL : L ∈ chargeSector P n) :
    comm K L ∈ chargeSector P (m + n) := by
  unfold comm
  exact (chargeSector P (m + n)).sub_mem (mul_mem_chargeSector hK hL)
    (by simpa only [add_comm] using mul_mem_chargeSector hL hK)

theorem one_mem_chargeSector (P : B) :
    (1 : Module.End ℤ B) ∈ chargeSector P 0 := by
  rw [mem_chargeSector, zero_smul]
  change (LieAlgebra.ad ℤ B P) * 1 - 1 * (LieAlgebra.ad ℤ B P) = 0
  simp

/-- The zero-charge endomorphisms form a Lie subalgebra: they commute with
the adjoint charge operator, and their commutators remain in its kernel. -/
def chargeZeroLieSubalgebra (P : B) :
    LieSubalgebra ℤ (Module.End ℤ B) where
  carrier := chargeSector P 0
  zero_mem' := (chargeSector P 0).zero_mem
  add_mem' := (chargeSector P 0).add_mem
  smul_mem' := by
    intro c K hK
    exact (chargeSector P 0).smul_mem c hK
  lie_mem' := by
    intro K L hK hL
    change comm K L ∈ chargeSector P 0
    exact comm_mem_chargeSector (m := 0) (n := 0) hK hL

end InfoGeometry.OperatorAlgebra.PeirceSpine
