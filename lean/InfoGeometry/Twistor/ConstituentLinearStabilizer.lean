/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwistorInternalSymmetry

/-! # Real-linear internal transformations on the existing packet carrier

Contract: the existing skew shift and unitary mix are real-linear bijections.
Their kinematic invariance places them in the real-linear stabilizer. Forgetting
linearity gives exactly membership in the existing permutation stabilizer.
No classification of the stabilizer is asserted.
-/
noncomputable section
namespace InfoGeometry.Twistor.ConstituentLinearStabilizer
open PenroseIncidence TwistorKinematicTensor TwistorConstituentKinematics
open TwistorInternalSymmetry
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The antilinear infinity operation is linear over the real scalars. -/
theorem infinityConjugate_real_smul (r : ℝ) (Z : Twistor4) :
    infinityConjugate (r • Z) = r • infinityConjugate Z := by
  change infinityConjugate ((r : ℂ) • Z) = (r : ℂ) • infinityConjugate Z
  rw [infinityConjugate_smul]
  simp

/-- The existing shift, with its real-linear structure exposed. -/
def shiftLinearEquiv (L : Matrix ι ι ℂ) : Packet ι ≃ₗ[ℝ] Packet ι where
  toEquiv := shiftEquiv L
  map_add' Z W := by
    funext i
    simp [shiftEquiv, shift, infinityConjugate_add, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' r Z := by
    change shift L (r • Z) = r • shift L Z
    funext i
    simp only [shift, Pi.smul_apply, infinityConjugate_real_smul, smul_add,
      Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _

/-- The existing unitary mixing, with its real-linear structure exposed. -/
def mixLinearEquiv (U : Matrix ι ι ℂ) (hl : Uᴴ * U = 1) (hr : U * Uᴴ = 1) :
    Packet ι ≃ₗ[ℝ] Packet ι where
  toEquiv := mixEquiv U hl hr
  map_add' Z W := by
    funext i
    simp [mixEquiv, mix, smul_add, Finset.sum_add_distrib]
  map_smul' r Z := by
    change mix U (r • Z) = r • mix U Z
    funext i
    simp only [mix, Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _

/-- Stabilizer restricted to real-linear automorphisms of actual constituents. -/
def kinematicLinearStabilizer : Subgroup (Packet ι ≃ₗ[ℝ] Packet ι) where
  carrier := {e | ∀ Z, totalKinematic (e Z) = totalKinematic Z}
  one_mem' Z := rfl
  mul_mem' {e f} he hf Z := (he (f Z)).trans (hf Z)
  inv_mem' {e} he Z := by
    have h := he (e.symm Z)
    simpa using h.symm

/-- Forgetting linearity relates the two stabilizers on the same carrier. -/
theorem mem_linearStabilizer_iff (e : Packet ι ≃ₗ[ℝ] Packet ι) :
    e ∈ kinematicLinearStabilizer ↔ e.toEquiv ∈ kinematicStabilizer := Iff.rfl

theorem shift_mem_linearStabilizer (L : Matrix ι ι ℂ) (hL : Lᵀ = -L) :
    shiftLinearEquiv L ∈ kinematicLinearStabilizer :=
  totalKinematic_shift L hL

theorem mix_mem_linearStabilizer (U : Matrix ι ι ℂ)
    (hl : Uᴴ * U = 1) (hr : U * Uᴴ = 1) :
    mixLinearEquiv U hl hr ∈ kinematicLinearStabilizer :=
  totalKinematic_mix U hl

end InfoGeometry.Twistor.ConstituentLinearStabilizer
