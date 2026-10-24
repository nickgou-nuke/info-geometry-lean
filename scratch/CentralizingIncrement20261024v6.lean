/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Physics.KleinBottleSewingExact
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-!
# Centralizing increments for commutator transport

Uncompiled sandbox. The generic criterion uses arbitrary rings. The concrete
complex-matrix obstruction concerns the native A ↦ A ⊗ I embedding only.
-/
noncomputable section

namespace InfoGeometry.Algebra.CentralizingIncrement

/-- Strict commutator transport at one element is exactly centralization by
its Hamiltonian increment. No characteristic assumption is needed. -/
theorem commutator_map_eq_iff {A B : Type*} [Ring A] [Ring B]
    (e : A →+* B) (H : A) (K : B) (a : A) :
    K * e a - e a * K = e (H * a - a * H) ↔
      Commute (K - e H) (e a) := by
  have hd : (K - e H) * e a - e a * (K - e H) =
      (K * e a - e a * K) - e (H * a - a * H) := by
    simp only [map_sub, map_mul]
    noncomm_ring
  constructor
  · intro h
    change (K - e H) * e a = e a * (K - e H)
    apply sub_eq_zero.mp
    rw [hd, h, sub_self]
  · intro h
    apply sub_eq_zero.mp
    rw [← hd]
    exact sub_eq_zero.mpr h.eq

/-- Compatibility on the entire old algebra is equivalent to its increment
belonging to the relative commutant, expressed without a new carrier. -/
theorem commutator_compatible_iff {A B : Type*} [Ring A] [Ring B]
    (e : A →+* B) (H : A) (K : B) :
    (∀ a, K * e a - e a * K = e (H * a - a * H)) ↔
      ∀ a, Commute (K - e H) (e a) := by
  exact forall_congr' (fun a => commutator_map_eq_iff e H K a)

end InfoGeometry.Algebra.CentralizingIncrement

namespace InfoGeometry.Canonical.CuntzBoundaryCouplingObstruction

open CuntzMatrixTowerInstantiation CuntzMatrixTraceTower
open InfoGeometry.Physics.KleinBottleSewingExact
open InfoGeometry.Algebra.CentralizingIncrement
open scoped Kronecker

/-- The raw two-site ZZ matrix used by the native boundary reindexing. -/
def tensorZZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  tilt2 ⊗ₖ tilt2

/-- The same old-site switch tensor identity used in concreteStep 1. -/
def tensorOldSwitch : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  switch2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- The actual raw tensor commutator survives every nonzero scalar coefficient. -/
theorem tensorZZ_scaled_noncommute (lam : ℂ) (hlam : lam ≠ 0) :
    (lam • tensorZZ) * tensorOldSwitch ≠ tensorOldSwitch * (lam • tensorZZ) := by
  intro ht
  unfold tensorZZ tensorOldSwitch at ht
  rw [smul_mul_assoc, mul_smul_comm,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    mul_one, one_mul] at ht
  have hv := congrArg
    (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M (0, 0) (1, 0)) ht
  have hv' : lam = -lam := by
    simpa [Matrix.kronecker_apply, tilt2, switch2,
      Matrix.mul_apply, Fin.sum_univ_two] using hv
  apply hlam
  linear_combination (1 / 2 : ℂ) * hv'

/-- Ordered-product inequality on the exact tensor carrier of the obstruction. -/
theorem tensorZZ_noncommute :
    tensorZZ * tensorOldSwitch ≠ tensorOldSwitch * tensorZZ := by
  simpa only [one_smul] using tensorZZ_scaled_noncommute (1 : ℂ) one_ne_zero

/-- Actual two-site ZZ coupling, using the same reindexing as concreteStep. -/
def boundaryZZ : MatrixStage 2 :=
  (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv 1)) tensorZZ

/-- A nonzero ZZ boundary coupling does not commute with an old-site switch. -/
theorem boundaryZZ_not_commute_old_switch (lam : ℂ) (hlam : lam ≠ 0) :
    ¬ Commute (lam • boundaryZZ) (concreteStep 1 switch2) := by
  intro hc
  let e := Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv 1)
  change (lam • e tensorZZ) * e tensorOldSwitch =
    e tensorOldSwitch * (lam • e tensorZZ) at hc
  have he : e (lam • tensorZZ) * e tensorOldSwitch =
      e tensorOldSwitch * e (lam • tensorZZ) := by
    simpa only [map_smul] using hc
  apply tensorZZ_scaled_noncommute lam hlam
  exact e.injective (by simpa only [map_mul] using he)

/-- Explicit ordered-product witness for the actual two-site boundary coupling. -/
theorem boundaryZZ_old_switch_noncommute :
    boundaryZZ * concreteStep 1 switch2 ≠ concreteStep 1 switch2 * boundaryZZ := by
  intro h
  apply boundaryZZ_not_commute_old_switch (1 : ℂ) one_ne_zero
  change (1 : ℂ) • boundaryZZ * concreteStep 1 switch2 =
    concreteStep 1 switch2 * ((1 : ℂ) • boundaryZZ)
  simpa only [one_smul] using h

/-- No old Hamiltonian cancels this increment's compatibility defect. -/
theorem boundaryZZ_not_commutator_compatible (H : MatrixStage 1)
    (lam : ℂ) (hlam : lam ≠ 0) :
    ¬ ∀ A : MatrixStage 1,
      (concreteStep 1 H + lam • boundaryZZ) * concreteStep 1 A -
        concreteStep 1 A * (concreteStep 1 H + lam • boundaryZZ) =
      concreteStep 1 (H * A - A * H) := by
  intro h
  have hc := (commutator_compatible_iff (concreteStep 1).toAlgHom.toRingHom H
    (concreteStep 1 H + lam • boundaryZZ)).mp h switch2
  change Commute (concreteStep 1 H + lam • boundaryZZ - concreteStep 1 H)
    (concreteStep 1 switch2) at hc
  apply boundaryZZ_not_commute_old_switch lam hlam
  simpa only [add_sub_cancel_left] using hc

end InfoGeometry.Canonical.CuntzBoundaryCouplingObstruction
