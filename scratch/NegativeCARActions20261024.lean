/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity

/-!
# Signed CAR bilinear actions

Uncompiled sandbox candidate. These are the two generator actions of the
signed bilinear `-(d i * b j)` under negative mixed CAR. No star identification,
matrix-unit product law, or Lie-superalgebra classification is asserted.
-/

namespace InfoGeometry.OperatorAlgebra

variable {A : Type*} [Ring A]

/-- Signed CAR bilinears act on the forward family at the matching right index. -/
theorem negative_car_bilinear_action_forward {ι : Type*} [DecidableEq ι]
    (d b : ι → A)
    (hdd : ∀ i j, quadraticAnticommutator (d i) (d j) = 0)
    (hdb : ∀ i j, quadraticAnticommutator (d i) (b j) =
      if i = j then -1 else 0) (i j k : ι) :
    quadraticCommutator (-(d i * b j)) (d k) =
      if j = k then d i else 0 := by
  have hbd : quadraticAnticommutator (b j) (d k) =
      if j = k then -1 else 0 := by
    simpa only [quadraticAnticommutator, add_comm, eq_comm] using hdb k j
  calc
    _ = -(d i * quadraticAnticommutator (b j) (d k)) +
        quadraticAnticommutator (d i) (d k) * b j := by
      dsimp [quadraticCommutator, quadraticAnticommutator]
      noncomm_ring
    _ = _ := by
      rw [hbd, hdd]
      by_cases hjk : j = k <;> simp [hjk]

/-- Signed CAR bilinears act contragrediently on the backward family. -/
theorem negative_car_bilinear_action_backward {ι : Type*} [DecidableEq ι]
    (d b : ι → A)
    (hbb : ∀ i j, quadraticAnticommutator (b i) (b j) = 0)
    (hdb : ∀ i j, quadraticAnticommutator (d i) (b j) =
      if i = j then -1 else 0) (i j k : ι) :
    quadraticCommutator (-(d i * b j)) (b k) =
      if i = k then -(b j) else 0 := by
  calc
    _ = -(d i * quadraticAnticommutator (b j) (b k)) +
        quadraticAnticommutator (d i) (b k) * b j := by
      dsimp [quadraticCommutator, quadraticAnticommutator]
      noncomm_ring
    _ = _ := by
      rw [hbb, hdb]
      by_cases hik : i = k <;> simp [hik]

end InfoGeometry.OperatorAlgebra
