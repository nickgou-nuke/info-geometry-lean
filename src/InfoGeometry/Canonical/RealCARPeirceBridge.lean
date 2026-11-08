/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.FractalCantorFock

/-! Reflexive Peirce identities for the existing real CAR interface. -/
namespace InfoGeometry.Topology.FractalCantorFock.RealCARPair
variable {A : Type*} [Ring A] (C : RealCARPair A)

theorem annihilation_reflexive :
    C.annihilation * C.creation * C.annihilation = C.annihilation := by
  rw [C.annihilation_creation_eq_one_sub_creation_annihilation]
  simp [sub_mul, mul_assoc, C.nilpotent_annihilation]

theorem creation_reflexive :
    C.creation * C.annihilation * C.creation = C.creation := by
  rw [C.creation_annihilation_eq_one_sub_annihilation_creation]
  simp [sub_mul, mul_assoc, C.nilpotent_creation]

end InfoGeometry.Topology.FractalCantorFock.RealCARPair
