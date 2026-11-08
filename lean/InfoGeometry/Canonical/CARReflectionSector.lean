/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealCARPeirceBridge
import InfoGeometry.Canonical.Cl11CARFockColimitBridge

/-! Reflection-fixed vectors cannot lie in just one CAR sector.
These are algebraic module statements, not assertions about Pin bundles or norms. -/
namespace InfoGeometry.Topology.FractalCantorFock.RealCARPair
variable {A : Type*} [Ring A] (C : RealCARPair A)

theorem reflection_sector_compression :
    (C.annihilation * C.creation) * (C.annihilation + C.creation) *
      (C.annihilation * C.creation) = 0 := by
  have h := C.annihilation_reflexive
  noncomm_ring [C.nilpotent_annihilation, C.nilpotent_creation, h]
  rw [← mul_assoc, C.nilpotent_annihilation, zero_mul]

theorem reflection_fixed_sector_eq_zero {V : Type*} [AddCommMonoid V] [Module A V]
    (x : V) (hp : (C.annihilation * C.creation) • x = x)
    (hq : (C.annihilation + C.creation) • x = x) : x = 0 := by
  have hz := congrArg (fun a : A => a • x) C.reflection_sector_compression
  simpa only [mul_smul, hp, hq, zero_smul] using hz

end InfoGeometry.Topology.FractalCantorFock.RealCARPair

namespace InfoGeometry.Canonical.CARReflectionSector
open Cl11CARFockColimitBridge

/-- The obstruction applies to the constructed CAR pair in the algebraic colimit. -/
theorem colimit_fixed_sector_eq_zero (k : ℕ)
    (x : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit)
    (hp : ((algebraicCARPair k).annihilation * (algebraicCARPair k).creation) * x = x)
    (hq : ((algebraicCARPair k).annihilation + (algebraicCARPair k).creation) * x = x) :
    x = 0 :=
  (algebraicCARPair k).reflection_fixed_sector_eq_zero x hp hq

end InfoGeometry.Canonical.CARReflectionSector
