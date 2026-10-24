/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceHyperbolicOrbit

/-! Naturality of the existing Peirce operators under algebra homomorphisms.
No nilpotency assumptions are needed for these polynomial identities. -/
namespace InfoGeometry.Canonical.PeirceAlgebraTransport
open ReflexiveNilpotentFlows PeirceRotorAction PeirceHyperbolicOrbit
variable {R A C : Type*} [CommRing R] [Ring A] [Ring C] [Algebra R A] [Algebra R C]

theorem map_pairMatrixLinear (f : A →ₐ[R] C) (d B : A)
    (M : Matrix (Fin 2) (Fin 2) R) :
    f (pairMatrixLinear d B M) = pairMatrixLinear (f d) (f B) M := by
  simp [pairMatrixLinear_apply, pairMatrixUnit]

theorem map_rotor (f : A →ₐ[R] C) (c s : R) (d B : A) :
    f (rotor c s d B) = rotor c s (f d) (f B) := by
  simp [rotor, complement, support]

theorem map_movingPlus (f : A →ₐ[R] C) (c s : R) (d B : A) :
    f (movingPlus c s d B) = movingPlus c s (f d) (f B) := by
  simp only [movingPlus, map_mul, map_rotor]

theorem map_hyperbolicPlus (f : A →ₐ[R] C) (u v : R) (d B : A) :
    f (hyperbolicPlus u v d B) = hyperbolicPlus u v (f d) (f B) := by
  exact map_pairMatrixLinear f d B (hyperbolicMatrix u v)

end InfoGeometry.Canonical.PeirceAlgebraTransport
