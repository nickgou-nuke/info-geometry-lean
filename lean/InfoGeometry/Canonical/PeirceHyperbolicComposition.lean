/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceMatrixUnitCompletion

/-! Composition of completed active-corner units and normalized boosts. -/
namespace InfoGeometry.Canonical.PeirceHyperbolicComposition
open ReflexiveNilpotentFlows PeirceMatrixUnitCompletion
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {d B : A} (hd : d*d=0) (hB : B*B=0)
  (hr : d*B*d=d) (hs : B*d*B=B)

/-- The native group representation of active matrix units in the ambient algebra. -/
def completedUnitHom : (Matrix (Fin 2) (Fin 2) R)ˣ →* Aˣ where
  toFun := completedUnit hd hB hr hs
  map_one' := by
    apply Units.ext
    exact completedMatrix_one
  map_mul' M N := by
    apply Units.ext
    exact (completedMatrix_mul hd hB hr hs (M : Matrix (Fin 2) (Fin 2) R)
      (N : Matrix (Fin 2) (Fin 2) R)).symm

theorem hyperbolic_norm_comp (u v e f : R) (hu : u*u-v*v=1) (he : e*e-f*f=1) :
    (u*e+v*f)*(u*e+v*f)-(u*f+v*e)*(u*f+v*e)=1 := by
  calc
    _ = (u*u-v*v)*(e*e-f*f) := by ring
    _ = 1 := by rw [hu, he, one_mul]

include hd hB hr hs

theorem hyperbolicUnit_mul (u v e f : R) (hu : u*u-v*v=1) (he : e*e-f*f=1) :
    hyperbolicUnit hd hB hr hs u v hu * hyperbolicUnit hd hB hr hs e f he =
      hyperbolicUnit hd hB hr hs (u*e+v*f) (u*f+v*e)
        (hyperbolic_norm_comp u v e f hu he) := by
  apply Units.ext
  change completedMatrix d B !![u, v; v, u] * completedMatrix d B !![e, f; f, e] = _
  rw [completedMatrix_mul hd hB hr hs]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem hyperbolicUnit_inv (u v : R) (h : u*u-v*v=1) :
    (hyperbolicUnit hd hB hr hs u v h)⁻¹ =
      hyperbolicUnit hd hB hr hs u (-v) (by simpa using h) := by
  apply Units.ext
  rfl

/-- Successive normalized boosts act on the existing hyperbolic projection orbit. -/
theorem hyperbolic_orbit_composition (u v e f : R)
    (hu : u*u-v*v=1) (he : e*e-f*f=1) :
    (hyperbolicUnit hd hB hr hs u v hu : A) *
      PeirceHyperbolicOrbit.hyperbolicPlus e f d B *
      (↑(hyperbolicUnit hd hB hr hs u v hu)⁻¹ : A) =
      PeirceHyperbolicOrbit.hyperbolicPlus (u*e+v*f) (u*f+v*e) d B := by
  rw [← hyperbolicUnit_conjugates_plus hd hB hr hs e f he,
    ← hyperbolicUnit_conjugates_plus hd hB hr hs (u*e+v*f) (u*f+v*e)
      (hyperbolic_norm_comp u v e f hu he)]
  simp only [← hyperbolicUnit_mul hd hB hr hs u v e f hu he,
    mul_inv_rev, Units.val_mul]
  noncomm_ring

end InfoGeometry.Canonical.PeirceHyperbolicComposition
