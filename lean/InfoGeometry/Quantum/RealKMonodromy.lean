import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Quantum.RealKCategory

/-!
# Real `K` monodromy surfaces

This file keeps monodromy-specific definitions out of the core
`RealKCategory` equivalence module. It records the finite real-linear rotor and
nilpotent projection data that can be checked quickly by Lean.
-/

open CategoryTheory

noncomputable section

namespace InfoGeometry.Quantum.RealKCategory
namespace RealKVect

/-- The two-dimensional complex monodromy space, seen as a `RealKVect` object. -/
noncomputable def monodromyCarrier : RealKVect :=
  RealKVect.complexToRealK.obj (ModuleCat.of ℂ (ℂ × ℂ))

/-- The real rotor `R(θ) = cos θ·I + sin θ·K` as an endomorphism in `RealKVect`. -/
noncomputable def rotor (X : RealKVect) (θ : ℝ) : X ⟶ X :=
  let c := (Real.cos θ : ℝ)
  let s := (Real.sin θ : ℝ)
  let L : X →ₗ[ℝ] X := c • LinearMap.id + s • X.K
  { hom := L
    comm := by
      ext x
      have hKsq_x : X.K (X.K x) = -x := by
        have := congrArg (fun T : X →ₗ[ℝ] X => T x) X.K_sq
        simpa using this
      simp [L, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hKsq_x] }

/-- A `RealKVect` endomorphism with square zero. -/
structure NilpotentHom (X : RealKVect) extends RealKVect.Hom X X where
  nilpotent : toHom.hom.comp toHom.hom = 0

/-- The affine nilpotent factor `I + aN` as a `RealKVect` endomorphism. -/
noncomputable def nilpotentAffine (X : RealKVect) (a : ℝ) (N : NilpotentHom X) : X ⟶ X :=
  { hom := LinearMap.id + a • N.toHom.hom
    comm := by
      ext x
      have hN_comm_x : N.toHom.hom (X.K x) = X.K (N.toHom.hom x) := by
        exact congrArg (fun f : X →ₗ[ℝ] X => f x) N.toHom.comm
      simp [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hN_comm_x] }

/-- Monodromy projection built from the real rotor and a nilpotent affine factor. -/
noncomputable def monodromyProjection (X : RealKVect) (h : ℝ) (N : NilpotentHom X) :
    X ⟶ X :=
  nilpotentAffine X (-2 * Real.pi) N ≫ rotor X (-2 * Real.pi * h)

/-- Readback: the monodromy projection is the stated rotor-after-nilpotent composite. -/
theorem monodromyProjection_hom (X : RealKVect) (h : ℝ) (N : NilpotentHom X) :
    (monodromyProjection X h N).hom =
      (rotor X (-2 * Real.pi * h)).hom.comp
        (LinearMap.id + (-2 * Real.pi : ℝ) • N.toHom.hom) := by
  rfl

end RealKVect
end InfoGeometry.Quantum.RealKCategory
