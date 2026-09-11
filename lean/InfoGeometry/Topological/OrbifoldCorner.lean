import Mathlib.NumberTheory.Modular
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Algebra.Group.Basic

namespace InfoGeometry.Topological

open UpperHalfPlane
open ModularGroup
open scoped MatrixGroups Modular

/-
Orbifold corner side of the modular architecture.

This file is deliberately separated from `CuspLimit.lean`:
  - `CuspLimit.lean` records the `i∞` asymptotic limit via `Tendsto`.
  - `OrbifoldCorner.lean` records stabilizer extraction at elliptic points.
-/

/-- 
  The generalized Phase/Rotor Cocycle over a Group Action.
  This correctly implements the projective multiplier system, avoiding the
  fatal flaw of assuming SL(2,Z) → Spin(2) is a global homomorphism.
-/
structure RotorCocycle (Γ X R : Type*)[Group Γ] [MulAction Γ X] [Group R] where
  toFun : Γ → X → R
  map_one : ∀ x, toFun 1 x = 1
  map_mul : ∀ γ δ x, toFun (γ * δ) x = (toFun γ (δ • x)) * (toFun δ x)

instance {Γ X R} [Group Γ] [MulAction Γ X][Group R] : 
  CoeFun (RotorCocycle Γ X R) (fun _ ↦ Γ → X → R) where
  coe := RotorCocycle.toFun

/-- 
  The Orbifold Corner Extraction.
  At a fixed point of the Möbius action (τ = i, ρ), the cocycle natively 
  collapses into a strict MonoidHom mapping the stabilizer into the Spin group.
-/
def extractStabilizerHom 
    {R : Type*} [Group R]
    (C : RotorCocycle SL(2, ℤ) UpperHalfPlane R)
    (τ : UpperHalfPlane)
    (stab : Subgroup SL(2, ℤ))
    (h_stab : ∀ γ ∈ stab, γ • τ = τ) : 
    stab →* R where
  toFun γ := C ↑γ τ
  map_one' := C.map_one τ
  map_mul' γ δ := by
    -- Core physical collapse: δ • τ = τ because δ is in the stabilizer.
    have h_fixed : (δ : SL(2, ℤ)) • τ = τ := h_stab δ δ.property
    have cocycle_prop := C.map_mul ↑γ ↑δ τ
    rw [h_fixed] at cocycle_prop
    exact cocycle_prop

end InfoGeometry.Topological
