import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.Modular

noncomputable section

namespace InfoGeometry.Canonical.Algebraic

/-! ### 1. The Abstract Rotor Cocycle -/

/--
A multiplicative action cocycle (projective representation).
This defines a map `Γ × X → R` that respects the group action of `Γ` on `X`.
Physically: the gauge-dependent transformation of a state bundle over `X`
under the symmetry group `Γ`, returning a localized phase/rotor in `R`.
-/
structure MulActionCocycle
    (Γ X R : Type*)
    [Group Γ] [MulAction Γ X] [Group R] where
  toFun : Γ → X → R
  map_one : ∀ x, toFun 1 x = 1
  map_mul : ∀ γ δ x,
    toFun (γ * δ) x = (toFun γ (δ • x)) * (toFun δ x)

instance {Γ X R : Type*} [Group Γ] [MulAction Γ X] [Group R] :
    CoeFun (MulActionCocycle Γ X R) (fun _ ↦ Γ → X → R) where
  coe := MulActionCocycle.toFun

/-! ### 2. The Modular Specialization -/

abbrev Γ : Type := Matrix.SpecialLinearGroup (Fin 2) ℤ
abbrev H : Type := UpperHalfPlane
abbrev modularFD : Set H := ModularGroup.fd
abbrev modularFDo : Set H := ModularGroup.fdo

abbrev SpinGroup (R : Type*) := Group R

variable {R : Type*} [SpinGroup R]

/--
The modular rotor cocycle.
This represents the exact Berry phase transformation.
Because the automorphic factor `j(γ, τ) = cτ + d` depends on the point
`τ ∈ ℍ`, the representation into `Spin(2)` cannot be a global `MonoidHom`.
It must be a cocycle over `ℍ`.
-/
abbrev ModularBerryCocycle := MulActionCocycle Γ UpperHalfPlane R

/-! ### 3. Stabilizer Limits (The Anomaly Extraction) -/

/--
When restricted to a fixed point (stabilizer) of the modular action,
the cocycle perfectly collapses into a strict group homomorphism.
This isolates the exact topological anomaly at the elliptic points.
-/
def extractStabilizerHom
    (C : ModularBerryCocycle (R := R))
    (τ : UpperHalfPlane)
    (stabilizerGrp : Subgroup Γ)
    (h_stab : ∀ γ ∈ stabilizerGrp, γ • τ = τ) :
    stabilizerGrp →* R where
  toFun γ := C ↑γ τ
  map_one' := C.map_one τ
  map_mul' γ δ := by
    have h_fixed : (δ : Γ) • τ = τ := h_stab δ δ.property
    have cocycle_prop := C.map_mul ↑γ ↑δ τ
    rw [h_fixed] at cocycle_prop
    exact cocycle_prop

end InfoGeometry.Canonical.Algebraic
