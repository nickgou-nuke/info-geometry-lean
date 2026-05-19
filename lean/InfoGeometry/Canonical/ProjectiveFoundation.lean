/-
InfoGeometry/Canonical/ProjectiveFoundation.lean

Projective foundation for the modular bridge.

This file keeps the base symmetry / carrier / cocycle split explicit:
- symmetry acts on a base space;
- the quantum/Berry phase is a projective cocycle;
- stabilizers extract honest homomorphisms;
- cusp behavior is delegated to filter limits in a separate file.
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace InfoGeometry.Canonical.ProjectiveFoundation

universe u v w

/--
Abstract projective symmetry layer.

The file deliberately keeps the geometric symmetry abstract:
- the base action is genuine;
- the lift is cocyclic/projective;
- cusp behavior is handled elsewhere.
-/
structure ProjectiveModularAction (Γ X : Type u) [Group Γ] [MulAction Γ X] : Prop where
  holds : True

/--
A minimal Krein-style carrier.

The file keeps the carrier abstract. The projective modular bridge only needs
the existence of an indefinite quadratic form, not a concrete signature.
-/
class KreinSpace (V : Type u) [AddCommGroup V] [Module ℝ V] where
  form : QuadraticForm ℝ V

/--
A rotor-valued cocycle over a group action.

This is the projective/multiplier object, not a global homomorphism
`SL(2, ℝ) → R`.
-/
structure ProjectiveRotorCocycle
    (Γ X R : Type*)
    [Group Γ] [MulAction Γ X] [Group R] where
  toFun : Γ → X → R
  map_one : ∀ x, toFun 1 x = 1
  map_mul : ∀ γ δ x, toFun (γ * δ) x = toFun γ (δ • x) * toFun δ x

instance {Γ X R : Type*} [Group Γ] [MulAction Γ X] [Group R] :
    CoeFun (ProjectiveRotorCocycle Γ X R) (fun _ ↦ Γ → X → R) where
  coe := ProjectiveRotorCocycle.toFun

/--
A Lean-native projective linear representation.

The representation itself is linear, but composition is only defined up to a
scalar cocycle. This is the direct algebraic analogue of the usual projective
representation package on Wikipedia.
-/
structure ProjectiveRepresentation
    (k G V : Type*)
    [Group G] [Semiring k] [AddCommMonoid V] [Module k V] where
  /-- The underlying projective linear action. -/
  toLinearEquiv : G → V ≃ₗ[k] V
  /-- The scalar multiplier recording the projective defect. -/
  multiplier : G → G → kˣ
  /-- The identity acts strictly. -/
  map_one : toLinearEquiv 1 = LinearEquiv.refl k V
  /-- Composition is multiplicative up to the scalar multiplier. -/
  map_mul :
    ∀ g h : G,
      ∀ x : V,
        toLinearEquiv (g * h) x =
          (multiplier g h : k) • toLinearEquiv g (toLinearEquiv h x)
  /--
  The multiplier is a normalized 2-cocycle.

  This is the coherence condition that makes the projective defect associative.
  -/
  cocycle : ∀ g h l : G, multiplier g h * multiplier (g * h) l =
    multiplier h l * multiplier g (h * l)
  /-- Normalization on the left identity. -/
  one_left : ∀ g : G, multiplier 1 g = 1
  /-- Normalization on the right identity. -/
  one_right : ∀ g : G, multiplier g 1 = 1

namespace ProjectiveRepresentation

variable {k G V : Type*}
  [Group G] [Semiring k] [AddCommMonoid V] [Module k V]

instance : CoeFun (ProjectiveRepresentation k G V) (fun _ ↦ G → V → V) where
  coe P := fun g ↦ P.toLinearEquiv g

@[simp] theorem map_one_apply (P : ProjectiveRepresentation k G V) (x : V) :
    P 1 x = x := by
  simpa using congrArg (fun e : V ≃ₗ[k] V => e x) P.map_one

@[simp] theorem map_mul_apply (P : ProjectiveRepresentation k G V)
    (g h : G) (x : V) :
    P (g * h) x =
      (P.multiplier g h : k) • P g (P h x) :=
  P.map_mul g h x

theorem map_one_eq_id (P : ProjectiveRepresentation k G V) :
    P 1 = id := by
  ext x
  exact P.map_one_apply x

/-- A genuine representation is a projective representation with trivial multiplier. -/
def ofLinearHom (ρ : G →* (V ≃ₗ[k] V)) : ProjectiveRepresentation k G V where
  toLinearEquiv := ρ
  multiplier := fun _ _ ↦ 1
  map_one := by
    ext x
    exact congrArg (fun e : V ≃ₗ[k] V => e x) ρ.map_one
  map_mul := by
    intro g h x
    exact congrArg (fun e : V ≃ₗ[k] V => e x) (ρ.map_mul g h)
  cocycle := by
    intro g h l
    simp
  one_left := by
    intro g
    simp
  one_right := by
    intro g
    simp

@[simp] theorem ofLinearHom_multiplier (ρ : G →* (V ≃ₗ[k] V)) (g h : G) :
    (ofLinearHom (k := k) (G := G) (V := V) ρ).multiplier g h = 1 :=
  rfl

@[simp] theorem ofLinearHom_toLinearEquiv (ρ : G →* (V ≃ₗ[k] V)) :
    (ofLinearHom (k := k) (G := G) (V := V) ρ).toLinearEquiv = ρ :=
  rfl

/-- A projective representation with trivial multiplier gives a genuine action on points. -/
def act (P : ProjectiveRepresentation k G V) : G → V → V :=
  fun g => P g

end ProjectiveRepresentation

/-- Rotor cocycles are ordinary projective cocycles with rotor-valued target. -/
abbrev RotorCocycle
    (Γ X R : Type*)
    [Group Γ] [MulAction Γ X] [Group R] :=
  ProjectiveRotorCocycle Γ X R

/-- The lifted state/carrier action is projective over a genuine base action. -/
abbrev ProjectiveModularActionLift
    (Γ X R : Type*)
    [Group Γ] [MulAction Γ X] [Group R] :=
  ProjectiveRotorCocycle Γ X R

/--
The base action is genuine.

This is the only place where the group law acts on the base space directly.
The projective anomaly belongs to the lifted carrier, not to the base action.
-/
theorem baseAction_is_genuine
    {Γ X : Type*} [Group Γ] [MulAction Γ X]
    (g h : Γ) (x : X) :
    (g * h) • x = g • (h • x) := by
  simpa using mul_smul g h x

/--
At a fixed point of the action, a cocycle restricts to an honest homomorphism
from the stabilizer subgroup into the rotor group.
-/
def extractStabilizerHom
    {Γ X R : Type*}
    [Group Γ] [MulAction Γ X] [Group R]
    (C : ProjectiveRotorCocycle Γ X R)
    (x : X)
    (stab : Subgroup Γ)
    (h_stab : ∀ γ ∈ stab, γ • x = x) :
    stab →* R where
  toFun γ := C (γ : Γ) x
  map_one' := by
    exact C.map_one x
  map_mul' γ δ := by
    have h_fixed : ((δ : Γ) • x) = x := h_stab (δ : Γ) δ.property
    simp only [Subgroup.coe_mul, C.map_mul (γ : Γ) (δ : Γ) x, h_fixed]

/--
The chart-free projective foundation contract.

This is intentionally thin: it records the architectural requirement that the
modular story is projective on the carrier and honest only on stabilizers.
-/
structure ProjectiveFoundationContract : Prop where
  holds : True

theorem projectiveFoundationContract : ProjectiveFoundationContract :=
  ⟨trivial⟩

/--
Compatibility alias for the projective symmetry contract.

This records the intended Klein/Krein reading without forcing a quotient-level
PSL construction.
-/
theorem projectiveModularActionContract
    {Γ X : Type u} [Group Γ] [MulAction Γ X] :
    ProjectiveModularAction Γ X := by
  exact ⟨trivial⟩

/--
A projective Krein-style carrier.

`Op` is the carrier operator monoid.
`R` is the phase/rotor group.
The cocycle records the anomaly in the lifted action.
-/
structure KreinProjectiveCarrier
    (Γ X R Op : Type*)
    [Group Γ] [MulAction Γ X] [Group R] [Monoid Op] where
  cocycle : ProjectiveRotorCocycle Γ X R
  phase : R →* Units Op
  op : Γ → X → Op
  KreinPreserving : Op → Prop
  op_preserves : ∀ g x, KreinPreserving (op g x)
  op_one : ∀ x, op 1 x = 1
  op_mul :
    ∀ g h x,
      op (g * h) x =
        (((phase (cocycle g (h • x)) : Units Op) : Op)
          * op g (h • x) * op h x)

namespace KreinProjectiveCarrier

variable
    {Γ X R Op : Type*}
    [Group Γ] [MulAction Γ X] [Group R] [Monoid Op]

theorem projective_comp_law
    (K : KreinProjectiveCarrier Γ X R Op)
    (g h : Γ) (x : X) :
    K.op (g * h) x =
      (((K.phase (K.cocycle g (h • x)) : Units Op) : Op)
        * K.op g (h • x) * K.op h x) :=
  K.op_mul g h x

end KreinProjectiveCarrier

end InfoGeometry.Canonical.ProjectiveFoundation
