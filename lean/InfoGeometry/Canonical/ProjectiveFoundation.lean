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
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace InfoGeometry.Canonical.ProjectiveFoundation

open scoped LinearAlgebra.Projectivization

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
    simpa using congrArg (fun e : V ≃ₗ[k] V => e x) (ρ.map_mul g h)
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

namespace ProjectiveRepresentation

section ProjectivizationAction

variable {K G V : Type*}
  [Group G] [DivisionRing K] [AddCommGroup V] [Module K V]

/--
The induced action on projective space.

This is the key geometric output of a projective representation: the scalar
defect is invisible after passing to rays.
-/
def projectivizationMap (P : ProjectiveRepresentation K G V) :
    G → ℙ K V → ℙ K V :=
  fun g => Projectivization.map (K := K) (V := V) (L := K) (W := V)
    (σ := RingHom.id K) (P.toLinearEquiv g).toLinearMap
    (LinearEquiv.injective (P.toLinearEquiv g))

@[simp] theorem projectivizationMap_mk (P : ProjectiveRepresentation K G V)
    (g : G) (v : V) (hv : v ≠ 0) :
    P.projectivizationMap g (Projectivization.mk K v hv) =
      Projectivization.mk (K := K) (V := V) (P.toLinearEquiv g v)
        ((P.toLinearEquiv g).map_ne_zero_iff.mpr hv) := by
  rfl

theorem projectivizationMap_one (P : ProjectiveRepresentation K G V) :
    P.projectivizationMap 1 = id := by
  ext ⟨v, hv⟩
  simp [projectivizationMap, P.map_one]

theorem projectivizationMap_mul (P : ProjectiveRepresentation K G V)
    (g h : G) :
    P.projectivizationMap (g * h) =
      P.projectivizationMap g ∘ P.projectivizationMap h := by
  ext ⟨v, hv⟩
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨P.multiplier g h, ?_⟩
  simpa [projectivizationMap, Projectivization.map_mk] using
    (P.map_mul_apply g h v).symm

/-- The projective representation induces a genuine monoid action on projective space. -/
def projectivizationAction (P : ProjectiveRepresentation K G V) : G →* Function.End (ℙ K V) where
  toFun := P.projectivizationMap
  map_one' := by
    simpa [Function.End.one_def] using P.projectivizationMap_one
  map_mul' := P.projectivizationMap_mul

end ProjectivizationAction

section CentralExtension

variable {K G V : Type*}
  [Group G] [Field K] [AddCommGroup V] [Module K V]

/--
The cocycle extension attached to a projective representation.

-/
structure centralExtension (P : ProjectiveRepresentation K G V) where
  fst : G
  snd : Kˣ

namespace centralExtension

variable (P : ProjectiveRepresentation K G V)

instance (priority := 1001) : Mul (P.centralExtension) where
  mul x y := ⟨x.1 * y.1, x.2 * y.2 * P.multiplier x.1 y.1⟩

instance : One (P.centralExtension) where
  one := ⟨1, 1⟩

instance : Inhabited (P.centralExtension) := ⟨1⟩

@[ext]
theorem ext {x y : P.centralExtension} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := by
  cases x
  cases y
  cases h1
  cases h2
  rfl

instance : Monoid (P.centralExtension) where
  mul := (· * ·)
  one := 1
  mul_assoc x y z := by
    cases x with
    | mk g a =>
    cases y with
    | mk h b =>
    cases z with
    | mk l c =>
      ext
      · change (g * h) * l = g * (h * l)
        exact mul_assoc g h l
      · have h : (({ fst := g, snd := a } : P.centralExtension) *
            ({ fst := h, snd := b } : P.centralExtension) *
            ({ fst := l, snd := c } : P.centralExtension)).snd =
          (({ fst := g, snd := a } : P.centralExtension) *
            (({ fst := h, snd := b } : P.centralExtension) *
              ({ fst := l, snd := c } : P.centralExtension))).snd := by
          simp [mul_assoc, mul_left_comm, mul_comm, P.cocycle]
        exact congrArg (fun u : Kˣ => (u : K)) h
  one_mul x := by
    cases x with
    | mk g a =>
      ext
      · change 1 * g = g
        exact one_mul g
      · have h : ((1 : P.centralExtension) * ({ fst := g, snd := a } : P.centralExtension)).snd =
          ({ fst := g, snd := a } : P.centralExtension).snd := by
          rfl
        exact congrArg (fun u : Kˣ => (u : K)) h
  mul_one x := by
    cases x with
    | mk g a =>
      ext
      · change g * 1 = g
        exact mul_one g
      · have h : (({ fst := g, snd := a } : P.centralExtension) * (1 : P.centralExtension)).snd =
          ({ fst := g, snd := a } : P.centralExtension).snd := by
          rfl
        exact congrArg (fun u : Kˣ => (u : K)) h

@[simp] theorem mul_fst (x y : P.centralExtension) : (x * y).1 = x.1 * y.1 := rfl
@[simp] theorem mul_snd (x y : P.centralExtension) :
    (x * y).2 = x.2 * y.2 * P.multiplier x.1 y.1 := rfl
@[simp] theorem one_fst : (1 : P.centralExtension).1 = (1 : G) := rfl
@[simp] theorem one_snd : (1 : P.centralExtension).2 = (1 : Kˣ) := rfl

/-- The extension projects to the original group. -/
def proj : P.centralExtension →* G where
  toFun := fun x => x.1
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- A projective representation lifts to an honest representation of the central extension. -/
def liftToCentralExtension : P.centralExtension →* (V ≃ₗ[K] V) where
  toFun := fun x => x.2⁻¹ • P.toLinearEquiv x.1
  map_one' := by
    ext v
    simp
  map_mul' := by
    intro x y
    cases x with
    | mk g a =>
    cases y with
    | mk h b =>
      ext v
      simp [P.map_mul_apply, smul_smul, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem liftToCentralExtension_apply (x : P.centralExtension) :
    centralExtension.liftToCentralExtension (P := P) x = x.2⁻¹ • P.toLinearEquiv x.1 := rfl

theorem liftToCentralExtension_proj (x : P.centralExtension) :
    centralExtension.proj (P := P) x = x.1 := rfl

end centralExtension

end CentralExtension

end ProjectiveRepresentation

namespace ProjectiveRepresentation

section PGL

variable {K V : Type*}
  [Field K] [AddCommGroup V] [Module K V]

def scalarEquiv : Kˣ →* (V ≃ₗ[K] V) where
  toFun a := a • LinearEquiv.refl K V
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp [smul_smul, mul_comm]

/-- Two linear equivalences are projectively equivalent if they differ by a scalar. -/
def projectiveEquivSetoid : Setoid (V ≃ₗ[K] V) where
  r e f := ∃ a : Kˣ, f = a • e
  iseqv := by
    constructor
    · intro e
      refine ⟨1, ?_⟩
      ext v
      simp
    · intro e f h
      rcases h with ⟨a, rfl⟩
      refine ⟨a⁻¹, ?_⟩
      ext v
      simp [smul_smul]
    · intro e f g h₁ h₂
      rcases h₁ with ⟨a, rfl⟩
      rcases h₂ with ⟨b, rfl⟩
      refine ⟨b * a, ?_⟩
      ext v
      simp [smul_smul, mul_comm]

/-- The projective linear group as a quotient by scalar equivalence. -/
abbrev PGL := Quotient (projectiveEquivSetoid (K := K) (V := V))

/-- The canonical quotient map to `PGL`. -/
def toPGL : (V ≃ₗ[K] V) → PGL (K := K) (V := V) :=
  Quotient.mk _

/-- The quotient acts on projective space. -/
def pglAction : PGL (K := K) (V := V) → ℙ K V → ℙ K V :=
  Quotient.lift
    (fun e => Projectivization.map e.toLinearMap e.injective)
    (by
      intro e f h
      rcases h with ⟨a, rfl⟩
      ext ⟨v, hv⟩
      change Projectivization.map e.toLinearMap e.injective (Projectivization.mk K v hv) =
        Projectivization.map (a • e).toLinearMap (LinearEquiv.injective (a • e))
          (Projectivization.mk K v hv)
      rw [Projectivization.map_mk, Projectivization.map_mk]
      apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
      refine ⟨a⁻¹, ?_⟩
      simp [smul_smul]
    )

/-- The quotient action agrees with the usual action of a chosen representative. -/
theorem pglAction_mk (e : V ≃ₗ[K] V) :
    pglAction (K := K) (V := V) (toPGL (K := K) (V := V) e)
      = Projectivization.map e.toLinearMap e.injective :=
  rfl

end PGL

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
