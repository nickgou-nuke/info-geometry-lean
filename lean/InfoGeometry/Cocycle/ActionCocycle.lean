import InfoGeometry.Canonical.Algebraic.ModularRotorCocycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Action Cocycle Calculus

This file owns monoid/group-action versions of the cocycle chain rule.

The groupoid files own local-arrow cocycles. This file owns the common
global-action specialization used by determinant, Jacobian, Radon-Nikodym, and
modular-rotor examples.
-/

noncomputable section

namespace InfoGeometry.Cocycle

open InfoGeometry.Canonical.Algebraic

/-! ## Coefficient-action 1-cocycles -/

/--
A multiplicative 1-cocycle for a monoid action on coefficient units.

The law is the abstract chain rule `c (g*h) = c g * g • c h`.
-/
structure MultiplicativeOneCocycle (G U : Type*) [Monoid G] [Group U]
    [MulDistribMulAction G U] where
  toFun : G → U
  map_one : toFun 1 = 1
  map_mul : ∀ g h : G, toFun (g * h) = toFun g * g • toFun h

instance {G U : Type*} [Monoid G] [Group U] [MulDistribMulAction G U] :
    CoeFun (MultiplicativeOneCocycle G U) (fun _ => G → U) where
  coe := MultiplicativeOneCocycle.toFun

namespace MultiplicativeOneCocycle

variable {G U : Type*} [Monoid G] [Group U] [MulDistribMulAction G U]

@[simp]
theorem map_one_apply (C : MultiplicativeOneCocycle G U) : C 1 = 1 :=
  C.map_one

/-- The multiplicative cocycle chain rule. -/
theorem chain_rule (C : MultiplicativeOneCocycle G U) (g h : G) :
    C (g * h) = C g * g • C h :=
  C.map_mul g h

/--
The canonical multiplicative coboundary `b⁻¹ * g • b`.

This is the algebraic form of changing normalization/trivialization.
-/
def coboundary (b : U) : MultiplicativeOneCocycle G U where
  toFun g := b⁻¹ * g • b
  map_one := by simp
  map_mul := by
    intro g h
    simp [mul_smul, mul_assoc]

end MultiplicativeOneCocycle

/--
A multiplicative 1-cocycle written against an explicit homomorphism into
multiplicative automorphisms.

This is the group version of a nonabelian frame-Jacobian chain rule:
`c (g*h) = c g * α g (c h)`.  It is useful when the coefficient action should
stay visible in the theorem statement rather than be inferred from a typeclass.
-/
structure TwistedGroupCocycle (G U : Type*) [Group G] [Group U] (α : G →* MulAut U) where
  toFun : G → U
  map_mul : ∀ g h : G, toFun (g * h) = toFun g * α g (toFun h)

instance {G U : Type*} [Group G] [Group U] {α : G →* MulAut U} :
    CoeFun (TwistedGroupCocycle G U α) (fun _ => G → U) where
  coe := TwistedGroupCocycle.toFun

namespace TwistedGroupCocycle

variable {G U : Type*} [Group G] [Group U] {α : G →* MulAut U}

/-- The explicit-action multiplicative cocycle chain rule. -/
theorem chain_rule (C : TwistedGroupCocycle G U α) (g h : G) :
    C (g * h) = C g * α g (C h) :=
  C.map_mul g h

@[simp]
theorem map_one_apply (C : TwistedGroupCocycle G U α) :
    C 1 = 1 := by
  have h := C.chain_rule 1 1
  simp at h
  have hleft := congrArg (fun x => (C 1)⁻¹ * x) h
  simpa [mul_assoc] using hleft.symm

end TwistedGroupCocycle

/--
An additive 1-cocycle for a monoid action on additive coefficients.

The law is the logarithmic chain rule `ℓ (g*h) = ℓ g + g • ℓ h`.
-/
structure AdditiveOneCocycle (G V : Type*) [Monoid G] [AddGroup V]
    [DistribMulAction G V] where
  toFun : G → V
  map_one : toFun 1 = 0
  map_mul : ∀ g h : G, toFun (g * h) = toFun g + g • toFun h

instance {G V : Type*} [Monoid G] [AddGroup V] [DistribMulAction G V] :
    CoeFun (AdditiveOneCocycle G V) (fun _ => G → V) where
  coe := AdditiveOneCocycle.toFun

namespace AdditiveOneCocycle

variable {G V : Type*} [Monoid G] [AddGroup V] [DistribMulAction G V]

@[simp]
theorem map_one_apply (C : AdditiveOneCocycle G V) : C 1 = 0 :=
  C.map_one

/-- The additive/logarithmic cocycle chain rule. -/
theorem chain_rule (C : AdditiveOneCocycle G V) (g h : G) :
    C (g * h) = C g + g • C h :=
  C.map_mul g h

/-- The canonical additive coboundary `-B + g • B`. -/
def coboundary (B : V) : AdditiveOneCocycle G V where
  toFun g := -B + g • B
  map_one := by simp
  map_mul := by
    intro g h
    simp [mul_smul, add_assoc]

end AdditiveOneCocycle

/-! ## Transformation-space action cocycles -/

/--
An additive action cocycle over a transformation space.

The base action supplies the pullback/twist:
`L (γ*δ) x = L γ (δ • x) + L δ x`.
-/
structure AddActionCocycle (Γ X V : Type*) [Group Γ] [MulAction Γ X] [AddGroup V] where
  toFun : Γ → X → V
  map_one : ∀ x, toFun 1 x = 0
  map_mul : ∀ γ δ x, toFun (γ * δ) x = toFun γ (δ • x) + toFun δ x

instance {Γ X V : Type*} [Group Γ] [MulAction Γ X] [AddGroup V] :
    CoeFun (AddActionCocycle Γ X V) (fun _ => Γ → X → V) where
  coe := AddActionCocycle.toFun

namespace AddActionCocycle

variable {Γ X V : Type*} [Group Γ] [MulAction Γ X] [AddGroup V]

@[simp]
theorem map_one_apply (C : AddActionCocycle Γ X V) (x : X) : C 1 x = 0 :=
  C.map_one x

/-- The additive action-cocycle chain rule. -/
theorem chain_rule (C : AddActionCocycle Γ X V) (γ δ : Γ) (x : X) :
    C (γ * δ) x = C γ (δ • x) + C δ x :=
  C.map_mul γ δ x

end AddActionCocycle

/-- A group homomorphism is an action cocycle over the trivial base. -/
def groupHomAsMulActionCocycle {Γ R : Type*} [Group Γ] [Group R] (φ : Γ →* R) :
    MulActionCocycle Γ PUnit R where
  toFun γ _ := φ γ
  map_one := by simp
  map_mul := by
    intro γ δ x
    simp [φ.map_mul γ δ]

@[simp]
theorem groupHomAsMulActionCocycle_apply {Γ R : Type*} [Group Γ] [Group R]
    (φ : Γ →* R) (γ : Γ) (x : PUnit) :
    groupHomAsMulActionCocycle φ γ x = φ γ :=
  rfl

namespace MulActionCocycle

variable {Γ X R : Type*} [Group Γ] [MulAction Γ X] [Group R]

/--
The canonical action-cocycle coboundary `b(γ • x) * b(x)⁻¹`.

This is the transformation-space version of changing local trivialization.
-/
def coboundary (b : X → R) : MulActionCocycle Γ X R where
  toFun γ x := b (γ • x) * (b x)⁻¹
  map_one := by
    intro x
    simp
  map_mul := by
    intro γ δ x
    simp [mul_smul, mul_assoc]

@[simp]
theorem coboundary_apply (b : X → R) (γ : Γ) (x : X) :
    coboundary b γ x = b (γ • x) * (b x)⁻¹ :=
  rfl

/--
Taking `log |-|` of a real-unit action cocycle gives an additive action
cocycle.
-/
noncomputable def logAbsUnits (C : MulActionCocycle Γ X ℝˣ) :
    AddActionCocycle Γ X ℝ where
  toFun γ x := Real.log |((C γ x : ℝˣ) : ℝ)|
  map_one := by
    intro x
    rw [C.map_one x]
    simp
  map_mul := by
    intro γ δ x
    rw [C.map_mul]
    simp only [Units.val_mul]
    rw [abs_mul]
    have hγ : |((C γ (δ • x) : ℝˣ) : ℝ)| ≠ 0 := by
      exact abs_ne_zero.mpr (Units.ne_zero (C γ (δ • x)))
    have hδ : |((C δ x : ℝˣ) : ℝ)| ≠ 0 := by
      exact abs_ne_zero.mpr (Units.ne_zero (C δ x))
    rw [Real.log_mul hγ hδ]

end MulActionCocycle

end InfoGeometry.Cocycle
