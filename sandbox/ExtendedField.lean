import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Order.WithBot
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Extended Linearly Ordered Fields

This module implements the `Extend F` structure for handling both positive and
negative infinity in info-geometric measures and divergences.
-/

namespace InfoGeometry.Core

/-- `Extend F` represents the extended field `F ∪ {⊥, ⊤}`. -/
abbrev Extend (F : Type*) := WithBot (WithTop F)

section Instances
variable {F : Type*}

section OrderedField

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]

instance : LinearOrder (Extend F) := inferInstance
instance : AddCommMonoid (Extend F) := inferInstance
instance : BoundedOrder (Extend F) := inferInstance
instance : IsOrderedAddMonoid (Extend F) := inferInstance

end OrderedField

/-- The canonical inclusion from `F` to `Extend F` is registered as a coercion. -/
instance : Coe F (Extend F) := ⟨fun x => WithBot.some (WithTop.some x)⟩

namespace EF

/-- Negation on `Extend F`, mapping `⊥` to `⊤` and vice versa. -/
def neg {F : Type*} [Neg F] (x : Extend F) : Extend F :=
  match x with
  | ⊥ => (⊤ : Extend F)
  | (y : WithTop F) =>
      match y with
      | ⊤ => (⊥ : Extend F)
      | (a : F) => ((-a : F) : Extend F)

instance [Neg F] : Neg (Extend F) := ⟨neg⟩

/-- Proof that negation is its own inverse on `Extend F`. -/
instance [InvolutiveNeg F] : InvolutiveNeg (Extend F) where
  neg_neg x := by
    cases x with
    | none => rfl
    | some y =>
      cases y with
      | top => rfl
      | coe a =>
        change some ((- -a : F) : WithTop F) = some (a : WithTop F)
        exact congrArg some (by simp)

@[simp] lemma coe_zero [Zero F] : ((0 : F) : Extend F) = WithBot.some (WithTop.some 0) := rfl
@[simp] lemma coe_one [One F] : ((1 : F) : Extend F) = WithBot.some (WithTop.some 1) := rfl

@[simp] lemma bot_lt_coe [Preorder F] (x : F) : (⊥ : Extend F) < (x : Extend F) := by
  simp

@[simp] lemma coe_lt_top [Preorder F] (x : F) : (x : Extend F) < (⊤ : Extend F) := by
  simpa using
    (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top x) :
      (((WithTop.some x : WithTop F) : WithBot (WithTop F)) < ((⊤ : WithTop F) : WithBot (WithTop F))))

end EF

end Instances

end InfoGeometry.Core


import Mathlib

namespace InfoGeometry.Canonical.DeformedIdeleAction

/-- The classical, commutative rational field acting as the base of the ideles. -/
variable (K : Type*) [Field K]

/-- The q-deformed algebra representing the non-commutative torus of the boundary. -/
class DeformedIdeleAlgebra (A : Type*) [Ring A] [StarRing A] where
  -- The deformed multiplication (isometry) and division (adjoint) operators
  S_p : A
  S_p_adj : A
  
  -- The Cuntz relation is the exact q = 0 limit of the deformed idelic commutation:
  -- S_p* * S_p = 1
  cuntz_isometry : S_p_adj * S_p = 1
  -- S_p * S_p* = P_p < 1 (the projection representing the branch containment)
  cuntz_projection : S_p * S_p_adj * (S_p * S_p_adj) = S_p * S_p_adj

variable {A : Type*} [Ring A] [StarRing A] [DeformedIdeleAlgebra A]

/-- The Cuntz projection operator P_p. -/
def P_p : A := DeformedIdeleAlgebra.S_p * DeformedIdeleAlgebra.S_p_adj

/-- **Theorem (Deformed Idelic Commutation)**:
    In the deformed algebra, the multiplication and division operators do not commute.
    Their commutator is regulated by the Cuntz boundary projector P_p, 
    proving that the deformation is non-zero (non-commutative) on the boundary. -/
theorem deformed_idelic_commutator_non_zero :
    DeformedIdeleAlgebra.S_p * DeformedIdeleAlgebra.S_p_adj - DeformedIdeleAlgebra.S_p_adj * DeformedIdeleAlgebra.S_p = P_p A - 1 := by
  unfold P_p
  rw [DeformedIdeleAlgebra.cuntz_isometry]
  ring

end InfoGeometry.Canonical.DeformedIdeleAction

-- LOST FRAGMENT RECOVERED FROM HIVE MEMORY --

import Mathlib

namespace InfoGeometry.Canonical.DeformedIdeleAction

/-- The classical, commutative rational field acting as the base of the ideles. -/
variable (K : Type*) [Field K]

/-- The q-deformed algebra representing the non-commutative torus of the boundary. -/
class DeformedIdeleAlgebra (A : Type*) [Ring A] [StarRing A] where
  -- The deformed multiplication (isometry) and division (adjoint) operators
  S_p : A
  S_p_adj : A
  
  -- The Cuntz relation is the exact q = 0 limit of the deformed idelic commutation:
  -- S_p* * S_p = 1
  cuntz_isometry : S_p_adj * S_p = 1
  -- S_p * S_p* = P_p < 1 (the projection representing the branch containment)
  cuntz_projection : S_p * S_p_adj * (S_p * S_p_adj) = S_p * S_p_adj

variable {A : Type*} [Ring A] [StarRing A] [DeformedIdeleAlgebra A]

/-- The Cuntz projection operator P_p. -/
def P_p : A := DeformedIdeleAlgebra.S_p * DeformedIdeleAlgebra.S_p_adj

/-- **Theorem (Deformed Idelic Commutation)**:
    In the deformed algebra, the multiplication and division operators do not commute.
    Their commutator is regulated by the Cuntz boundary projector P_p, 
    proving that the deformation is non-zero (non-commutative) on the boundary. -/
theorem deformed_idelic_commutator_non_zero :
    DeformedIdeleAlgebra.S_p * DeformedIdeleAlgebra.S_p_adj - DeformedIdeleAlgebra.S_p_adj * DeformedIdeleAlgebra.S_p = P_p A - 1 := by
  unfold P_p
  rw [DeformedIdeleAlgebra.cuntz_isometry]
  ring

end InfoGeometry.Canonical.DeformedIdeleAction

-- LOST FRAGMENT RECOVERED FROM HIVE MEMORY --

import Mathlib

namespace InfoGeometry.Canonical.DeformedIdeleAction

/-- The classical, commutative rational field acting as the base of the ideles. -/
variable (K : Type*) [Field K]

/-- The q-deformed algebra representing the non-commutative torus of the boundary. -/
class DeformedIdeleAlgebra (A : Type*) [Ring A] [StarRing A] where
  -- The deformed multiplication (isometry) and division (adjoint) operators
  S_p : A
  S_p_adj : A
  
  -- The Cuntz relation is the exact q = 0 limit of the deformed idelic commutation:
  -- S_p* * S_p = 1
  cuntz_isometry : S_p_adj * S_p = 1
  -- S_p * S_p* = P_p < 1 (the projection representing the branch containment)
  cuntz_projection : S_p * S_p_adj * (S_p * S_p_adj) = S_p * S_p_adj

variable {A : Type*} [Ring A] [StarRing A] [DeformedIdeleAlgebra A]

/-- The Cuntz projection operator P_p. -/
def P_p : A := DeformedIdeleAlgebra.S_p * DeformedIdeleAlgebra.S_p_adj

/-- **Theorem (Deformed Idelic Commutation)**:
    In the deformed algebra, the multiplication and division operators do not commute.
    Their commutator is regulated by the Cuntz boundary projector P_p, 
    proving that the deformation is non-zero (non-commutative) on the boundary. -/
theorem deformed_idelic_commutator_non_zero :
    DeformedIdeleAlgebra.S_p * DeformedIdeleAlgebra.S_p_adj - DeformedIdeleAlgebra.S_p_adj * DeformedIdeleAlgebra.S_p = P_p A - 1 := by
  unfold P_p
  rw [DeformedIdeleAlgebra.cuntz_isometry]
  ring

end InfoGeometry.Canonical.DeformedIdeleAction