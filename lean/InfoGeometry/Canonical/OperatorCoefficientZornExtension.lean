import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Tactic

/-!
# OperatorCoefficientZornExtension

Lifts the canonical Zorn derivation structure to operator coefficients.

This module extends the scalar Zorn algebra `O_s` to operator-valued coefficients
`End(H) ⊗ O_s`, formalizing the derivation and involution structures on operator-valued
Zorn matrices.
-/

noncomputable section

open ContinuousLinearMap

namespace InfoGeometry.Canonical.OperatorCoefficientZornExtension

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
=============================================================================
PART 1: Lifting Scalar Zorn Algebra to Operator Coefficients
=============================================================================
-/

/-- The operator-valued Zorn matrix: entries are continuous linear maps on H -/
@[ext]
structure OpZorn (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  a : H →L[ℂ] H
  u : Fin 3 → (H →L[ℂ] H)
  v : Fin 3 → (H →L[ℂ] H)
  b : H →L[ℂ] H

def toProd (X : OpZorn H) : (H →L[ℂ] H) × (Fin 3 → (H →L[ℂ] H)) × (Fin 3 → (H →L[ℂ] H)) × (H →L[ℂ] H) :=
  (X.a, X.u, X.v, X.b)

def fromProd (p : (H →L[ℂ] H) × (Fin 3 → (H →L[ℂ] H)) × (Fin 3 → (H →L[ℂ] H)) × (H →L[ℂ] H)) : OpZorn H :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩

def equivProd : OpZorn H ≃ ((H →L[ℂ] H) × (Fin 3 → (H →L[ℂ] H)) × (Fin 3 → (H →L[ℂ] H)) × (H →L[ℂ] H)) where
  toFun := toProd
  invFun := fromProd
  left_inv _ := rfl
  right_inv _ := rfl

instance : Zero (OpZorn H) := ⟨⟨0, fun _ => 0, fun _ => 0, 0⟩⟩
instance : Add (OpZorn H) := ⟨fun X Y => ⟨X.a + Y.a, fun i => X.u i + Y.u i, fun i => X.v i + Y.v i, X.b + Y.b⟩⟩
instance : Neg (OpZorn H) := ⟨fun X => ⟨-X.a, fun i => -X.u i, fun i => -X.v i, -X.b⟩⟩
instance : Sub (OpZorn H) := ⟨fun X Y => ⟨X.a - Y.a, fun i => X.u i - Y.u i, fun i => X.v i - Y.v i, X.b - Y.b⟩⟩
instance : SMul ℕ (OpZorn H) := ⟨fun n X => ⟨n • X.a, fun i => n • X.u i, fun i => n • X.v i, n • X.b⟩⟩
instance : SMul ℤ (OpZorn H) := ⟨fun n X => ⟨n • X.a, fun i => n • X.u i, fun i => n • X.v i, n • X.b⟩⟩
instance : SMul ℂ (OpZorn H) := ⟨fun c X => ⟨c • X.a, fun i => c • X.u i, fun i => c • X.v i, c • X.b⟩⟩

instance : AddCommGroup (OpZorn H) :=
  equivProd.injective.addCommGroup toProd rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℂ (OpZorn H) :=
  equivProd.injective.module ℂ ⟨⟨toProd, rfl⟩, (fun _ _ => rfl)⟩ (fun _ _ => rfl)

/-- Vector dot product for Fin 3 operator vectors -/
def opDot (u v : Fin 3 → (H →L[ℂ] H)) : H →L[ℂ] H :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Cross product for Fin 3 operator vectors -/
def opCross (u v : Fin 3 → (H →L[ℂ] H)) : Fin 3 → (H →L[ℂ] H) := fun i =>
  match i with
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

/-- The operator-valued Zorn multiplication law -/
def opZornMul (X Y : OpZorn H) : OpZorn H where
  a := X.a * Y.a + opDot X.u Y.v
  u := fun i => X.a * Y.u i + Y.b * X.u i - (opCross X.v Y.v) i
  v := fun i => Y.a * X.v i + X.b * Y.v i + (opCross X.u Y.u) i
  b := X.b * Y.b + opDot X.v Y.u

instance : Mul (OpZorn H) := ⟨opZornMul⟩

/-- The unit operator-valued Zorn matrix -/
def opZornOne : OpZorn H where
  a := 1
  u := fun _ => 0
  v := fun _ => 0
  b := 1

instance : One (OpZorn H) := ⟨opZornOne⟩

/-- Operator Zorn involution (adjoint) -/
def opZornStar (X : OpZorn H) : OpZorn H where
  a := ContinuousLinearMap.adjoint X.a
  u := fun i => ContinuousLinearMap.adjoint (X.u i)
  v := fun i => ContinuousLinearMap.adjoint (X.v i)
  b := ContinuousLinearMap.adjoint X.b

/-- The star operation is an involution -/
theorem opZornStar_involutive (X : OpZorn H) : opZornStar (opZornStar X) = X := by
  ext <;> simp [opZornStar]

/-!
=============================================================================
PART 2: Operator Derivations
=============================================================================
-/

/-- A derivation on the operator-valued Zorn algebra -/
structure OpDerivation (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  toLinearMap : OpZorn H →ₗ[ℂ] OpZorn H
  leibniz : ∀ (X Y : OpZorn H), toLinearMap (X * Y) = toLinearMap X * Y + X * toLinearMap Y

/-- Derivation commutes with star condition -/
def derivationCommutesStar (D : OpDerivation H) : Prop :=
  ∀ X : OpZorn H, D.toLinearMap (opZornStar X) = opZornStar (D.toLinearMap X)

end InfoGeometry.Canonical.OperatorCoefficientZornExtension