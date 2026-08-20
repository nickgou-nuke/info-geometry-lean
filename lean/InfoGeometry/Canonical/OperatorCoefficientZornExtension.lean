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

@[simp] theorem opZornStar_zero :
    opZornStar (0 : OpZorn H) = 0 := by
  apply OpZorn.ext
  · change ContinuousLinearMap.adjoint (0 : H →L[ℂ] H) = 0
    exact map_zero ContinuousLinearMap.adjoint
  · funext i
    change ContinuousLinearMap.adjoint (0 : H →L[ℂ] H) = 0
    exact map_zero ContinuousLinearMap.adjoint
  · funext i
    change ContinuousLinearMap.adjoint (0 : H →L[ℂ] H) = 0
    exact map_zero ContinuousLinearMap.adjoint
  · change ContinuousLinearMap.adjoint (0 : H →L[ℂ] H) = 0
    exact map_zero ContinuousLinearMap.adjoint

theorem opZornStar_add (X Y : OpZorn H) :
    opZornStar (X + Y) = opZornStar X + opZornStar Y := by
  apply OpZorn.ext
  · change ContinuousLinearMap.adjoint (X.a + Y.a) =
      ContinuousLinearMap.adjoint X.a + ContinuousLinearMap.adjoint Y.a
    exact map_add ContinuousLinearMap.adjoint X.a Y.a
  · funext i
    change ContinuousLinearMap.adjoint (X.u i + Y.u i) =
      ContinuousLinearMap.adjoint (X.u i) + ContinuousLinearMap.adjoint (Y.u i)
    exact map_add ContinuousLinearMap.adjoint (X.u i) (Y.u i)
  · funext i
    change ContinuousLinearMap.adjoint (X.v i + Y.v i) =
      ContinuousLinearMap.adjoint (X.v i) + ContinuousLinearMap.adjoint (Y.v i)
    exact map_add ContinuousLinearMap.adjoint (X.v i) (Y.v i)
  · change ContinuousLinearMap.adjoint (X.b + Y.b) =
      ContinuousLinearMap.adjoint X.b + ContinuousLinearMap.adjoint Y.b
    exact map_add ContinuousLinearMap.adjoint X.b Y.b

theorem opZornStar_sub (X Y : OpZorn H) :
    opZornStar (X - Y) = opZornStar X - opZornStar Y := by
  apply OpZorn.ext
  · change ContinuousLinearMap.adjoint (X.a - Y.a) =
      ContinuousLinearMap.adjoint X.a - ContinuousLinearMap.adjoint Y.a
    exact map_sub ContinuousLinearMap.adjoint X.a Y.a
  · funext i
    change ContinuousLinearMap.adjoint (X.u i - Y.u i) =
      ContinuousLinearMap.adjoint (X.u i) - ContinuousLinearMap.adjoint (Y.u i)
    exact map_sub ContinuousLinearMap.adjoint (X.u i) (Y.u i)
  · funext i
    change ContinuousLinearMap.adjoint (X.v i - Y.v i) =
      ContinuousLinearMap.adjoint (X.v i) - ContinuousLinearMap.adjoint (Y.v i)
    exact map_sub ContinuousLinearMap.adjoint (X.v i) (Y.v i)
  · change ContinuousLinearMap.adjoint (X.b - Y.b) =
      ContinuousLinearMap.adjoint X.b - ContinuousLinearMap.adjoint Y.b
    exact map_sub ContinuousLinearMap.adjoint X.b Y.b

theorem opZornStar_neg (X : OpZorn H) :
    opZornStar (-X) = -opZornStar X := by
  apply OpZorn.ext
  · change ContinuousLinearMap.adjoint (-X.a) = -ContinuousLinearMap.adjoint X.a
    exact map_neg ContinuousLinearMap.adjoint X.a
  · funext i
    change ContinuousLinearMap.adjoint (-(X.u i)) =
      -ContinuousLinearMap.adjoint (X.u i)
    exact map_neg ContinuousLinearMap.adjoint (X.u i)
  · funext i
    change ContinuousLinearMap.adjoint (-(X.v i)) =
      -ContinuousLinearMap.adjoint (X.v i)
    exact map_neg ContinuousLinearMap.adjoint (X.v i)
  · change ContinuousLinearMap.adjoint (-X.b) = -ContinuousLinearMap.adjoint X.b
    exact map_neg ContinuousLinearMap.adjoint X.b

@[simp] theorem op_add_a (X Y : OpZorn H) : (X + Y).a = X.a + Y.a := rfl
@[simp] theorem op_add_u (X Y : OpZorn H) (i : Fin 3) : (X + Y).u i = X.u i + Y.u i := rfl
@[simp] theorem op_add_v (X Y : OpZorn H) (i : Fin 3) : (X + Y).v i = X.v i + Y.v i := rfl
@[simp] theorem op_add_b (X Y : OpZorn H) : (X + Y).b = X.b + Y.b := rfl

@[simp] theorem op_sub_a (X Y : OpZorn H) : (X - Y).a = X.a - Y.a := rfl
@[simp] theorem op_sub_u (X Y : OpZorn H) (i : Fin 3) : (X - Y).u i = X.u i - Y.u i := rfl
@[simp] theorem op_sub_v (X Y : OpZorn H) (i : Fin 3) : (X - Y).v i = X.v i - Y.v i := rfl
@[simp] theorem op_sub_b (X Y : OpZorn H) : (X - Y).b = X.b - Y.b := rfl

@[simp] theorem op_mul_a (X Y : OpZorn H) : (X * Y).a = X.a * Y.a + opDot X.u Y.v := rfl
@[simp] theorem op_mul_u (X Y : OpZorn H) (i : Fin 3) : (X * Y).u i = X.a * Y.u i + Y.b * X.u i - (opCross X.v Y.v) i := rfl
@[simp] theorem op_mul_v (X Y : OpZorn H) (i : Fin 3) : (X * Y).v i = Y.a * X.v i + X.b * Y.v i + (opCross X.u Y.u) i := rfl
@[simp] theorem op_mul_b (X Y : OpZorn H) : (X * Y).b = X.b * Y.b + opDot X.v Y.u := rfl

/-!
=============================================================================
PART 2: Operator Derivations & Automorphisms
=============================================================================
-/

/-- A derivation on the operator-valued Zorn algebra -/
structure OpDerivation (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  toLinearMap : OpZorn H →ₗ[ℂ] OpZorn H
  leibniz : ∀ (X Y : OpZorn H), toLinearMap (X * Y) = toLinearMap X * Y + X * toLinearMap Y

/-- Derivation commutes with star condition -/
def derivationCommutesStar (D : OpDerivation H) : Prop :=
  ∀ X : OpZorn H, D.toLinearMap (opZornStar X) = opZornStar (D.toLinearMap X)

/-- A derivation commuting with the operator-Zorn involution preserves the
star-fixed (self-adjoint) subspace. -/
theorem derivation_preserves_star_fixed
    (D : OpDerivation H)
    (hstar : derivationCommutesStar D)
    (X : OpZorn H)
    (hX : opZornStar X = X) :
    opZornStar (D.toLinearMap X) = D.toLinearMap X := by
  calc
    opZornStar (D.toLinearMap X) = D.toLinearMap (opZornStar X) :=
      (hstar X).symm
    _ = D.toLinearMap X := by rw [hX]

/-- 🏆 THEOREM: Leibniz rule for lifted operator derivation -/
theorem liftDerivation_leibniz (D : OpDerivation H) (X Y : OpZorn H) :
    D.toLinearMap (X * Y) = D.toLinearMap X * Y + X * D.toLinearMap Y :=
  D.leibniz X Y

/-- Commutator of two operator derivations: [D₁, D₂] = D₁ ∘ D₂ - D₂ ∘ D₁ -/
def opDerivationCommutator (D₁ D₂ : OpDerivation H) : OpZorn H →ₗ[ℂ] OpZorn H :=
  D₁.toLinearMap.comp D₂.toLinearMap - D₂.toLinearMap.comp D₁.toLinearMap

/-- Left multiplication distributes over subtraction -/
theorem opZornMul_sub_left (X Y Z : OpZorn H) :
    X * (Y - Z) = X * Y - X * Z := by
  apply OpZorn.ext
  · simp only [op_mul_a, op_sub_a, op_sub_v, opDot, mul_sub]
    noncomm_ring
  · ext i; fin_cases i <;>
      simp only [op_mul_u, op_sub_u, op_sub_v, op_sub_b, opCross, mul_sub, sub_mul] <;>
      noncomm_ring
  · ext i; fin_cases i <;>
      simp only [op_mul_v, op_sub_a, op_sub_u, op_sub_v, opCross, mul_sub, sub_mul] <;>
      noncomm_ring
  · simp only [op_mul_b, op_sub_b, op_sub_u, opDot, mul_sub]
    noncomm_ring

/-- Right multiplication distributes over subtraction -/
theorem opZornMul_sub_right (X Y Z : OpZorn H) :
    (X - Y) * Z = X * Z - Y * Z := by
  apply OpZorn.ext
  · simp only [op_mul_a, op_sub_a, op_sub_u, opDot, sub_mul]
    noncomm_ring
  · ext i; fin_cases i <;>
      simp only [op_mul_u, op_sub_a, op_sub_u, op_sub_v, opCross, mul_sub, sub_mul] <;>
      noncomm_ring
  · ext i; fin_cases i <;>
      simp only [op_mul_v, op_sub_u, op_sub_v, op_sub_b, opCross, mul_sub, sub_mul] <;>
      noncomm_ring
  · simp only [op_mul_b, op_sub_b, op_sub_v, opDot, sub_mul]
    noncomm_ring

/-- 🏆 THEOREM: Commutator of derivations satisfies the derivation Leibniz identity -/
theorem liftDerivation_commutator (D₁ D₂ : OpDerivation H) (X Y : OpZorn H) :
    opDerivationCommutator D₁ D₂ (X * Y) =
      opDerivationCommutator D₁ D₂ X * Y + X * opDerivationCommutator D₁ D₂ Y := by
  dsimp [opDerivationCommutator, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [D₂.leibniz X Y, map_add, D₁.leibniz, D₁.leibniz]
  rw [D₁.leibniz X Y, map_add, D₂.leibniz, D₂.leibniz]
  rw [opZornMul_sub_right, opZornMul_sub_left]
  abel

theorem derivationCommutesStar_commutator
    (D₁ D₂ : OpDerivation H)
    (h₁ : derivationCommutesStar D₁)
    (h₂ : derivationCommutesStar D₂)
    (X : OpZorn H) :
    opDerivationCommutator D₁ D₂ (opZornStar X) =
      opZornStar (opDerivationCommutator D₁ D₂ X) := by
  dsimp [opDerivationCommutator]
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    h₂ X, h₁ (D₂.toLinearMap X), h₂ X,
    h₁ (D₁.toLinearMap X)]
  exact (opZornStar_sub
    (D₁.toLinearMap (D₂.toLinearMap X))
    (D₂.toLinearMap (D₁.toLinearMap X))).symm

/-- An automorphism of the operator-valued Zorn algebra -/
structure OpAutomorphism (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  toLinearEquiv : OpZorn H ≃ₗ[ℂ] OpZorn H
  map_mul' : ∀ (X Y : OpZorn H), toLinearEquiv (X * Y) = toLinearEquiv X * toLinearEquiv Y

/-- 🏆 THEOREM: Lifted automorphism preserves the operator Zorn multiplication -/
theorem liftAutomorphism_mul (Φ : OpAutomorphism H) (X Y : OpZorn H) :
    Φ.toLinearEquiv (X * Y) = Φ.toLinearEquiv X * Φ.toLinearEquiv Y :=
  Φ.map_mul' X Y

end InfoGeometry.Canonical.OperatorCoefficientZornExtension
