import Mathlib

/-!
# Represented inverse twists and associative products

Meier--Viana, arXiv:2601.19983v1, (3.1)--(3.5).
The data are the two- and three-tensor actions of an inverse twist. Naturality
with multiplication and the inverse cocycle are explicit hypotheses; associativity
of the deformed product is a conclusion, not a structure field. This file does
not construct a universal-enveloping-algebra action or a formal-series completion.
-/
noncomputable section
namespace InfoGeometry.QuantumAlgebra.RepresentedTwist
open scoped TensorProduct
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

abbrev multiply : A ⊗[R] A →ₗ[R] A := LinearMap.mul' R A

def contractLeft : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] A :=
  TensorProduct.map (multiply (R := R) (A := A)) (LinearMap.id : A →ₗ[R] A)

def contractRight : A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] A :=
  TensorProduct.map (LinearMap.id : A →ₗ[R] A) (multiply (R := R) (A := A))

theorem contract_associativity (t : A ⊗[R] (A ⊗[R] A)) :
    multiply (contractLeft ((TensorProduct.assoc R A A A).symm t)) =
      multiply (contractRight t) := by
  have h : (multiply (R := R) (A := A)).comp
      ((contractLeft (R := R) (A := A)).comp (TensorProduct.assoc R A A A).symm.toLinearMap) =
      (multiply (R := R) (A := A)).comp (contractRight (R := R) (A := A)) := by
    ext a b c
    simp [contractLeft, contractRight, mul_assoc]
  exact LinearMap.congr_fun h t

/-- Represented module-algebra naturality and inverse-cocycle equations. -/
structure InverseTwist where
  two : A ⊗[R] A ≃ₗ[R] A ⊗[R] A
  leftThree : (A ⊗[R] A) ⊗[R] A →ₗ[R] (A ⊗[R] A) ⊗[R] A
  rightThree : A ⊗[R] (A ⊗[R] A) →ₗ[R] A ⊗[R] (A ⊗[R] A)
  natural_left : ∀ (u : A ⊗[R] A) (c : A),
    two (multiply u ⊗ₜ[R] c) = contractLeft (leftThree (u ⊗ₜ[R] c))
  natural_right : ∀ (a : A) (u : A ⊗[R] A),
    two (a ⊗ₜ[R] multiply u) = contractRight (rightThree (a ⊗ₜ[R] u))
  cocycle : ∀ a b c : A,
    leftThree (two (a ⊗ₜ[R] b) ⊗ₜ[R] c) =
      (TensorProduct.assoc R A A A).symm (rightThree (a ⊗ₜ[R] two (b ⊗ₜ[R] c)))
  normal_left : ∀ a : A, two (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] a
  normal_right : ∀ a : A, two (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1

namespace InverseTwist
variable (F : InverseTwist (R := R) (A := A))

def product (a b : A) : A := multiply (F.two (a ⊗ₜ[R] b))

theorem product_assoc (a b c : A) : F.product (F.product a b) c = F.product a (F.product b c) := by
  unfold product
  rw [F.natural_left, F.natural_right, F.cocycle, contract_associativity]

@[simp] theorem product_one_left (a : A) : F.product 1 a = a := by
  simp [product, F.normal_left]

@[simp] theorem product_one_right (a : A) : F.product a 1 = a := by
  simp [product, F.normal_right]

theorem product_add_left (a b c : A) : F.product (a+b) c = F.product a c + F.product b c := by
  simp [product, TensorProduct.add_tmul]

theorem product_add_right (a b c : A) : F.product a (b+c) = F.product a b + F.product a c := by
  simp [product, TensorProduct.tmul_add]

/-- Twisting preserves a product when the represented inverse twist fixes its tensor. -/
theorem product_of_fixed_tensor (a b : A) (h : F.two (a ⊗ₜ[R] b) = a ⊗ₜ[R] b) :
    F.product a b = a*b := by simp [product, h]

/-- Conjugated flip; it is not an assumed Yang--Baxter solution. -/
def braiding : A ⊗[R] A ≃ₗ[R] A ⊗[R] A :=
  F.two.trans ((TensorProduct.comm R A A).trans F.two.symm)

theorem braiding_involutive : Function.Involutive F.braiding := by
  intro t
  simp [braiding, LinearEquiv.trans_apply]

/-- The unchanged differential remains a derivation when its tensor action commutes
with the twist. This is the degree-zero version of (3.8). -/
theorem differential_product (d : A →ₗ[R] A)
    (hd : ∀ a b, d (a*b) = d a*b+a*d b)
    (hc : ∀ t : A ⊗[R] A,
      (TensorProduct.map d LinearMap.id + TensorProduct.map LinearMap.id d) (F.two t) =
      F.two ((TensorProduct.map d LinearMap.id + TensorProduct.map LinearMap.id d) t))
    (a b : A) : d (F.product a b) = F.product (d a) b + F.product a (d b) := by
  have hm : d.comp (multiply (R := R) (A := A)) =
      (multiply (R := R) (A := A)).comp
        (TensorProduct.map d LinearMap.id + TensorProduct.map LinearMap.id d) := by
    ext x y
    simpa using hd x y
  change (d.comp multiply) (F.two (a ⊗ₜ[R] b)) = _
  rw [hm]
  simp only [LinearMap.comp_apply, hc]
  simp [product]

end InverseTwist

/-- Nonvacuous undeformed witness for the represented coherence contract. -/
def identityTwist : InverseTwist (R := R) (A := A) where
  two := LinearEquiv.refl R _
  leftThree := LinearMap.id
  rightThree := LinearMap.id
  natural_left := by intro u c; simp [contractLeft]
  natural_right := by intro a u; simp [contractRight]
  cocycle := by intro a b c; simp
  normal_left := by intro a; rfl
  normal_right := by intro a; rfl

@[simp] theorem identityTwist_product (a b : A) :
    (identityTwist (R := R) (A := A)).product a b = a*b := by simp [InverseTwist.product, identityTwist]

section Commutative
variable {B : Type*} [CommRing B] [Algebra R B]

theorem multiply_flip (t : B ⊗[R] B) :
    multiply ((TensorProduct.comm R B B) t) = multiply t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem braided_product (F : InverseTwist (R := R) (A := B)) (t : B ⊗[R] B) :
    multiply (F.two (F.braiding t)) = multiply (F.two t) := by
  simp [InverseTwist.braiding, LinearEquiv.trans_apply, multiply_flip]

end Commutative
end InfoGeometry.QuantumAlgebra.RepresentedTwist
