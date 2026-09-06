import Mathlib
import Mathlib.Algebra.Lie.Basic

set_option autoImplicit false
universe u

namespace InfoGeometry.Algebra.HessianThermodynamicManifold

class JordanAlgebra (V : Type u) [AddCommGroup V] (R : Type u) [CommRing R] where
  mul : V → V → V
  comm : ∀ x y, mul x y = mul y x
  jordan_id : ∀ x y, mul x (mul (mul x x) y) = mul (mul x x) (mul x y)

instance {R : Type u} [CommRing R] : JordanAlgebra R R where
  mul := fun x y => x * y
  comm := mul_comm
  jordan_id := fun x y => by ring

class InnerSpace (V : Type u) [AddCommGroup V] (R : Type u) [CommRing R] where
  inner : V → V → R
  inner_zero_right : ∀ x, inner x 0 = 0

instance {R : Type u} [CommRing R] : InnerSpace R R where
  inner := fun x y => x * y
  inner_zero_right := fun x => mul_zero x

def bregman_divergence {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R]
  [InnerSpace V R] (ψ : V → R) (grad_ψ : V → V) (x y : V) : R :=
  ψ x - ψ y - InnerSpace.inner (grad_ψ y) (x - y)

theorem bregman_self_divergence_zero {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R]
  [InnerSpace V R] (ψ : V → R) (grad_ψ : V → V) (x : V) :
  bregman_divergence ψ grad_ψ x x = 0 := by
  unfold bregman_divergence
  have h_sub : x - x = 0 := sub_self x
  rw [h_sub]
  have h_inner : InnerSpace.inner (grad_ψ x) (0 : V) = (0 : R) := InnerSpace.inner_zero_right (grad_ψ x)
  rw [h_inner]
  ring

theorem jordan_local_comm {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R]
  [JordanAlgebra V R] (x y : V) :
  JordanAlgebra.mul (R := R) x y = JordanAlgebra.mul (R := R) y x :=
  JordanAlgebra.comm x y

class StrictlyConvexPotential {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [InnerSpace V R] (ψ : V → R) (grad_ψ : V → V) where
  first_order_cond : ∀ x y, x ≠ y → ψ x > ψ y + InnerSpace.inner (grad_ψ y) (x - y)

theorem bregman_divergence_pos {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [InnerSpace V R] (ψ : V → R) (grad_ψ : V → V)
  [StrictlyConvexPotential ψ grad_ψ] (x y : V) (h : x ≠ y) :
  bregman_divergence ψ grad_ψ x y > 0 := by
  unfold bregman_divergence
  have h_convex := StrictlyConvexPotential.first_order_cond (ψ := ψ) (grad_ψ := grad_ψ) x y h
  linarith

structure KKT_Nilpotent_Boundary {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R]
  [JordanAlgebra V R] (N : V) where
  is_boundary : JordanAlgebra.mul (R := R) N N = 0

instance {R : Type u} [CommRing R] : Inhabited (KKT_Nilpotent_Boundary (V := R) (R := R) 0) where
  default := { is_boundary := by simp [JordanAlgebra.mul] }

theorem TKK_Lift_Existence {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R] [Invertible (2 : R)]
  [JordanAlgebra V R] :
  ∃ (L : Type u) (_addL : AddCommGroup L) (_lieRing : LieRing L) (_lieAlg : LieAlgebra R L)
    (emb : V → L), Function.Injective emb := sorry

def is_square {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R] [JordanAlgebra V R] (x : V) : Prop :=
  ∃ y : V, x = JordanAlgebra.mul (R := R) y y

theorem Koecher_Vinberg_SelfDual {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R] [LinearOrder R]
  [JordanAlgebra V R] [InnerSpace V R] (y : V) :
  (∀ x : V, is_square x → InnerSpace.inner x y ≥ 0) ↔ is_square y := sorry

structure FenchelDualPair {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R] [LinearOrder R]
  [InnerSpace V R] (ψ : V → R) (ψ_star : V → R) (grad_ψ : V → V) where
  fenchel_young : ∀ x y, ψ x + ψ_star y ≥ InnerSpace.inner y x
  legendre_identity : ∀ x, ψ x + ψ_star (grad_ψ x) = InnerSpace.inner (grad_ψ x) x

theorem bregman_eq_fenchel_young_loss {V : Type u} [AddCommGroup V] {R : Type u} [CommRing R] [LinearOrder R]
  [InnerSpace V R] (ψ : V → R) (ψ_star : V → R) (grad_ψ : V → V) (pair : FenchelDualPair ψ ψ_star grad_ψ)
  (x y : V) (inner_sub_right : ∀ (u : V) (v : V) (w : V), InnerSpace.inner (R := R) u (v - w) = InnerSpace.inner (R := R) u v - InnerSpace.inner (R := R) u w) :
  bregman_divergence ψ grad_ψ x y = ψ x + ψ_star (grad_ψ y) - InnerSpace.inner (grad_ψ y) x := by
  unfold bregman_divergence
  rw [inner_sub_right]
  have h_legendre := pair.legendre_identity y
  rw [← h_legendre]
  ring

end InfoGeometry.Algebra.HessianThermodynamicManifold
