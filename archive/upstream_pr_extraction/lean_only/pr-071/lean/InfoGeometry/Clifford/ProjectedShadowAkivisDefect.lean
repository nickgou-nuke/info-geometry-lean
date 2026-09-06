import InfoGeometry.Algebra.ChiralOperatorSymbolProjection

/-!
# Akivis identity for a projected associative shadow

The shadow carrier has no multiplication instance: its product is explicitly
the readout of an ambient associative product.  The theorem below therefore
uses only the definitions of commutator and associator, and makes no
alternativity or Malcev claim.
-/

namespace InfoGeometry.Clifford.ProjectedShadowAkivisDefect

open InfoGeometry.Algebra

variable {R Z E : Type*} [CommRing R]
  [AddCommGroup Z] [Module R Z]
  [Ring E] [Algebra R E]

def shadowMul (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) (x y : Z) : Z :=
  projectedOperatorMul ι σ x y

def shadowCommutator (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) (x y : Z) : Z :=
  shadowMul ι σ x y - shadowMul ι σ y x

def shadowAssociator (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z)
    (x y z : Z) : Z :=
  shadowMul ι σ (shadowMul ι σ x y) z -
    shadowMul ι σ x (shadowMul ι σ y z)

def shadowJacobiator (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z)
    (x y z : Z) : Z :=
  shadowCommutator ι σ (shadowCommutator ι σ x y) z +
    (shadowCommutator ι σ (shadowCommutator ι σ y z) x +
      shadowCommutator ι σ (shadowCommutator ι σ z x) y)

theorem shadow_akivis_identity
    (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) (x y z : Z) :
    shadowJacobiator ι σ x y z =
      (shadowAssociator ι σ x y z +
          shadowAssociator ι σ y z x +
          shadowAssociator ι σ z x y) -
        (shadowAssociator ι σ y x z +
          shadowAssociator ι σ x z y +
          shadowAssociator ι σ z y x) := by
  simp [shadowJacobiator, shadowCommutator, shadowAssociator,
    shadowMul, projectedOperatorMul, sub_eq_add_neg, mul_add, add_mul]
  abel_nf

theorem shadow_associator_eq_leakage
    (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) (x y z : Z) :
    shadowAssociator ι σ x y z =
      σ (ι x * symbolDefect ι σ (ι y * ι z) -
        symbolDefect ι σ (ι x * ι y) * ι z) := by
  exact projectedOperatorAssociator_eq_defect ι σ x y z

end InfoGeometry.Clifford.ProjectedShadowAkivisDefect
