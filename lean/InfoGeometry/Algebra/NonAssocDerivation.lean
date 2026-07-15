import Mathlib.Algebra.Lie.OfAssociative

/-!
# Derivations of nonassociative algebras

For an `R`-module with an `R`-bilinear, possibly nonassociative multiplication, the linear
endomorphisms satisfying the Leibniz rule form a Lie subalgebra of `Module.End R A`. The bracket is
the endomorphism commutator inherited from Mathlib.
-/

namespace InfoGeometry.Algebra.NonAssocDerivation

variable (R A : Type*) [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The Leibniz property for a linear endomorphism of a possibly nonassociative algebra. -/
def IsLeibniz (D : Module.End R A) : Prop :=
  ∀ x y : A, D (x * y) = D x * y + x * D y

/-- Leibniz endomorphisms form a Lie subalgebra of the endomorphism Lie algebra. -/
def derivations : LieSubalgebra R (Module.End R A) where
  carrier := {D | IsLeibniz R A D}
  zero_mem' := by
    intro x y
    simp
  add_mem' := by
    intro D E hD hE x y
    simp only [LinearMap.add_apply]
    rw [hD x y, hE x y]
    simp only [add_mul, mul_add]
    abel
  smul_mem' := by
    intro r D hD x y
    simp only [LinearMap.smul_apply]
    rw [hD x y, smul_add, smul_mul_assoc, mul_smul_comm]
  lie_mem' := by
    intro D E hD hE x y
    simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply]
    rw [hE x y, map_add, hD (E x) y, hD x (E y)]
    rw [hD x y, map_add, hE (D x) y, hE x (D y)]
    simp only [sub_mul, mul_sub]
    abel

/-- A bundled nonassociative derivation satisfies the Leibniz rule. -/
@[simp]
theorem leibniz (D : derivations R A) (x y : A) :
    (D : Module.End R A) (x * y) =
      (D : Module.End R A) x * y + x * (D : Module.End R A) y :=
  D.property x y

/-- The inherited Lie bracket is the pointwise commutator of endomorphisms. -/
@[simp]
theorem lie_apply (D E : derivations R A) (x : A) :
    ((⁅D, E⁆ : derivations R A) : Module.End R A) x =
      (D : Module.End R A) ((E : Module.End R A) x) -
        (E : Module.End R A) ((D : Module.End R A) x) :=
  rfl

/-- Closure under commutator, exposed on the ambient endomorphism carrier. -/
theorem commutator_mem (D E : derivations R A) :
    ⁅(D : Module.End R A), (E : Module.End R A)⁆ ∈ derivations R A :=
  LieSubalgebra.lie_mem _ D.property E.property

section Quadratic

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- Polarization of a quadratic `U`-operator in its outer variables. -/
def polarizedU (U : A → A → A) (X Y Z : A) : A :=
  U (X + Z) Y - U X Y - U Z Y

/-- The quadratic Leibniz rule for an endomorphism relative to a `U`-operator. -/
def IsQuadraticDerivation (U : A → A → A) (D : Module.End R A) : Prop :=
  ∀ X Y : A,
    D (U X Y) = polarizedU U (D X) Y X + U X (D Y)

/-- A quadratic derivation acts slotwise on the polarized triple product. -/
theorem map_polarizedU
    (U : A → A → A) (D : Module.End R A)
    (hD : IsQuadraticDerivation U D)
    (haddLeft : ∀ X₁ X₂ Y Z : A,
      polarizedU U (X₁ + X₂) Y Z = polarizedU U X₁ Y Z + polarizedU U X₂ Y Z)
    (haddRight : ∀ X Y Z₁ Z₂ : A,
      polarizedU U X Y (Z₁ + Z₂) = polarizedU U X Y Z₁ + polarizedU U X Y Z₂)
    (houter : ∀ X Y Z : A, polarizedU U X Y Z = polarizedU U Z Y X)
    (X Y Z : A) :
    D (polarizedU U X Y Z) =
      polarizedU U (D X) Y Z + polarizedU U X (D Y) Z + polarizedU U X Y (D Z) := by
  calc
    D (polarizedU U X Y Z) =
        (polarizedU U (D (X + Z)) Y (X + Z) + U (X + Z) (D Y)) -
          (polarizedU U (D X) Y X + U X (D Y)) -
            (polarizedU U (D Z) Y Z + U Z (D Y)) := by
      rw [polarizedU, map_sub, map_sub, hD, hD, hD]
    _ = polarizedU U (D X) Y Z + polarizedU U (D Z) Y X +
          polarizedU U X (D Y) Z := by
      rw [map_add, haddLeft, haddRight, haddRight]
      unfold polarizedU
      abel
    _ = polarizedU U (D X) Y Z + polarizedU U X (D Y) Z +
          polarizedU U X Y (D Z) := by
      rw [houter (D Z) Y X]
      abel

end Quadratic

end InfoGeometry.Algebra.NonAssocDerivation
