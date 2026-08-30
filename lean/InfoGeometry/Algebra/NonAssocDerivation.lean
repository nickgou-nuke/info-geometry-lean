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

/-- A bundled element of `derivations` satisfies the Leibniz rule.

The name is intentionally qualified by `derivations_`: the older
`AlternativeDerivations` file already owns
`InfoGeometry.Algebra.NonAssocDerivation.leibniz` for its bundled
`NonAssocDerivation` structure.  Keeping this theorem under a distinct name
lets both owner files be imported by the algebra barrel without either theorem
shadowing or deleting the other. -/
@[simp]
theorem derivations_leibniz (D : derivations R A) (x y : A) :
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

section Transport

variable {B : Type*} [NonUnitalNonAssocRing B] [Module R B]
  [IsScalarTower R B B] [SMulCommClass R B B]

/-- Conjugation transports a non-associative Leibniz derivation across a
linear equivalence which preserves multiplication. -/
def transport (e : A ≃ₗ[R] B) (D : Module.End R A) : Module.End R B :=
  e.toLinearMap.comp (D.comp e.symm.toLinearMap)

theorem transport_mem (e : A ≃ₗ[R] B)
    (hmul : ∀ x y : A, e (x * y) = e x * e y)
    {D : Module.End R A} (hD : D ∈ derivations R A) :
    transport R A e D ∈ derivations R B := by
  have hsymm : ∀ x y : B, e.symm (x * y) = e.symm x * e.symm y := by
    intro x y
    apply e.injective
    rw [e.apply_symm_apply, hmul, e.apply_symm_apply, e.apply_symm_apply]
  change ∀ x y : B, transport R A e D (x * y) =
    transport R A e D x * y + x * transport R A e D y
  intro x y
  dsimp [transport]
  rw [hsymm, hD (e.symm x) (e.symm y), map_add, hmul, hmul,
    e.apply_symm_apply, e.apply_symm_apply]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
@[simp] theorem transport_refl (D : Module.End R A) :
    transport R A (LinearEquiv.refl R A) D = D := by
  ext x
  rfl

omit [IsScalarTower R A A] [SMulCommClass R A A]
  [IsScalarTower R B B] [SMulCommClass R B B] in
/-- Conjugation transports the endomorphism commutator. -/
theorem transport_commutator (e : A ≃ₗ[R] B)
    (D E : Module.End R A) :
    transport R A e (D * E - E * D) =
      transport R A e D * transport R A e E -
        transport R A e E * transport R A e D := by
  apply LinearMap.ext
  intro x
  simp [transport, Module.End.mul_apply, LinearMap.sub_apply]

omit [IsScalarTower R A A] [SMulCommClass R A A]
  [IsScalarTower R B B] [SMulCommClass R B B] in
theorem transport_symm (e : A ≃ₗ[R] B) (D : Module.End R A) :
    transport R B e.symm (transport R A e D) = D := by
  ext x
  simp [transport]

/-! The preceding two lemmas package as a Lie hom on derivation carriers. -/
noncomputable def transportLieHom (e : A ≃ₗ[R] B)
    (hmul : ∀ x y : A, e (x * y) = e x * e y) :
    derivations R A →ₗ⁅R⁆ derivations R B where
  toFun D := ⟨transport R A e D, transport_mem R A e hmul D.property⟩
  map_add' D E := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    simp [transport]
  map_smul' r D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    simp [transport]
  map_lie' := by
    intro D E
    apply Subtype.ext
    change transport R A e ((D : Module.End R A) * (E : Module.End R A) -
      (E : Module.End R A) * (D : Module.End R A)) = _
    exact transport_commutator R A e (D : Module.End R A) (E : Module.End R A)

noncomputable def transportLieEquiv (e : A ≃ₗ[R] B)
    (hmul : ∀ x y : A, e (x * y) = e x * e y) :
    derivations R A ≃ₗ⁅R⁆ derivations R B := by
  let hsymm : ∀ x y : B, e.symm (x * y) = e.symm x * e.symm y := by
    intro x y
    apply e.injective
    rw [e.apply_symm_apply, hmul, e.apply_symm_apply, e.apply_symm_apply]
  let f := transportLieHom R A e hmul
  apply LieEquiv.ofBijective f
  constructor
  · intro D E h
    apply Subtype.ext
    have h' := congrArg (fun T : derivations R B =>
      transportLieHom R B e.symm hsymm T) h
    dsimp [f, transportLieHom] at h'
    have h'' := congrArg Subtype.val h'
    change transport R B e.symm (transport R A e (D : Module.End R A)) =
      transport R B e.symm (transport R A e (E : Module.End R A)) at h''
    rw [transport_symm, transport_symm] at h''
    exact h''
  · intro D
    refine ⟨transportLieHom R B e.symm hsymm D, ?_⟩
    apply Subtype.ext
    change transport R A e (transport R B e.symm (D : Module.End R B)) =
      (D : Module.End R B)
    exact transport_symm R B e.symm D



end Transport

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
