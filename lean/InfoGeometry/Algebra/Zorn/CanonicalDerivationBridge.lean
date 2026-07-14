import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Canonical and Kingdon realization of the Zorn derivation Lie algebra

This file transports the native `ZornVectorMatrix.Derivation` Lie algebra through
checked carrier equivalences.  Its images in the canonical-Zorn and AbstractKingdon
endomorphism algebras consist of genuine Leibniz derivations and inherit the
commutator bracket through injective Lie equivalences.

No dimension or split-`G₂` classification claim is made here.
-/

namespace CanonicalDerivationBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.KingdonSplitOctonion
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev VectorDerivation := ZornVectorMatrix.Derivation (R := ℝ)
abbrev CanonicalEnd := Module.End ℝ CZ
abbrev Kingdon := AbstractKingdon
abbrev KingdonEnd := Module.End ℝ Kingdon

@[simp] theorem zMul_eq_canonical_mul (X Y : CZ) : zMul X Y = X * Y := rfl

/-- Conjugate a native Zorn-vector-matrix derivation onto the canonical Zorn carrier. -/
noncomputable def toCanonicalEnd (D : VectorDerivation) : CanonicalEnd where
  toFun X := canonicalVectorEquiv.symm (D (canonicalVectorEquiv X))
  map_add' X Y := by
    rw [canonicalVectorEquiv_add, ZornVectorMatrix.Derivation.map_add]
    exact canonicalVectorEquiv_symm_add _ _
  map_smul' r X := by
    rw [canonicalVectorEquiv_smul, ZornVectorMatrix.Derivation.map_smul]
    exact canonicalVectorEquiv_symm_smul _ _

@[simp] theorem toCanonicalEnd_apply (D : VectorDerivation) (X : CZ) :
    toCanonicalEnd D X = canonicalVectorEquiv.symm (D (canonicalVectorEquiv X)) := rfl

/-- The transported canonical endomorphism satisfies the nonassociative Leibniz law. -/
@[simp] theorem toCanonicalEnd_leibniz (D : VectorDerivation) (X Y : CZ) :
    toCanonicalEnd D (X * Y) = toCanonicalEnd D X * Y + X * toCanonicalEnd D Y := by
  apply canonicalVectorEquiv.injective
  simp only [toCanonicalEnd_apply, Equiv.apply_symm_apply, canonicalVectorEquiv_mul,
    canonicalVectorEquiv_add, ZornVectorMatrix.Derivation.map_mul]

/-- Transport of native derivations as a real-linear map into canonical endomorphisms. -/
noncomputable def canonicalDerivationLinearMap : VectorDerivation →ₗ[ℝ] CanonicalEnd where
  toFun := toCanonicalEnd
  map_add' D E := by
    apply LinearMap.ext
    intro X
    apply canonicalVectorEquiv.injective
    change (D + E) (canonicalVectorEquiv X) = ZornVectorMatrix.add
      (D (canonicalVectorEquiv X)) (E (canonicalVectorEquiv X))
    exact ZornVectorMatrix.Derivation.add_apply D E _
  map_smul' r D := by
    apply LinearMap.ext
    intro X
    apply canonicalVectorEquiv.injective
    change (r • D) (canonicalVectorEquiv X) =
      ZornVectorMatrix.smul r (D (canonicalVectorEquiv X))
    exact ZornVectorMatrix.Derivation.smul_apply r D _

@[simp] theorem canonicalDerivationLinearMap_apply (D : VectorDerivation) (X : CZ) :
    canonicalDerivationLinearMap D X = toCanonicalEnd D X := rfl

theorem canonicalDerivationLinearMap_injective :
    Function.Injective canonicalDerivationLinearMap := by
  intro D E h
  apply ZornVectorMatrix.Derivation.ext
  intro X
  have hX := LinearMap.congr_fun h (canonicalVectorEquiv.symm X)
  exact canonicalVectorEquiv.symm.injective (by simpa [toCanonicalEnd] using hX)

/-- Transport identifies the native derivation bracket with the endomorphism commutator. -/
theorem toCanonicalEnd_bracket (D E : VectorDerivation) :
    toCanonicalEnd (ZornVectorMatrix.Derivation.bracket D E) =
      toCanonicalEnd D * toCanonicalEnd E - toCanonicalEnd E * toCanonicalEnd D := by
  apply LinearMap.ext
  intro X
  apply canonicalVectorEquiv.injective
  simp only [toCanonicalEnd_apply, ZornVectorMatrix.Derivation.bracket_apply,
    Equiv.apply_symm_apply, LinearMap.sub_apply, Module.End.mul_apply,
    canonicalVectorEquiv_sub]

/-- Native Zorn derivations represented in the canonical endomorphism Lie algebra. -/
noncomputable def canonicalDerivationLieHom : VectorDerivation →ₗ⁅ℝ⁆ CanonicalEnd where
  toLinearMap := canonicalDerivationLinearMap
  map_lie' := by
    intro D E
    change toCanonicalEnd (ZornVectorMatrix.Derivation.bracket D E) =
      ⁅toCanonicalEnd D, toCanonicalEnd E⁆
    simpa only [LieRing.of_associative_ring_bracket] using toCanonicalEnd_bracket D E

/-- The canonical real-Zorn derivation Lie algebra as the exact transported image. -/
noncomputable def canonicalDerivationLieAlgebra : LieSubalgebra ℝ CanonicalEnd :=
  canonicalDerivationLieHom.range

theorem canonicalDerivationLieHom_injective :
    Function.Injective canonicalDerivationLieHom := by
  intro D E h
  exact canonicalDerivationLinearMap_injective h

/-- Lie equivalence from the native owner to its canonical-Zorn realization. -/
noncomputable def canonicalDerivationLieEquiv :
    VectorDerivation ≃ₗ⁅ℝ⁆ canonicalDerivationLieAlgebra :=
  canonicalDerivationLieHom.equivRangeOfInjective canonicalDerivationLieHom_injective

@[simp] theorem canonicalDerivationLieEquiv_apply (D : VectorDerivation) :
    (canonicalDerivationLieEquiv D : CanonicalEnd) = toCanonicalEnd D := by
  rfl

/-- Conjugate a native Zorn derivation through the canonical realization of AbstractKingdon. -/
noncomputable def toKingdonEnd (D : VectorDerivation) : KingdonEnd where
  toFun x := kingdonCanonicalLinearEquiv.symm
    (toCanonicalEnd D (kingdonCanonicalLinearEquiv x))
  map_add' x y := by
    apply kingdonCanonicalLinearEquiv.injective
    simp only [LinearEquiv.apply_symm_apply, LinearEquiv.map_add, LinearMap.map_add]
  map_smul' r x := by
    apply kingdonCanonicalLinearEquiv.injective
    simp only [LinearEquiv.apply_symm_apply, LinearEquiv.map_smul, LinearMap.map_smul,
      RingHom.id_apply]

@[simp] theorem toKingdonEnd_apply (D : VectorDerivation) (x : Kingdon) :
    toKingdonEnd D x = kingdonCanonicalLinearEquiv.symm
      (toCanonicalEnd D (kingdonCanonicalLinearEquiv x)) := rfl

/-- The transported AbstractKingdon endomorphism satisfies the Leibniz law. -/
@[simp] theorem toKingdonEnd_leibniz (D : VectorDerivation) (x y : Kingdon) :
    toKingdonEnd D (x * y) = toKingdonEnd D x * y + x * toKingdonEnd D y := by
  apply kingdonCanonicalLinearEquiv.injective
  simp only [toKingdonEnd_apply, LinearEquiv.apply_symm_apply, LinearEquiv.map_add,
    kingdonCanonicalLinearEquiv_mul, zMul_eq_canonical_mul, toCanonicalEnd_leibniz]

/-- Transport of native derivations as a real-linear map into Kingdon endomorphisms. -/
noncomputable def kingdonDerivationLinearMap : VectorDerivation →ₗ[ℝ] KingdonEnd where
  toFun := toKingdonEnd
  map_add' D E := by
    apply LinearMap.ext
    intro x
    apply kingdonCanonicalLinearEquiv.injective
    simpa only [toKingdonEnd_apply, LinearEquiv.apply_symm_apply, LinearEquiv.map_add,
      LinearMap.add_apply] using
      LinearMap.congr_fun (canonicalDerivationLinearMap.map_add D E)
        (kingdonCanonicalLinearEquiv x)
  map_smul' r D := by
    apply LinearMap.ext
    intro x
    apply kingdonCanonicalLinearEquiv.injective
    simpa only [toKingdonEnd_apply, LinearEquiv.apply_symm_apply, LinearEquiv.map_smul,
      LinearMap.smul_apply, RingHom.id_apply] using
      LinearMap.congr_fun (canonicalDerivationLinearMap.map_smul r D)
        (kingdonCanonicalLinearEquiv x)

@[simp] theorem kingdonDerivationLinearMap_apply (D : VectorDerivation) (x : Kingdon) :
    kingdonDerivationLinearMap D x = toKingdonEnd D x := rfl

theorem kingdonDerivationLinearMap_injective :
    Function.Injective kingdonDerivationLinearMap := by
  intro D E h
  apply canonicalDerivationLinearMap_injective
  apply LinearMap.ext
  intro X
  let x := kingdonCanonicalLinearEquiv.symm X
  have hx := LinearMap.congr_fun h x
  exact kingdonCanonicalLinearEquiv.symm.injective (by simpa [x, toKingdonEnd] using hx)

/-- Kingdon transport also identifies the native bracket with the endomorphism commutator. -/
theorem toKingdonEnd_bracket (D E : VectorDerivation) :
    toKingdonEnd (ZornVectorMatrix.Derivation.bracket D E) =
      toKingdonEnd D * toKingdonEnd E - toKingdonEnd E * toKingdonEnd D := by
  apply LinearMap.ext
  intro x
  apply kingdonCanonicalLinearEquiv.injective
  simp only [toKingdonEnd_apply, LinearEquiv.apply_symm_apply, map_sub,
    LinearMap.sub_apply, Module.End.mul_apply]
  exact LinearMap.congr_fun (toCanonicalEnd_bracket D E) (kingdonCanonicalLinearEquiv x)

/-- Native Zorn derivations represented in the AbstractKingdon endomorphism Lie algebra. -/
noncomputable def kingdonDerivationLieHom : VectorDerivation →ₗ⁅ℝ⁆ KingdonEnd where
  toLinearMap := kingdonDerivationLinearMap
  map_lie' := by
    intro D E
    change toKingdonEnd (ZornVectorMatrix.Derivation.bracket D E) =
      ⁅toKingdonEnd D, toKingdonEnd E⁆
    simpa only [LieRing.of_associative_ring_bracket] using toKingdonEnd_bracket D E

/-- The Kingdon derivation Lie algebra as the exact transported image. -/
noncomputable def kingdonDerivationLieAlgebra : LieSubalgebra ℝ KingdonEnd :=
  kingdonDerivationLieHom.range

theorem kingdonDerivationLieHom_injective :
    Function.Injective kingdonDerivationLieHom := by
  intro D E h
  exact kingdonDerivationLinearMap_injective h

/-- Lie equivalence from the native owner to its AbstractKingdon realization. -/
noncomputable def kingdonDerivationLieEquiv :
    VectorDerivation ≃ₗ⁅ℝ⁆ kingdonDerivationLieAlgebra :=
  kingdonDerivationLieHom.equivRangeOfInjective kingdonDerivationLieHom_injective

@[simp] theorem kingdonDerivationLieEquiv_apply (D : VectorDerivation) :
    (kingdonDerivationLieEquiv D : KingdonEnd) = toKingdonEnd D := by
  rfl

end CanonicalDerivationBridge
