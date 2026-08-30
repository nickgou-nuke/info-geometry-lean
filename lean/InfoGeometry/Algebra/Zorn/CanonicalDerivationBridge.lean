import InfoGeometry.Algebra.KingdonSplitOctonion
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Algebra.NonAssocDerivation
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra

set_option synthInstance.maxHeartbeats 100000

/-!
# Canonical and Kingdon realization of the Zorn derivation Lie algebra

This file transports the native `ZornVectorMatrix.Derivation` Lie algebra through
checked carrier equivalences.  Its images in the canonical-Zorn and AbstractKingdon
endomorphism algebras consist of genuine Leibniz derivations and inherit the
commutator bracket through injective Lie equivalences.

No dimension or split-`G₂` classification claim is made here.
-/

namespace InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev VectorDerivation := ZornVectorMatrix.Derivation (R := ℝ)
abbrev CanonicalEnd := Module.End ℝ CZ
/- The transported carrier is the native AbstractKingdon owner; the bridge
   keeps that type explicit instead of introducing a second carrier alias. -/

@[simp] theorem zMul_eq_canonical_mul (X Y : CZ) : zMul X Y = X * Y := rfl

noncomputable def canonicalVectorLinearEquiv : CZ ≃ₗ[ℝ] VZ where
  toFun := canonicalVectorEquiv
  invFun := canonicalVectorEquiv.symm
  left_inv := canonicalVectorEquiv.left_inv
  right_inv := canonicalVectorEquiv.right_inv
  map_add' := canonicalVectorEquiv_add
  map_smul' := canonicalVectorEquiv_smul

/-- Conjugate a native Zorn-vector-matrix derivation onto the canonical Zorn carrier. -/
noncomputable def toCanonicalEnd (D : VectorDerivation) : CanonicalEnd :=
  NonAssocDerivation.transport ℝ VZ canonicalVectorLinearEquiv.symm
    (toNonAssocDerivation D)

@[simp] theorem toCanonicalEnd_apply (D : VectorDerivation) (X : CZ) :
    toCanonicalEnd D X = canonicalVectorLinearEquiv.symm (D (canonicalVectorLinearEquiv X)) := by
  rfl

/-- The transported canonical endomorphism satisfies the nonassociative Leibniz law. -/
@[simp] theorem toCanonicalEnd_leibniz (D : VectorDerivation) (X Y : CZ) :
    toCanonicalEnd D (X * Y) = toCanonicalEnd D X * Y + X * toCanonicalEnd D Y := by
  apply canonicalVectorLinearEquiv.injective
  change D (canonicalVectorEquiv (X * Y)) =
    canonicalVectorEquiv (toCanonicalEnd D X * Y + X * toCanonicalEnd D Y)
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_add,
    toCanonicalEnd_apply, Equiv.apply_symm_apply]
  exact ZornVectorMatrix.Derivation.map_mul D _ _

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
  have hX' := congrArg canonicalVectorEquiv hX
  simpa only [toCanonicalEnd_apply, LinearEquiv.apply_symm_apply] using hX'

/-- Transport identifies the native derivation bracket with the endomorphism commutator. -/
theorem toCanonicalEnd_bracket (D E : VectorDerivation) :
    toCanonicalEnd (ZornVectorMatrix.Derivation.bracket D E) =
      toCanonicalEnd D * toCanonicalEnd E - toCanonicalEnd E * toCanonicalEnd D := by
  apply LinearMap.ext
  intro X
  apply canonicalVectorLinearEquiv.injective
  change (D (E (canonicalVectorEquiv X)) - E (D (canonicalVectorEquiv X))) =
    D (E (canonicalVectorEquiv X)) - E (D (canonicalVectorEquiv X))
  rfl

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
noncomputable def toKingdonEnd (D : VectorDerivation) :
    Module.End ℝ InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.AbstractKingdon :=
  NonAssocDerivation.transport ℝ CZ kingdonCanonicalLinearEquiv.symm
    (toCanonicalEnd D)

@[simp] theorem toKingdonEnd_apply (D : VectorDerivation)
    (x : InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.AbstractKingdon) :
    toKingdonEnd D x = kingdonCanonicalLinearEquiv.symm
      (toCanonicalEnd D (kingdonCanonicalLinearEquiv x)) := rfl

/-- The transported AbstractKingdon endomorphism satisfies the Leibniz law. -/
@[simp] theorem toKingdonEnd_leibniz (D : VectorDerivation)
    (x y : InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.AbstractKingdon) :
    toKingdonEnd D (x * y) = toKingdonEnd D x * y + x * toKingdonEnd D y := by
  apply kingdonCanonicalLinearEquiv.injective
  simp only [toKingdonEnd_apply, LinearEquiv.apply_symm_apply, LinearEquiv.map_add,
    kingdonCanonicalLinearEquiv_mul, zMul_eq_canonical_mul, toCanonicalEnd_leibniz]

/-- Transport of native derivations as a real-linear map into Kingdon endomorphisms. -/
noncomputable def kingdonDerivationLinearMap : VectorDerivation →ₗ[ℝ]
    Module.End ℝ InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.AbstractKingdon where
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

@[simp] theorem kingdonDerivationLinearMap_apply (D : VectorDerivation)
    (x : InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.AbstractKingdon) :
    kingdonDerivationLinearMap D x = toKingdonEnd D x := rfl

theorem kingdonDerivationLinearMap_injective :
    Function.Injective kingdonDerivationLinearMap := by
  intro D E h
  apply canonicalDerivationLinearMap_injective
  apply LinearMap.ext
  intro X
  let x := kingdonCanonicalLinearEquiv.symm X
  have hx := LinearMap.congr_fun h x
  have hx' := congrArg kingdonCanonicalLinearEquiv hx
  simpa only [x, kingdonDerivationLinearMap_apply, toKingdonEnd_apply,
    canonicalDerivationLinearMap_apply, LinearEquiv.apply_symm_apply] using hx'

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
noncomputable def kingdonDerivationLieHom : VectorDerivation →ₗ⁅ℝ⁆
    (Module.End ℝ InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.AbstractKingdon) where
  toLinearMap := kingdonDerivationLinearMap
  map_lie' := by
    intro D E
    change toKingdonEnd (ZornVectorMatrix.Derivation.bracket D E) =
      ⁅toKingdonEnd D, toKingdonEnd E⁆
    simpa only [LieRing.of_associative_ring_bracket] using toKingdonEnd_bracket D E

/-- The Kingdon derivation Lie algebra as the exact transported image. -/
noncomputable def kingdonDerivationLieAlgebra : LieSubalgebra ℝ
    (Module.End ℝ InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.AbstractKingdon) :=
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
    (kingdonDerivationLieEquiv D :
      Module.End ℝ InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.AbstractKingdon) =
      toKingdonEnd D := by
  rfl

end InfoGeometry.Algebra.Zorn.CanonicalDerivationBridge
