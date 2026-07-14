import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

noncomputable section

namespace CanonicalZornDerivation

open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ
abbrev VZ := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev VDer := InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)

def IsDerivation (D : EndCZ) : Prop :=
  ∀ X Y : CZ, D (X * Y) = D X * Y + X * D Y

noncomputable def derivationSubmodule : Submodule ℝ EndCZ where
  carrier := {D | IsDerivation D}
  zero_mem' := by
    intro X Y
    simp only [LinearMap.zero_apply, zero_mul, mul_zero, add_zero]
  add_mem' := by
    intro D E hD hE X Y
    simp only [LinearMap.add_apply]
    rw [hD, hE, add_mul, mul_add]
    abel
  smul_mem' := by
    intro r D hD X Y
    simp only [LinearMap.smul_apply]
    rw [hD, smul_mul,
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul, smul_add]

noncomputable def canonicalZornDerivations : LieSubalgebra ℝ EndCZ :=
  { derivationSubmodule with
    lie_mem' := by
      intro D E hD hE X Y
      rw [LieRing.of_associative_ring_bracket]
      change D (E (X * Y)) - E (D (X * Y)) =
        (D (E X) - E (D X)) * Y + X * (D (E Y) - E (D Y))
      rw [hE, hD, map_add, map_add, hD, hD, hE, hE]
      rw [sub_mul, mul_sub]
      abel }

@[simp] theorem mem_canonicalZornDerivations (D : EndCZ) :
    D ∈ canonicalZornDerivations ↔ IsDerivation D := Iff.rfl

noncomputable def vectorToCanonicalEnd (D : VDer) : EndCZ where
  toFun X := canonicalVectorEquiv.symm (D (canonicalVectorEquiv X))
  map_add' X Y := by
    simp only [canonicalVectorEquiv_add, D.map_add,
      canonicalVectorEquiv_symm_add]
  map_smul' r X := by
    simp only [canonicalVectorEquiv_smul, D.map_smul,
      canonicalVectorEquiv_symm_smul, RingHom.id_apply]

@[simp] theorem vectorToCanonicalEnd_apply (D : VDer) (X : CZ) :
    vectorToCanonicalEnd D X =
      canonicalVectorEquiv.symm (D (canonicalVectorEquiv X)) := rfl

theorem vectorToCanonicalEnd_isDerivation (D : VDer) :
    IsDerivation (vectorToCanonicalEnd D) := by
  intro X Y
  apply canonicalVectorEquiv.injective
  simp only [vectorToCanonicalEnd_apply, Equiv.apply_symm_apply,
    canonicalVectorEquiv_mul, D.map_mul, canonicalVectorEquiv_add]

noncomputable def vectorToCanonicalDerivation (D : VDer) : canonicalZornDerivations :=
  ⟨vectorToCanonicalEnd D, vectorToCanonicalEnd_isDerivation D⟩

noncomputable def canonicalToVectorDerivation
    (D : canonicalZornDerivations) : VDer where
  toFun X := canonicalVectorEquiv (D.1 (canonicalVectorEquiv.symm X))
  map_add' X Y := by
    simp only [canonicalVectorEquiv_symm_add, map_add, canonicalVectorEquiv_add]
  map_smul' r X := by
    simp only [canonicalVectorEquiv_symm_smul, map_smul, canonicalVectorEquiv_smul]
  map_mul' X Y := by
    have hD : IsDerivation D.1 := D.property
    rw [canonicalVectorEquiv_symm_mul, hD]
    simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_add,
      Equiv.apply_symm_apply]

@[simp] theorem canonicalToVectorDerivation_apply
    (D : canonicalZornDerivations) (X : VZ) :
    canonicalToVectorDerivation D X =
      canonicalVectorEquiv (D.1 (canonicalVectorEquiv.symm X)) := rfl

noncomputable def vectorCanonicalLinearEquiv :
    VDer ≃ₗ[ℝ] canonicalZornDerivations where
  toFun := vectorToCanonicalDerivation
  invFun := canonicalToVectorDerivation
  left_inv D := by
    apply InfoGeometry.Algebra.ZornVectorMatrix.Derivation.ext
    intro X
    simp [vectorToCanonicalDerivation, canonicalToVectorDerivation,
      vectorToCanonicalEnd]
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    simp [vectorToCanonicalDerivation, canonicalToVectorDerivation,
      vectorToCanonicalEnd]
  map_add' D E := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    apply canonicalVectorEquiv.injective
    change InfoGeometry.Algebra.ZornVectorMatrix.Derivation.add D E
        (canonicalVectorEquiv X) =
      InfoGeometry.Algebra.ZornVectorMatrix.add
        (D (canonicalVectorEquiv X)) (E (canonicalVectorEquiv X))
    rfl
  map_smul' r D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    apply canonicalVectorEquiv.injective
    change InfoGeometry.Algebra.ZornVectorMatrix.Derivation.smul r D
        (canonicalVectorEquiv X) =
      InfoGeometry.Algebra.ZornVectorMatrix.smul r (D (canonicalVectorEquiv X))
    rfl

noncomputable def vectorCanonicalLieEquiv :
    VDer ≃ₗ⁅ℝ⁆ canonicalZornDerivations :=
  { vectorCanonicalLinearEquiv with
    map_lie' := by
      intro D E
      apply Subtype.ext
      apply LinearMap.ext
      intro X
      apply canonicalVectorEquiv.injective
      change InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket D E
          (canonicalVectorEquiv X) =
        InfoGeometry.Algebra.ZornVectorMatrix.sub
          (D (E (canonicalVectorEquiv X))) (E (D (canonicalVectorEquiv X)))
      rfl }

end CanonicalZornDerivation
