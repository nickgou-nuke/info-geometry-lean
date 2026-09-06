import InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
import InfoGeometry.Algebra.Zorn.G2RootInnerDerivationBridge
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-!
# Alignment of finite G₂ roots with the native non-Cartan derivation indices

This owner records only the carrier identification.  Weyl equivariance and
root-space transport are intentionally downstream.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment

open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Algebra.Zorn.G2RootInnerDerivationBridge
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-- The native index selected by a finite short/long root label. -/
def rootIndexOf (r : G2Root) : nonzeroIndex :=
  ⟨rootCoordinate r, rootCoordinate_ne_cartan_indices r⟩

theorem rootIndexOf_val (r : G2Root) :
    (rootIndexOf r).1 = rootCoordinate r := rfl

theorem rootIndexOf_injective : Function.Injective rootIndexOf := by
  intro r s h
  apply rootCoordinate_injective
  exact congrArg Subtype.val h

theorem rootIndexOf_derivation_readback (r : G2Root) :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (zornDerivationRootRepresentation r) =
      rootDerivation (rootIndexOf r).1 := by
  simpa [rootIndexOf_val] using
    (finiteRoot_derivation_canonical_transport r)

theorem rootIndexOf_surjective : Function.Surjective rootIndexOf := by
  native_decide

noncomputable def rootIndexEquiv : G2Root ≃ nonzeroIndex :=
  Equiv.ofBijective rootIndexOf
    ⟨rootIndexOf_injective, rootIndexOf_surjective⟩

@[simp] theorem rootIndexEquiv_apply (r : G2Root) :
    rootIndexEquiv r = rootIndexOf r := rfl

end InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
