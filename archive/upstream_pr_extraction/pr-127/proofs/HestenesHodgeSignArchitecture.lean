import proofs.HestenesDistinctHodge
import proofs.HestenesTransportedOddHodge
import proofs.HestenesBivectorSelfDuality

/-!
# The native sign architecture of the two Hodge operators

This owner records the shared pseudoscalar sign data and the two distinct
squares.  It intentionally does not identify the transported product
involution with the intrinsic complex Hodge structure.
-/

noncomputable section
namespace HestenesHodgeSignArchitecture

open HestenesCl14 HestenesCliffordCenter HestenesHermitianAdjoint
open HestenesBivectorCarrier HestenesHodgeEvenTransport
open HestenesDistinctHodge HestenesTransportedOddHodge
open HestenesBivectorSelfDuality

abbrev EvenPart := CliffordAlgebra.evenOdd Q14 0

 theorem omega_reverse_and_square :
    CliffordAlgebra.reverse
        (HestenesCliffordCenter.spacetimePseudoscalar : Cl14) =
        (HestenesCliffordCenter.spacetimePseudoscalar : Cl14) ∧
      (HestenesCliffordCenter.spacetimePseudoscalar : Cl14) *
          HestenesCliffordCenter.spacetimePseudoscalar = -1 :=
  ⟨reverse_spacetimePseudoscalar, spacetimePseudoscalar_sq⟩

 theorem intrinsic_even_hodge_sign :
    ∀ y : EvenPart, intrinsicEvenHodge (intrinsicEvenHodge y) = -y :=
  fun y => intrinsicEvenHodge_sq y

 theorem transported_paravector_hodge_sign :
    ∀ y : EvenPart, paravectorHodge (paravectorHodge y) = y :=
  fun y => paravectorHodge_sq y

 theorem transported_volume_adjoint_sign :
    hestenesAdjoint
        (HestenesHodgeEvenTransport.asEvenAlgebra
          HestenesCliffordCenter.spacetimePseudoscalar) =
      -(HestenesHodgeEvenTransport.asEvenAlgebra
          HestenesCliffordCenter.spacetimePseudoscalar) :=
  HestenesDistinctHodge.hestenesAdjoint_spacetimePseudoscalar

 theorem hodge_sign_architecture :
    (CliffordAlgebra.reverse
        (HestenesCliffordCenter.spacetimePseudoscalar : Cl14) =
        HestenesCliffordCenter.spacetimePseudoscalar) ∧
    ((HestenesCliffordCenter.spacetimePseudoscalar : Cl14) *
        HestenesCliffordCenter.spacetimePseudoscalar = -1) ∧
    (∀ y : EvenPart,
      intrinsicEvenHodge (intrinsicEvenHodge y) = -y) ∧
    (∀ y : EvenPart,
      paravectorHodge (paravectorHodge y) = y) ∧
    hestenesAdjoint
        (HestenesHodgeEvenTransport.asEvenAlgebra
          HestenesCliffordCenter.spacetimePseudoscalar) =
      -(HestenesHodgeEvenTransport.asEvenAlgebra
          HestenesCliffordCenter.spacetimePseudoscalar) := by
  exact ⟨reverse_spacetimePseudoscalar,
    spacetimePseudoscalar_sq,
    intrinsic_even_hodge_sign,
    transported_paravector_hodge_sign,
    transported_volume_adjoint_sign⟩

theorem real_product_projector_packet :
    (∀ y : EvenPart,
      productProjPlus (productProjPlus y) = productProjPlus y) ∧
    (∀ y : EvenPart,
      productProjMinus (productProjMinus y) = productProjMinus y) ∧
    (∀ y : EvenPart,
      productProjPlus (productProjMinus y) = 0 ∧
        productProjMinus (productProjPlus y) = 0) ∧
    (∀ y : EvenPart,
      productProjPlus y + productProjMinus y = y) :=
  ⟨productProjPlus_idempotent_apply,
    productProjMinus_idempotent_apply,
    productProjectors_cross_zero,
    productProjectors_add_apply⟩

theorem complex_hodge_projector_packet :
    (∀ F : ComplexBivector,
      selfDualProj (selfDualProj F) = selfDualProj F) ∧
    (∀ F : ComplexBivector,
      antiSelfDualProj (antiSelfDualProj F) = antiSelfDualProj F) ∧
    (∀ F : ComplexBivector,
      selfDualProj (antiSelfDualProj F) = 0 ∧
        antiSelfDualProj (selfDualProj F) = 0) ∧
    (∀ F : ComplexBivector,
      selfDualProj F + antiSelfDualProj F = F) ∧
    (∀ F : ComplexBivector,
      complexHodgeStar (selfDualProj F) = Complex.I • selfDualProj F) ∧
    (∀ F : ComplexBivector,
      complexHodgeStar (antiSelfDualProj F) =
        -Complex.I • antiSelfDualProj F) :=
  ⟨selfDualProj_idempotent_apply,
    antiSelfDualProj_idempotent_apply,
    fun F => ⟨selfDual_antiSelfDual_zero_apply F,
      antiSelfDual_selfDual_zero_apply F⟩,
    projectors_add_apply,
    star_on_selfDual,
    star_on_antiSelfDual⟩

end HestenesHodgeSignArchitecture
end noncomputable section
