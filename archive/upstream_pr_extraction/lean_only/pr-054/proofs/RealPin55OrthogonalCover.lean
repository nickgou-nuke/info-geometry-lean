import proofs.RealPin55ExactKernel
import proofs.OQ55MatrixEquiv
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The exact real `Pin(5,5) -> O(5,5)` quotient cover

This owner packages the two independently proved ingredients:

* constructive surjectivity of the twisted Clifford representation;
* its exact kernel, the two central scalar signs.

The result is the literal group equivalence
`FullPin55 / {+1,-1} ~= O(5,5)`.
-/

noncomputable section
namespace RealPin55OrthogonalCover

open RealPin55Core
open RealOrthogonalGroup55
open RealPin55MatrixRepresentation
open RealPin55Kernel
open RealPin55ExactKernel
open OQ55MatrixEquiv

instance centralSignSubgroup_normal : centralSignSubgroup.Normal := by
  rw [<- fullPinToO55_kernel_exact]
  infer_instance

/-- First-isomorphism-theorem form of the real split Pin cover. -/
noncomputable def fullPinQuotientKernelEquivO55 :
    FullPin55 ⧸ MonoidHom.ker fullPinToO55 ≃* O55 :=
  QuotientGroup.quotientKerEquivOfSurjective fullPinToO55
    fullPinToO55_surjective

/-- Strong literal form: quotienting by the two central Clifford signs gives
the full real orthogonal group of the split `(5,5)` form. -/
noncomputable def fullPinQuotientCentralSignEquivO55 :
    FullPin55 ⧸ centralSignSubgroup ≃* O55 :=
  (QuotientGroup.congr centralSignSubgroup
      (MonoidHom.ker fullPinToO55)
      (MulEquiv.refl FullPin55) (by
        simpa using fullPinToO55_kernel_exact.symm)).trans
    fullPinQuotientKernelEquivO55

/-- Exact algebraic covering packet for the real split Pin representation. -/
theorem real_pin55_orthogonal_cover_packet :
    Function.Surjective fullPinToO55 ∧
      MonoidHom.ker fullPinToO55 = centralSignSubgroup ∧
      (∀ g : FullPin55,
        g ∈ MonoidHom.ker fullPinToO55 ↔ g = 1 ∨ g = pinNegOne) ∧
      Nonempty (FullPin55 ⧸ centralSignSubgroup ≃* O55) := by
  exact ⟨fullPinToO55_surjective, fullPinToO55_kernel_exact,
    mem_fullPinToO55_kernel_iff, ⟨fullPinQuotientCentralSignEquivO55⟩⟩

end RealPin55OrthogonalCover
end noncomputable section
