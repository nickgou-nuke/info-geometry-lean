import InfoGeometry.Lie.MathlibBackportBasisLieEnd
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-! Project-owned compatibility module forwarding upstream Cartan criterion foundations.

`Polynomial.exists_eval_eq_iff` is provided upstream by `Mathlib.LinearAlgebra.Lagrange`.
`LinearMap.baseChangeHom_injective` is provided upstream by `Mathlib.RingTheory.Flat.Basic`.
`Module.End.IsSemisimple.iSup_eigenspace_eq_top` and `Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue`
are provided upstream by `Mathlib.LinearAlgebra.Eigenspace.Semisimple`.
-/

noncomputable section
section

namespace LinearMap

lemma baseChangeHom_injective_of_faithfulSMul
    {R S M N : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [FaithfulSMul R S] [Module.Flat R N] :
    Function.Injective (LinearMap.baseChangeHom R S M N) := by
  intro f g h
  ext m
  have hmk : Function.Injective (TensorProduct.mk R S N (1 : S)) := by
    have hfac : TensorProduct.mk R S N (1 : S) =
        (Algebra.linearMap R S).rTensor N ∘ (TensorProduct.lid R N).symm := by
      ext
      simp
    rw [hfac]
    exact Function.Injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap
        (M := N) (Algebra.linearMap R S)
        (FaithfulSMul.algebraMap_injective R S))
      (LinearEquiv.injective _)
  have h_eq : (1 : S) ⊗ₜ[R] f m = (1 : S) ⊗ₜ[R] g m := by
    simpa only [LinearMap.baseChangeHom_apply, LinearMap.baseChange_tmul] using
      LinearMap.congr_fun h ((1 : S) ⊗ₜ[R] m)
  exact hmk h_eq

end LinearMap
