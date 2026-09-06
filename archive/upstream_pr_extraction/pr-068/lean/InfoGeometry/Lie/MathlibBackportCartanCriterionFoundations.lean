module

import InfoGeometry.Lie.MathlibBackportBasisLieEnd
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

noncomputable section
public section

namespace Polynomial

lemma exists_eval_eq_iff {F ι : Type*} [Field F] [Finite ι] (x y : ι → F) :
    (∃ q : F[X], ∀ i, q.eval (x i) = y i) ↔
      ∀ i j, x i = x j → y i = y j := by
  refine ⟨fun ⟨q, hq⟩ i j hij ↦ by rw [← hq, ← hq, hij], ?_⟩
  intro hxy
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let v : F → F := fun z ↦ if h : ∃ i, x i = z then y h.choose else 0
  refine ⟨Lagrange.interpolate (Finset.univ.image x) (fun d : F ↦ d) v, ?_⟩
  intro i
  change Polynomial.eval ((fun d : F ↦ d) (x i))
      (Lagrange.interpolate (Finset.univ.image x) (fun d : F ↦ d) v) = y i
  have hi := Lagrange.eval_interpolate_at_node v Function.injective_id.injOn
    (i := x i) (by simp : x i ∈ Finset.univ.image x)
  calc
    _ = v (x i) := by simpa using hi
    _ = y i := by
      dsimp [v]
      split_ifs with h
      · exact hxy h.choose i h.choose_spec
      · exact False.elim (h ⟨i, rfl⟩)

end Polynomial

namespace LinearMap

lemma baseChangeHom_injective_of_faithfulSMul
    {R S M N : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [FaithfulSMul R S] [Module.Flat R N] :
    Function.Injective (LinearMap.baseChangeHom R S M N) := by
  intro f g h
  ext m
  have hmk : Function.Injective (TensorProduct.mk R S N 1) := by
    have hfac : TensorProduct.mk R S N 1 =
        (Algebra.linearMap R S).rTensor N ∘ (TensorProduct.lid R N).symm := by
      ext
      simp
    rw [hfac]
    exact Function.Injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap
        (M := N) (Algebra.linearMap R S)
        (FaithfulSMul.algebraMap_injective R S))
      (LinearEquiv.injective _)
  apply hmk
  simpa only [LinearMap.baseChangeHom_apply, LinearMap.baseChange_tmul] using
    LinearMap.congr_fun h (1 ⊗ₜ[R] m)

lemma baseChangeHom_injective {R S M N : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.FaithfullyFlat R S] :
    Function.Injective (LinearMap.baseChangeHom R S M N) := by
  intro f g h
  ext m
  rw [← sub_eq_zero]
  apply ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (A := S) R N
    (f m - g m)).mp)
  have hm := LinearMap.congr_fun h ((1 : S) ⊗ₜ[R] m)
  have hm0 : ((1 : S) ⊗ₜ[R] f m) = ((1 : S) ⊗ₜ[R] g m) := by
    simpa only [LinearMap.baseChangeHom_apply, LinearMap.baseChange_tmul] using hm
  have hm' : ((1 : S) ⊗ₜ[R] f m) - ((1 : S) ⊗ₜ[R] g m) = 0 := sub_eq_zero.mpr hm0
  simpa only [← TensorProduct.tmul_sub] using hm'

end LinearMap

namespace Module.End

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {f : End K V}

lemma IsSemisimple.iSup_eigenspace_eq_top (hf : f.IsSemisimple) :
    ⨆ μ : K, f.eigenspace μ = ⊤ := by
  simpa only [hf.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using
    iSup_maxGenEigenspace_eq_top f

lemma IsSemisimple.eq_zero_iff_forall_eigenvalue (hf : f.IsSemisimple) :
    f = 0 ↔ ∀ μ : K, f.HasEigenvalue μ → μ = 0 := by
  constructor
  · rintro rfl μ hμ
    by_contra hμ0
    obtain ⟨x, hx, hx_ne⟩ := (Submodule.ne_bot_iff _).mp hμ
    rw [mem_eigenspace_iff] at hx
    exact hx_ne ((smul_eq_zero.mp hx.symm).resolve_left hμ0)
  · intro h
    suffices f.eigenspace 0 = ⊤ by rwa [eigenspace_zero, LinearMap.ker_eq_top] at this
    rw [← hf.iSup_eigenspace_eq_top]
    refine le_antisymm (le_iSup _ 0) (iSup_le fun μ ↦ ?_)
    rcases eq_or_ne μ 0 with rfl | hμ
    · exact le_refl _
    · have : f.eigenspace μ = ⊥ := not_not.mp (hasEigenvalue_iff.not.mp fun he ↦ hμ (h μ he))
      simp [this]

end Module.End
