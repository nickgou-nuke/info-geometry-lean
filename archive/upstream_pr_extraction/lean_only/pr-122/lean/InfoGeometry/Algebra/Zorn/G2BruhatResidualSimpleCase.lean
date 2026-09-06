import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
import InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords

/-!
# A concrete simple-reflection residual inclusion

This owner connects the existing corrected second-reflection conjugation
certificate to the residual-subgroup convention used by the Bruhat carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleCase

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2TwoOppositeUnipotent
open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2RootPCAlignment
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords

noncomputable instance : Fintype (residualSubgroup (2, true)) :=
  Fintype.ofFinite _

theorem correctedT_eq_w0_mul_weylNF :
    correctedT = w0 * weylNF 2 true := by
  change concreteWeylElement 11 = c ^ 3 * (s * c ^ 2)
  rw [c_pow_three_eq_swapCartan]
  change swapCartanAut * (swap01Aut * (cycle012Aut * cycle012Aut)) =
    swapCartanAut * (swap01Aut * c ^ 2)
  rw [c_pow_two_eq_cycle012_sq]

theorem residual_conjugator_simple_eq_weylNF_five_true :
    w0 * weylNF 2 true = weylNF 5 true := by
  rw [← correctedT_eq_w0_mul_weylNF]
  exact concreteWeylElement_eleven_eq_weylNF_five_true

theorem residual_conjugator_simple_length :
    weylLength (weylElementOfNF (5, true)) = 3 := by
  decide

theorem correctedTComplementSubgroup_le_residualSubgroup :
    correctedTComplementSubgroup ≤ residualSubgroup (2, true) := by
  intro x hx
  apply Subgroup.mem_inf.mpr
  constructor
  · exact correctedTComplementSubgroup_le_unipotentSubgroup hx
  · change correctedT⁻¹ * x * correctedT ∈ unipotentSubgroup
    exact correctedT_complement_conj_mem_unipotent x hx

theorem canonicalResidualPCWord_simple_mem_residualSubgroup
    (e : CanonicalResidualExponent (weylElementOfNF (2, true))) :
    canonicalResidualPCWord (weylElementOfNF (2, true)) e ∈
      residualSubgroup (2, true) := by
  apply correctedTComplementSubgroup_le_residualSubgroup
  apply pcWord_mem_correctedTComplement
  change residualToPCExponent (weylElementOfNF (2, true)) e 0 = false
  unfold residualToPCExponent
  apply dif_neg
  intro h
  rcases h with ⟨α, hα⟩
  have : rootPCAlignment α.1 = 0 := hα
  have hroot : α.1 = G2PositiveRoot.alpha := by
    apply (rootPCAlignment.injective)
    simpa using this
  have hnot : G2PositiveRoot.alpha ∉
      canonicalSignedInversionRoots (weylElementOfNF (2, true)) := by
    decide
  apply hnot
  simpa [hroot] using α.2

theorem residualSubgroup_simple_card_ge_canonical_residual_card :
    Fintype.card (CanonicalResidualExponent (weylElementOfNF (2, true))) ≤
      Fintype.card (residualSubgroup (2, true)) := by
  let f : CanonicalResidualExponent (weylElementOfNF (2, true)) →
      residualSubgroup (2, true) := fun e =>
    ⟨canonicalResidualPCWord (weylElementOfNF (2, true)) e,
      canonicalResidualPCWord_simple_mem_residualSubgroup e⟩
  apply Fintype.card_le_of_injective f
  intro e₁ e₂ h
  apply canonicalResidualPCWord_injective (weylElementOfNF (2, true))
  exact congrArg Subtype.val h

theorem residualSubgroup_simple_card_ge_8 :
    8 ≤ Fintype.card (residualSubgroup (2, true)) := by
  have h := residualSubgroup_simple_card_ge_canonical_residual_card
  rw [canonicalResidualExponent_card] at h
  have hw : weylLength (weylElementOfNF (2, true)) = 3 := by
    decide
  rw [hw] at h
  norm_num at h ⊢
  exact h

theorem residualSubgroup_simple_card_ge_32_from_complement :
    32 ≤ Fintype.card (residualSubgroup (2, true)) := by
  let E := {e : G2TwoSylowSubgroup.PCWordExp // e 0 = false}
  let f : E → residualSubgroup (2, true) := fun e =>
    ⟨G2TwoSylowSubgroup.pcWord e.1,
      correctedTComplementSubgroup_le_residualSubgroup
        (pcWord_mem_correctedTComplement e.1 e.2)⟩
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    apply Subtype.ext
    apply G2TwoPCRecovery.pcWord_injective
    exact congrArg Subtype.val h
  have hc : Fintype.card E = 32 := by
    decide
  rw [← hc]
  exact Fintype.card_le_of_injective f hf

theorem no_canonical_residual_equiv_simple :
    ¬ Nonempty (CanonicalResidualExponent (weylElementOfNF (2, true)) ≃
      residualSubgroup (2, true)) := by
  rintro ⟨hEquiv⟩
  have hcard := Fintype.card_congr hEquiv
  rw [canonicalResidualExponent_card] at hcard
  have hw : weylLength (weylElementOfNF (2, true)) = 3 := by
    decide
  rw [hw] at hcard
  have hlow := residualSubgroup_simple_card_ge_32_from_complement
  norm_num at hcard hlow
  omega

end InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleCase
