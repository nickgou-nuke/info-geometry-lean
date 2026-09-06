import InfoGeometry.Analysis.AsanoContractionNative
import InfoGeometry.AsanoRuelle.MobiusPoleEndpointClosure

/-!
# Closed/bounded endpoint closure for Asano contraction

This is the downstream consumer that connects the explicit Möbius endpoint
theorem to the nondegenerate Asano contraction adapters.  It adds no new
analytic assumption and makes no categorical or conformal claim.
-/

noncomputable section

namespace InfoGeometry.AsanoRuelle

open InfoGeometry.Analysis.AsanoContractionNative
open Bornology

theorem asanoContract_ne_zero_outside_signedProduct_of_closed_bounded_zeroFree
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂)
    (hK₁_bounded : IsBounded K₁)
    (hK₂_bounded : IsBounded K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    asanoContract A D z ≠ 0 := by
  have hpoles := mobius_both_poles_mem_of_closed_bounded_zeroFree
    hK₁ hK₂ hK₁_bounded hK₂_bounded hzf hD hdet
  have hC : C ≠ 0 := by
    intro hC
    apply h0₁
    simpa [hC] using hpoles.1
  have hB : B ≠ 0 := by
    intro hB
    apply h0₂
    simpa [hB] using hpoles.2
  exact asanoContract_ne_zero_outside_signedProduct_of_nonDegenerate_via_endpoint
    h0₁ h0₂ hzf hD (Or.inl ⟨hC, hpoles.1⟩) hz_not

theorem contracted_zero_mem_signedProduct_of_closed_bounded_zeroFree
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂)
    (hK₁_bounded : IsBounded K₁)
    (hK₂_bounded : IsBounded K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hzero : IsContractedZero A D z) :
    z ∈ signedProductSet K₁ K₂ := by
  have hpoles := mobius_both_poles_mem_of_closed_bounded_zeroFree
    hK₁ hK₂ hK₁_bounded hK₂_bounded hzf hD hdet
  have hC : C ≠ 0 := by
    intro hC
    apply h0₁
    simpa [hC] using hpoles.1
  exact contracted_zero_mem_signedProduct_of_nonDegenerate_via_endpoint
    h0₁ h0₂ hzf hD (Or.inl ⟨hC, hpoles.1⟩) hzero

theorem asanoContract_ne_zero_outside_signedProduct_of_closed_bounded_zeroFree_all_branches
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂)
    (hK₁_bounded : IsBounded K₁)
    (hK₂_bounded : IsBounded K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    asanoContract A D z ≠ 0 := by
  by_cases hD : D = 0
  · exact asanoContract_ne_zero_of_D_eq_zero h0₁ h0₂ hzf hD
  · by_cases hdet : A * D - B * C = 0
    · exact asanoContract_ne_zero_outside_signedProduct_of_rankOne
        h0₁ h0₂ hzf hD hdet hz_not
    · exact asanoContract_ne_zero_outside_signedProduct_of_closed_bounded_zeroFree
        h0₁ h0₂ hK₁ hK₂ hK₁_bounded hK₂_bounded hzf hD hdet hz_not

theorem contracted_zero_mem_signedProduct_of_closed_bounded_zeroFree_all_branches
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂)
    (hK₁_bounded : IsBounded K₁)
    (hK₂_bounded : IsBounded K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hzero : IsContractedZero A D z) :
    z ∈ signedProductSet K₁ K₂ := by
  by_cases hD : D = 0
  · have hneq : asanoContract A D z ≠ 0 :=
      asanoContract_ne_zero_of_D_eq_zero h0₁ h0₂ hzf hD
    exact False.elim (hneq hzero)
  · by_cases hdet : A * D - B * C = 0
    · exact contracted_zero_mem_signedProduct_of_rankOne
        h0₁ h0₂ hzf hD hdet hzero
    · exact contracted_zero_mem_signedProduct_of_closed_bounded_zeroFree
        h0₁ h0₂ hK₁ hK₂ hK₁_bounded hK₂_bounded hzf hD hdet hzero

end InfoGeometry.AsanoRuelle
