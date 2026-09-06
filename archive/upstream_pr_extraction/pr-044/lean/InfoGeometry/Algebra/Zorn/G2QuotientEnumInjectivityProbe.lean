import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

namespace InfoGeometry.Algebra.Zorn.G2QuotientEnumInjectivityProbe

open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_nontrivial_pc_quotient_factor :
    ∀ i j : Fin 189, i ≠ j →
      ∀ e : PCWordExp,
        autMatrix ((flagRepresentative i)⁻¹ * flagRepresentative j) ≠
          autMatrix (pcWord e) := by
  decide

theorem quotientRepresentative_injective :
    Function.Injective quotientRepresentative := by
  intro i j h
  by_contra hij
  rw [quotientRepresentative_eq_iff] at h
  obtain ⟨e, he⟩ := h
  exact no_nontrivial_pc_quotient_factor i j hij e
    (autMatrix_injective he)

theorem quotient_card_ge_189 :
    189 ≤ Fintype.card CarrierQuotient := by
  have h := Fintype.card_le_of_injective
    quotientRepresentative quotientRepresentative_injective
  simpa using h

end InfoGeometry.Algebra.Zorn.G2QuotientEnumInjectivityProbe
