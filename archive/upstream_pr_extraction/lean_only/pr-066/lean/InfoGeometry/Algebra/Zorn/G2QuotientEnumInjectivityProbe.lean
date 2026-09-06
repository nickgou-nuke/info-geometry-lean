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

/-! Quotient equality is equivalent to membership in the concrete PC subgroup.
The subgroup owner already identifies that subgroup with the native
polycyclic-word image, so this direction produces an actual PC exponent rather
than attempting a global table enumeration. -/
theorem quotient_equality_has_pc_factor
    (i j : Fin 189)
    (hquot : quotientRepresentative i = quotientRepresentative j) :
    ∃ e : PCWordExp,
      autMatrix ((flagRepresentative i)⁻¹ * flagRepresentative j) =
        autMatrix (pcWord e) := by
  have hmem :
      (flagRepresentative i)⁻¹ * flagRepresentative j ∈
        G2TwoPCSubgroupClosure.unipotentSubgroup :=
    (quotientRepresentative_eq_iff i j).1 hquot
  let z : G2TwoPCSubgroupClosure.unipotentSubgroup :=
    ⟨(flagRepresentative i)⁻¹ * flagRepresentative j, hmem⟩
  obtain ⟨e, he⟩ := (G2TwoPCSubgroupClosure.pcWordMulEquiv).surjective z
  refine ⟨e, ?_⟩
  have he' : pcWord e = (flagRepresentative i)⁻¹ * flagRepresentative j := by
    exact congrArg Subtype.val he
  exact congrArg autMatrix he'.symm

theorem quotient_equality_iff_pc_matrix_factor
    (i j : Fin 189) :
    quotientRepresentative i = quotientRepresentative j ↔
      ∃ e : PCWordExp,
        autMatrix ((flagRepresentative i)⁻¹ * flagRepresentative j) =
          autMatrix (pcWord e) := by
  constructor
  · exact quotient_equality_has_pc_factor i j
  · rintro ⟨e, he⟩
    exact quotientRepresentative_eq_of_pc_matrix_factor i j e he

end InfoGeometry.Algebra.Zorn.G2QuotientEnumInjectivityProbe
