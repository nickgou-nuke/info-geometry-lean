import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

namespace InfoGeometry.Algebra.Zorn.G2FlagCellQuotientProbe

open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def gapExp (support : List (Fin 6)) : PCWordExp :=
  fun i => decide (i ∈ support)

example :
    quotientRepresentative 45 =
      (QuotientGroup.mk
        (pcWord (gapExp [(1 : Fin 6), (4 : Fin 6)]) *
          weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) : CarrierQuotient) := by
  change QuotientGroup.mk (flagRepresentative 45) = _
  rw [QuotientGroup.eq]
  have hex : ∃ e : PCWordExp,
      autMatrix ((flagRepresentative 45)⁻¹ *
        (pcWord (gapExp [(1 : Fin 6), (4 : Fin 6)]) *
          weylNF (orbitWeyl 1).1 (orbitWeyl 1).2)) =
        autMatrix (pcWord e) := by
    decide
  obtain ⟨e, he⟩ := hex
  have hgroup :
      (flagRepresentative 45)⁻¹ *
          (pcWord (gapExp [(1 : Fin 6), (4 : Fin 6)]) *
            weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) =
        pcWord e := by
    exact autMatrix_injective he
  rw [hgroup]
  exact ⟨e, rfl⟩

end InfoGeometry.Algebra.Zorn.G2FlagCellQuotientProbe
