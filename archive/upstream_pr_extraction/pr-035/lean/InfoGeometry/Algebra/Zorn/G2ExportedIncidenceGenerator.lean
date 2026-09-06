import InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction
import InfoGeometry.Algebra.Zorn.G2CASNativePointAction

/-!
# Exported incidence preservation for the CAS generator permutations

This owner records the finite certificate check for the seven explicit point
permutations used by the native orbit computation.  It does not promote the
generator check to transitivity of `SplitOctF2Aut`; that requires a separate
generation and orbit theorem.
-/

namespace InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator

open InfoGeometry.Algebra.Zorn.G2FlagIncidenceAction
open InfoGeometry.Algebra.Zorn.G2CASNativePointAction
open InfoGeometry.Algebra.Zorn.G2HexagonIncidence
open InfoGeometry.Algebra.Zorn.G2ParabolicIncidenceCertificate

theorem casPointPerm_preserves_incidence (k : Fin 7) :
    PreservesIncidence (casPointPerm k) := by
  intro p l
  simp only [parabolicCertificate, parabolicLinePoints, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change l ∈ incidence p ↔
    casPointPermRaw k l ∈ incidence (casPointPermRaw k p)
  fin_cases k <;> fin_cases p <;> fin_cases l <;> decide

theorem correctedTPointPerm_preserves_incidence :
    PreservesIncidence correctedTPointPerm := by
  intro p l
  simp only [parabolicCertificate, parabolicLinePoints, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change l ∈ incidence p ↔
    correctedTPointPermRaw l ∈ incidence (correctedTPointPermRaw p)
  fin_cases p <;> fin_cases l <;> decide

end InfoGeometry.Algebra.Zorn.G2ExportedIncidenceGenerator
