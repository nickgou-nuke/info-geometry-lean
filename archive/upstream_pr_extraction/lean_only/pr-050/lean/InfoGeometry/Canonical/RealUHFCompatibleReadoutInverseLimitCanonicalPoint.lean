import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat

/-!
# The distinguished normalized-trace point of the readout inverse limit

The compatible normalized-trace family is transported through the native
`TopCat` limit isomorphism.  This owner records its coordinate formula only;
it does not identify the point with a state, a KMS state, or a completed UHF
algebra element.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitCanonicalPoint

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat

noncomputable def normalizedTraceInverseLimitPoint :
    TopCat.carrier (limit readoutDiagram) :=
  compatibleReadoutInverseLimitIso.hom normalizedTraceReadoutFamily

theorem normalizedTraceInverseLimitPoint_projection
    (n : ℕ) :
    (limit.π readoutDiagram n)
        normalizedTraceInverseLimitPoint =
      normalizedTraceReadoutFamily.1 n := by
  have hmap :
      compatibleReadoutInverseLimitIso.hom ≫
          limit.π readoutDiagram n =
        readoutInverseCone.π.app n := by
    simpa [compatibleReadoutInverseLimitIso] using
      (IsLimit.conePointUniqueUpToIso_hom_comp
        readoutInverseConeIsLimit (limit.isLimit readoutDiagram) n)
  have h := congrArg
    (fun f => f normalizedTraceReadoutFamily) hmap
  change (limit.π readoutDiagram n)
      (compatibleReadoutInverseLimitIso.hom normalizedTraceReadoutFamily) =
    normalizedTraceReadoutFamily.1 n
  simpa [TopCat.comp_app, readoutInverseCone, coordinateTopCatHom] using h

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitCanonicalPoint

end
