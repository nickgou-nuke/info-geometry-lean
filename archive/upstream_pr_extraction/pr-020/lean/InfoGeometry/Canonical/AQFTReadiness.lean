import InfoGeometry.Canonical.AQFTHilbertCompression
import InfoGeometry.Canonical.BogoliubovFockSuper

/-!
# InfoGeometry.Canonical.AQFTReadiness

Static AQFT readiness packages over the concrete Hilbert compression models.
-/

namespace InfoGeometry.Canonical.AQFTOperatorInterface

open InfoGeometry.Canonical.BogoliubovFockSuper

section CanonicalReadiness

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Static AQFT readiness data for the real Hilbert model.
-/
structure AQFTReadinessPackage
    (F E : Type)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  isCStarReadyF : IsCStarReady (Obs := RealHilbertObs F)
  isCompleteCStarReadyE : IsCompleteCStarReady (Obs := RealHilbertObs E)
  interpretation : AQFTOperatorInterpretation E (RealHilbertObs E)
  projectorSuperPair :
    IsProjectorSuperPair (E := E)
      (InfoGeometry.Quantum.annihilationOp (E := E))
      (InfoGeometry.Quantum.creationOp (E := E))

/-- Canonical static readiness package for the real Hilbert AQFT model. -/
def aqftReadinessPackageRealHilbert :
    AQFTReadinessPackage F E where
  isCStarReadyF := by
    infer_instance
  isCompleteCStarReadyE := by
    exact ⟨by infer_instance, inferInstance⟩
  interpretation := realHilbertCompressionInterpretation (E := E)
  projectorSuperPair := projectorSuperPair_base (E := E)

end CanonicalReadiness

end InfoGeometry.Canonical.AQFTOperatorInterface
