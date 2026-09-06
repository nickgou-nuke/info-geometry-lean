import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeGenerationClosure
import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeHestenesMonodromyConsumer

/-!
# Generated Hestenes closure of the finite Laurent-mode operators

Explicit algebraic generation of the ambient carrier gives global ambient
connection--monodromy commutation.  The supplied continuous-linear equivalence
then transports that equality to every vector of the doubled Hestenes--Krein
carrier.

No density, completion, convergence, or holonomy theorem is used.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeHestenesGenerationClosure

open HadjiivanovLogConnectionBridge
open HadjiivanovLogConnectionHestenesKreinConsumer
open HadjiivanovFiniteLaurentModeTower
open HadjiivanovFiniteLaurentModeColimitProjection
open HadjiivanovFiniteLaurentModeRealification
open HadjiivanovFiniteLaurentModeMonodromyReadout
open HadjiivanovFiniteLaurentModeHestenesMonodromyConsumer
open HadjiivanovFiniteLaurentModeGenerationClosure
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Krein

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {A_inf : Type*} [NormedAddCommGroup A_inf] [NormedSpace ℂ A_inf]

/-- Under explicit finite-mode generation, the represented logarithmic
connection and represented Hadjiivanov readout commute on the entire doubled
Hestenes--Krein carrier. -/
theorem representedConnection_monodromy_commute
    (R : LogResidue V)
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientConnection ambientMonodromy : A_inf →ₗ[ℂ] A_inf)
    (ambientConnection_comm : ∀ n,
      ambientConnection.comp (psi n) =
        (psi n).comp (finiteModeConnection R n))
    (ambientMonodromy_comm : ∀ n,
      ambientMonodromy.comp (psi n) =
        (psi n).comp (finiteModeMonodromyReadout R n))
    (hGenerate : FiniteModeImagesGenerate A_inf psi)
    (H : HestenesKreinCone)
    (K : HestenesKreinConnectionConsumer
      (LaurentModeTower V) A_inf
      (realifiedFiniteModeConnectionCone R A_inf psi psi_comm
        ambientConnection ambientConnection_comm) H)
    (M : FiniteModeHestenesMonodromyConsumer R psi psi_comm
      ambientConnection ambientMonodromy ambientConnection_comm H K) :
    K.ambientDifferential.comp M.monodromyDifferential =
      M.monodromyDifferential.comp K.ambientDifferential := by
  have hAmbient := ambientConnection_monodromy_commute R A_inf psi psi_comm
    ambientConnection ambientMonodromy ambientConnection_comm
    ambientMonodromy_comm hGenerate
  apply ContinuousLinearMap.ext
  intro v
  let y : A_inf := K.identify.symm v
  have hv : K.identify y = v := K.identify.apply_symm_apply v
  rw [← hv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    M.identifiesMonodromy, K.identifiesConnection,
    K.identifiesConnection, M.identifiesMonodromy]
  exact congrArg K.identify (LinearMap.congr_fun hAmbient y)

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeHestenesGenerationClosure
