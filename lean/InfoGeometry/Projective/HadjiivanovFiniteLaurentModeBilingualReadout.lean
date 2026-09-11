import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeHestenesKreinConsumer
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BilingualRealHestenesDictionary

/-!
# Bilingual readout of the finite Laurent-mode Hestenes connection

The represented connection already commutes with the doubled Hestenes clock
axis.  This owner reads that theorem in the repository's equivalent
`complex_i`, `KLinear`, and vanishing-commutator languages.  It adds no complex
analytic structure and no holonomy assertion.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeBilingualReadout

open HadjiivanovLogConnectionBridge
open HadjiivanovLogConnectionHestenesKreinConsumer
open HadjiivanovFiniteLaurentModeTower
open HadjiivanovFiniteLaurentModeColimitProjection
open HadjiivanovFiniteLaurentModeRealification
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesRealStructures
open InfoGeometry.Canonical.BilingualRealHestenesDictionary
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Krein

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {A_inf : Type*} [NormedAddCommGroup A_inf] [NormedSpace ℂ A_inf]
variable (R : LogResidue V)
variable (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
variable (ambientConnection : A_inf →ₗ[ℂ] A_inf)
variable (ambientConnection_comm : ∀ n,
  ambientConnection.comp (psi n) =
    (psi n).comp (finiteModeConnection R n))
variable (H : HestenesKreinCone)

variable (K : HestenesKreinConnectionConsumer
  (LaurentModeTower V) A_inf
  (realifiedFiniteModeConnectionCone R A_inf psi psi_comm
    ambientConnection ambientConnection_comm) H)

/-- Bilingual pointwise readout: the represented differential commutes with
the real doubled operator named `complex_i`. -/
theorem representedFiniteModeConnection_complex_i
    (v : DoubledSpace H.LimitBase) :
    K.ambientDifferential (complex_i (E := H.LimitBase) v) =
      complex_i (E := H.LimitBase) (K.ambientDifferential v) := by
  rw [← realPhaseAxis_eq_complex_i]
  exact K.ambientDifferential_clockAxis v

/-- The represented finite-mode connection is linear for the native internal
phase axis. -/
theorem representedFiniteModeConnection_isKLinear :
    KLinear (E := H.LimitBase) K.ambientDifferential :=
  K.representedConnection_isHestenesCompatible

/-- Equivalent operator-algebra readout: its phase-axis transport commutator
vanishes. -/
theorem representedFiniteModeConnection_phaseCommutator_eq_zero :
    transportCommutator (E := H.LimitBase) K.ambientDifferential
        (clockAxis (E := H.LimitBase)) = 0 := by
  exact (complexLinear_readback K.ambientDifferential).2
    K.representedConnection_isHestenesCompatible

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeBilingualReadout
