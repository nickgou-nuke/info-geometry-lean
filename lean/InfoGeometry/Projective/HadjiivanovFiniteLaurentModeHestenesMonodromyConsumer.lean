import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeHestenesKreinConsumer
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeMonodromyColimitProjection

/-!
# Hestenes representation of the ambient finite-mode monodromy readout

The ambient connection and ambient Hadjiivanov readout are represented on one
explicit doubled Hestenes--Krein carrier.  Their finite-image commutation is
transported through the supplied continuous-linear identification.  No claim
is made outside the finite-stage image without an additional generation or
density theorem.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeHestenesMonodromyConsumer

open HadjiivanovLogConnectionBridge
open HadjiivanovLogConnectionHestenesKreinConsumer
open HadjiivanovFiniteLaurentModeTower
open HadjiivanovFiniteLaurentModeColimitProjection
open HadjiivanovFiniteLaurentModeRealification
open HadjiivanovFiniteLaurentModeHestenesKreinConsumer
open HadjiivanovFiniteLaurentModeMonodromyReadout
open HadjiivanovFiniteLaurentModeMonodromyColimitProjection
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Krein

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {A_inf : Type*} [NormedAddCommGroup A_inf] [NormedSpace ℂ A_inf]

/-- Additional data representing the ambient Hadjiivanov readout on the same
Hestenes--Krein carrier as the logarithmic connection. -/
structure FiniteModeHestenesMonodromyConsumer
    (R : LogResidue V)
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientConnection ambientMonodromy : A_inf →ₗ[ℂ] A_inf)
    (ambientConnection_comm : ∀ n,
      ambientConnection.comp (psi n) =
        (psi n).comp (finiteModeConnection R n))
    (H : HestenesKreinCone)
    (K : HestenesKreinConnectionConsumer
      (LaurentModeTower V) A_inf
      (realifiedFiniteModeConnectionCone R A_inf psi psi_comm
        ambientConnection ambientConnection_comm) H) where
  monodromyDifferential :
    DoubledSpace H.LimitBase →L[ℝ] DoubledSpace H.LimitBase
  identifiesMonodromy : ∀ x,
    monodromyDifferential (K.identify x) = K.identify (ambientMonodromy x)
  hestenesCompatible :
    IsHestenesHolomorphicDifferential
      (E := H.LimitBase) (F := H.LimitBase) monodromyDifferential

namespace FiniteModeHestenesMonodromyConsumer

variable (R : LogResidue V)
variable (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
variable (ambientConnection ambientMonodromy : A_inf →ₗ[ℂ] A_inf)
variable (ambientConnection_comm : ∀ n,
  ambientConnection.comp (psi n) =
    (psi n).comp (finiteModeConnection R n))
variable (H : HestenesKreinCone)
variable (K : HestenesKreinConnectionConsumer
  (LaurentModeTower V) A_inf
  (realifiedFiniteModeConnectionCone R A_inf psi psi_comm
    ambientConnection ambientConnection_comm) H)
variable (M : FiniteModeHestenesMonodromyConsumer R psi psi_comm
  ambientConnection ambientMonodromy ambientConnection_comm H K)

/-- The represented monodromy readout commutes with the doubled Hestenes phase
axis. -/
theorem monodromyDifferential_clockAxis (v : DoubledSpace H.LimitBase) :
    M.monodromyDifferential (clockAxis (E := H.LimitBase) v) =
      clockAxis (E := H.LimitBase) (M.monodromyDifferential v) := by
  have h := congrArg
    (fun D : DoubledSpace H.LimitBase →L[ℝ] DoubledSpace H.LimitBase => D v)
    M.hestenesCompatible
  exact h

/-- The represented logarithmic connection and represented monodromy readout
commute on every vector coming from a finite Laurent stage. -/
theorem representedConnection_monodromy_commute_on_finiteImage
    (ambientMonodromy_comm : ∀ n,
      ambientMonodromy.comp (psi n) =
        (psi n).comp (finiteModeMonodromyReadout R n))
    (n m : ℕ) (x : LaurentModeTower V n) :
    K.ambientDifferential
        (M.monodromyDifferential
          (K.identify
            (psi (n + m)
              (iota_seq (LaurentModeTower V) modeBond n m x)))) =
      M.monodromyDifferential
        (K.ambientDifferential
          (K.identify
            (psi (n + m)
              (iota_seq (LaurentModeTower V) modeBond n m x)))) := by
  rw [M.identifiesMonodromy, K.identifiesConnection,
    K.identifiesConnection, M.identifiesMonodromy]
  exact congrArg K.identify
    (ambientConnection_monodromy_commute_on_finiteImage R A_inf psi psi_comm
      ambientConnection ambientMonodromy ambientConnection_comm
      ambientMonodromy_comm n m x)

end FiniteModeHestenesMonodromyConsumer

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeHestenesMonodromyConsumer
