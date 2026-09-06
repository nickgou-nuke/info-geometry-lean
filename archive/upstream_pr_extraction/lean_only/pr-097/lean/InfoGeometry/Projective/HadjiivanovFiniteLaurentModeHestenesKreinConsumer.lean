import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeRealification
import InfoGeometry.Projective.HadjiivanovLogConnectionHestenesKreinConsumer

/-!
# Hestenes--Krein consumer for the finite Laurent-mode tower

This owner specializes the existing conditional Hestenes--Krein consumer to
the realification of the finite Laurent-mode connection cone.  All normed,
continuous, and phase-axis data remain explicit witnesses.  No completion,
analytic continuation, horizontal solution, or holonomy is inferred.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeHestenesKreinConsumer

open HadjiivanovLogConnectionBridge
open HadjiivanovLogConnectionColimitBridge
open HadjiivanovLogConnectionHestenesKreinConsumer
open HadjiivanovFiniteLaurentModeTower
open HadjiivanovFiniteLaurentModeColimitProjection
open HadjiivanovFiniteLaurentModeRealification
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Krein

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {A_inf : Type*} [NormedAddCommGroup A_inf] [NormedSpace ℂ A_inf]

/-- The real-linear successor map consumed by the Hestenes--Krein layer. -/
def realModeBond (n : ℕ) :
    LaurentModeTower V n →ₗ[ℝ] LaurentModeTower V (n + 1) :=
  (modeBond n).restrictScalars ℝ

@[simp] theorem realModeBond_apply
    (n : ℕ) (x : LaurentModeTower V n) :
    realModeBond n x = modeBond n x := rfl

/-- Build the existing Hestenes--Krein consumer on the concrete realified
finite Laurent-mode connection cone. -/
def finiteModeHestenesKreinConsumer
    (R : LogResidue V)
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientConnection : A_inf →ₗ[ℂ] A_inf)
    (ambientConnection_comm : ∀ n,
      ambientConnection.comp (psi n) =
        (psi n).comp (finiteModeConnection R n))
    (H : HestenesKreinCone)
    (identify : A_inf ≃L[ℝ] DoubledSpace H.LimitBase)
    (ambientDifferential :
      DoubledSpace H.LimitBase →L[ℝ] DoubledSpace H.LimitBase)
    (identifiesConnection : ∀ x,
      ambientDifferential (identify x) = identify (ambientConnection x))
    (hestenesCompatible :
      IsHestenesHolomorphicDifferential
        (E := H.LimitBase) (F := H.LimitBase) ambientDifferential) :
    HestenesKreinConnectionConsumer
      (LaurentModeTower V) A_inf
      (realifiedFiniteModeConnectionCone R A_inf psi psi_comm
        ambientConnection ambientConnection_comm) H where
  identify := identify
  ambientDifferential := ambientDifferential
  identifiesConnection := identifiesConnection
  hestenesCompatible := hestenesCompatible

/-- After any finite number of Laurent-window embeddings, the represented
connection has the same value in the supplied Hestenes--Krein carrier. -/
theorem representedFiniteModeConnection_after_iota_seq
    (R : LogResidue V)
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientConnection : A_inf →ₗ[ℂ] A_inf)
    (ambientConnection_comm : ∀ n,
      ambientConnection.comp (psi n) =
        (psi n).comp (finiteModeConnection R n))
    (H : HestenesKreinCone)
    (K : HestenesKreinConnectionConsumer
      (LaurentModeTower V) A_inf
      (realifiedFiniteModeConnectionCone R A_inf psi psi_comm
        ambientConnection ambientConnection_comm) H)
    (n m : ℕ) (x : LaurentModeTower V n) :
    K.ambientDifferential
        (K.identify
          (psi (n + m)
            (iota_seq (LaurentModeTower V) realModeBond n m x))) =
      K.identify (psi n (finiteModeConnection R n x)) := by
  exact K.representedConnection_after_iota_seq n m x

/-- The represented differential commutes with the native doubled Hestenes
clock axis. -/
theorem representedFiniteModeConnection_clockAxis
    (R : LogResidue V)
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientConnection : A_inf →ₗ[ℂ] A_inf)
    (ambientConnection_comm : ∀ n,
      ambientConnection.comp (psi n) =
        (psi n).comp (finiteModeConnection R n))
    (H : HestenesKreinCone)
    (K : HestenesKreinConnectionConsumer
      (LaurentModeTower V) A_inf
      (realifiedFiniteModeConnectionCone R A_inf psi psi_comm
        ambientConnection ambientConnection_comm) H)
    (v : DoubledSpace H.LimitBase) :
    K.ambientDifferential (clockAxis (E := H.LimitBase) v) =
      clockAxis (E := H.LimitBase) (K.ambientDifferential v) :=
  K.ambientDifferential_clockAxis v

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeHestenesKreinConsumer
