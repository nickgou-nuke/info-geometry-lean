import InfoGeometry.Projective.HadjiivanovLogConnectionColimitBridge
import InfoGeometry.Canonical.FilteredHestenesKreinColimit

/-!
# Hestenes--Krein consumer socket for a colimit logarithmic connection

This final adapter is deliberately conditional.  It requires an explicit
continuous-linear identification of the supplied algebraic ambient carrier
with a doubled Hestenes--Krein limit carrier, together with a continuous
differential representing the ambient connection and a phase-axis
compatibility proof.

Consequently the theorems below transport already proved finite-stage
connection identities into the bilingual Hestenes--Krein formulation.  They
do not construct analytic continuation, horizontal solutions, or holonomy.
-/

namespace InfoGeometry.Projective.HadjiivanovLogConnectionHestenesKreinConsumer

open InfoGeometry.Projective.HadjiivanovLogConnectionColimitBridge
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Krein

noncomputable section

variable (A : ℕ → Type*) [∀ n, AddCommGroup (A n)] [∀ n, Module ℝ (A n)]
variable (A_inf : Type*) [NormedAddCommGroup A_inf] [NormedSpace ℝ A_inf]

/-- Explicit typed ownership contract for the analytic Hestenes--Krein
consumer of an algebraic connection colimit cone. -/
structure HestenesKreinConnectionConsumer
    (C : ConnectionColimitCone (R := ℝ) A A_inf)
    (H : HestenesKreinCone) where
  identify : A_inf ≃L[ℝ] DoubledSpace H.LimitBase
  ambientDifferential :
    DoubledSpace H.LimitBase →L[ℝ] DoubledSpace H.LimitBase
  identifiesConnection : ∀ x,
    ambientDifferential (identify x) = identify (C.ambientConnection x)
  hestenesCompatible :
    IsHestenesHolomorphicDifferential
      (E := H.LimitBase) (F := H.LimitBase) ambientDifferential

namespace HestenesKreinConnectionConsumer

variable {A A_inf}
variable {C : ConnectionColimitCone (R := ℝ) A A_inf}
variable {H : HestenesKreinCone}
variable (K : HestenesKreinConnectionConsumer A A_inf C H)

/-- The represented ambient connection commutes with the Hestenes clock axis. -/
theorem ambientDifferential_clockAxis (v : DoubledSpace H.LimitBase) :
    K.ambientDifferential (clockAxis (E := H.LimitBase) v) =
      clockAxis (E := H.LimitBase) (K.ambientDifferential v) := by
  have hcompat := K.hestenesCompatible
  unfold IsHestenesHolomorphicDifferential at hcompat
  have h := congrArg
    (fun D : DoubledSpace H.LimitBase →L[ℝ] DoubledSpace H.LimitBase => D v)
    hcompat
  exact h

/-- Finite-stage connection application, after arbitrary bonding iterations,
has the same represented Hestenes--Krein ambient value. -/
theorem representedConnection_after_iota_seq
    (n m : ℕ) (x : A n) :
    K.ambientDifferential
        (K.identify
          (C.psi (n + m) (iota_seq A C.iota n m x))) =
      K.identify (C.psi n (C.stageConnection n x)) := by
  rw [K.identifiesConnection]
  rw [C.ambientConnection_after_iota_seq]

/-- The analytic word used here means exactly native Hestenes phase-axis
compatibility of the supplied continuous differential. -/
theorem representedConnection_isHestenesCompatible :
    IsHestenesHolomorphicDifferential
      (E := H.LimitBase) (F := H.LimitBase) K.ambientDifferential :=
  K.hestenesCompatible

end HestenesKreinConnectionConsumer

end

end InfoGeometry.Projective.HadjiivanovLogConnectionHestenesKreinConsumer
