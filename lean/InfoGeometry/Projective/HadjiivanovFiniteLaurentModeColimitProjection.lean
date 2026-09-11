import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.HadjiivanovLogConnectionColimitBridge

/-!
# Colimit projection of the finite Laurent-mode connection tower

This file specializes the existing `ConnectionColimitCone` owner to the
symmetric finite Laurent windows.  The ambient carrier and its cone maps remain
explicit inputs: no completion, universal colimit, convergence, or analytic
connection is constructed here.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeColimitProjection

open HadjiivanovLogConnectionBridge
open HadjiivanovLogConnectionColimitBridge
open HadjiivanovFiniteLaurentModeTower

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The staged carrier underlying the symmetric finite Laurent-mode tower. -/
abbrev LaurentModeTower (V : Type*) (n : ℕ) :=
  FiniteModeSection n V

/-- Package the concrete finite Laurent-mode connection tower as an instance
of the repository's existing colimit-cone contract.

Only the ambient cone and its intertwining law are assumptions.  Compatibility
of successive finite stages is supplied by `finiteModeConnection_modeBond`. -/
def finiteModeConnectionCone
    (R : LogResidue V)
    (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientConnection : A_inf →ₗ[ℂ] A_inf)
    (ambientConnection_comm : ∀ n,
      ambientConnection.comp (psi n) =
        (psi n).comp (finiteModeConnection R n)) :
    ConnectionColimitCone (R := ℂ) (LaurentModeTower V) A_inf where
  iota := modeBond
  psi := psi
  psi_comm := psi_comm
  stageConnection := finiteModeConnection R
  ambientConnection := ambientConnection
  stageConnection_comm := finiteModeConnection_modeBond R
  ambientConnection_comm := ambientConnection_comm

/-- Every finite bonding iterate intertwines the concrete Laurent-mode
connections. -/
theorem finiteModeConnection_iota_seq
    (R : LogResidue V)
    (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientConnection : A_inf →ₗ[ℂ] A_inf)
    (ambientConnection_comm : ∀ n,
      ambientConnection.comp (psi n) =
        (psi n).comp (finiteModeConnection R n))
    (n m : ℕ) :
    (finiteModeConnection R (n + m)).comp
        (iota_seq (LaurentModeTower V) modeBond n m) =
      (iota_seq (LaurentModeTower V) modeBond n m).comp
        (finiteModeConnection R n) := by
  let C := finiteModeConnectionCone R A_inf psi psi_comm
    ambientConnection ambientConnection_comm
  exact ConnectionColimitCone.stageConnection_iota_seq
    (A := LaurentModeTower V) (A_inf := A_inf) C n m

/-- Projection to the supplied ambient carrier commutes with the logarithmic
connection after every finite number of Laurent-window embeddings. -/
theorem ambientConnection_after_finiteModeBond
    (R : LogResidue V)
    (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientConnection : A_inf →ₗ[ℂ] A_inf)
    (ambientConnection_comm : ∀ n,
      ambientConnection.comp (psi n) =
        (psi n).comp (finiteModeConnection R n))
    (n m : ℕ) (x : LaurentModeTower V n) :
    ambientConnection
        (psi (n + m) (iota_seq (LaurentModeTower V) modeBond n m x)) =
      psi n (finiteModeConnection R n x) := by
  let C := finiteModeConnectionCone R A_inf psi psi_comm
    ambientConnection ambientConnection_comm
  exact ConnectionColimitCone.ambientConnection_after_iota_seq
    (A := LaurentModeTower V) (A_inf := A_inf) C n m x

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeColimitProjection
