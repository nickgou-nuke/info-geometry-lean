import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeColimitProjection
import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeMonodromyReadout

/-!
# Ambient projection of the finite-mode Hadjiivanov readout

An explicitly supplied ambient monodromy readout is packaged using the same
`ConnectionColimitCone` infrastructure as the logarithmic connection.  Its
compatibility with finite cone maps implies representative-independent ambient
readout.  Together with the connection cone, the two ambient operators commute
on every finite-stage image.

No universal, completed, topological, or analytic colimit is constructed.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeMonodromyColimitProjection

open HadjiivanovLogConnectionBridge
open HadjiivanovLogConnectionColimitBridge
open HadjiivanovFiniteLaurentModeTower
open HadjiivanovFiniteLaurentModeColimitProjection
open HadjiivanovFiniteLaurentModeMonodromyReadout

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Package the finite-mode Hadjiivanov readouts and an explicit ambient
readout as the existing colimit-cone operator contract. -/
def finiteModeMonodromyCone
    (R : LogResidue V)
    (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientMonodromy : A_inf →ₗ[ℂ] A_inf)
    (ambientMonodromy_comm : ∀ n,
      ambientMonodromy.comp (psi n) =
        (psi n).comp (finiteModeMonodromyReadout R n)) :
    ConnectionColimitCone (R := ℂ) (LaurentModeTower V) A_inf where
  iota := modeBond
  psi := psi
  psi_comm := psi_comm
  stageConnection := finiteModeMonodromyReadout R
  ambientConnection := ambientMonodromy
  stageConnection_comm := finiteModeMonodromyReadout_modeBond R
  ambientConnection_comm := ambientMonodromy_comm

/-- Ambient monodromy readout is independent of every later finite-stage
representative selected by the bonding maps. -/
theorem ambientMonodromy_after_finiteModeBond
    (R : LogResidue V)
    (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientMonodromy : A_inf →ₗ[ℂ] A_inf)
    (ambientMonodromy_comm : ∀ n,
      ambientMonodromy.comp (psi n) =
        (psi n).comp (finiteModeMonodromyReadout R n))
    (n m : ℕ) (x : LaurentModeTower V n) :
    ambientMonodromy
        (psi (n + m) (iota_seq (LaurentModeTower V) modeBond n m x)) =
      psi n (finiteModeMonodromyReadout R n x) := by
  let C := finiteModeMonodromyCone R A_inf psi psi_comm
    ambientMonodromy ambientMonodromy_comm
  exact ConnectionColimitCone.ambientConnection_after_iota_seq
    (A := LaurentModeTower V) (A_inf := A_inf) C n m x

/-- The ambient logarithmic connection and ambient Hadjiivanov readout commute
on every element represented at a finite Laurent stage. -/
theorem ambientConnection_monodromy_commute_on_finiteImage
    (R : LogResidue V)
    (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (modeBond n) = psi n)
    (ambientConnection ambientMonodromy : A_inf →ₗ[ℂ] A_inf)
    (ambientConnection_comm : ∀ n,
      ambientConnection.comp (psi n) =
        (psi n).comp (finiteModeConnection R n))
    (ambientMonodromy_comm : ∀ n,
      ambientMonodromy.comp (psi n) =
        (psi n).comp (finiteModeMonodromyReadout R n))
    (n m : ℕ) (x : LaurentModeTower V n) :
    ambientConnection
        (ambientMonodromy
          (psi (n + m) (iota_seq (LaurentModeTower V) modeBond n m x))) =
      ambientMonodromy
        (ambientConnection
          (psi (n + m) (iota_seq (LaurentModeTower V) modeBond n m x))) := by
  rw [ambientMonodromy_after_finiteModeBond R A_inf psi psi_comm
    ambientMonodromy ambientMonodromy_comm]
  have hConnection := ambientConnection_after_finiteModeBond R A_inf psi psi_comm
    ambientConnection ambientConnection_comm n m x
  rw [hConnection]
  have hConnectionAtStage := LinearMap.congr_fun (ambientConnection_comm n)
    (finiteModeMonodromyReadout R n x)
  have hMonodromyAtStage := LinearMap.congr_fun (ambientMonodromy_comm n)
    (finiteModeConnection R n x)
  change ambientConnection
      (psi n (finiteModeMonodromyReadout R n x)) =
    psi n (finiteModeConnection R n (finiteModeMonodromyReadout R n x))
      at hConnectionAtStage
  change ambientMonodromy
      (psi n (finiteModeConnection R n x)) =
    psi n (finiteModeMonodromyReadout R n (finiteModeConnection R n x))
      at hMonodromyAtStage
  rw [hConnectionAtStage, hMonodromyAtStage]
  exact congrArg (psi n)
    (LinearMap.congr_fun (finiteModeConnection_monodromyReadout R n) x)

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeMonodromyColimitProjection
