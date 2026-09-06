import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeMonodromyColimitProjection

/-!
# Generation closure for ambient finite-mode operators

The previous ambient commutation theorem is intentionally restricted to the
union of finite-stage images.  This owner records the exact additional
algebraic hypothesis under which that union is the whole ambient carrier and
then promotes commutation globally.

The hypothesis is explicit surjective generation, not density, completion, or
an analytic limiting argument.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeGenerationClosure

open HadjiivanovLogConnectionBridge
open HadjiivanovFiniteLaurentModeTower
open HadjiivanovFiniteLaurentModeColimitProjection
open HadjiivanovFiniteLaurentModeMonodromyReadout
open HadjiivanovFiniteLaurentModeMonodromyColimitProjection

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Every ambient vector is represented by some finite symmetric Laurent
window.  This is stronger than density and is never inferred automatically. -/
def FiniteModeImagesGenerate
    (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
    (psi : ∀ n, LaurentModeTower V n →ₗ[ℂ] A_inf) : Prop :=
  ∀ y : A_inf, ∃ n : ℕ, ∃ x : LaurentModeTower V n, psi n x = y

/-- Explicit finite-image generation promotes connection--monodromy
commutation from cone representatives to the entire ambient carrier. -/
theorem ambientConnection_monodromy_commute
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
    (hGenerate : FiniteModeImagesGenerate A_inf psi) :
    ambientConnection.comp ambientMonodromy =
      ambientMonodromy.comp ambientConnection := by
  apply LinearMap.ext
  intro y
  rcases hGenerate y with ⟨n, x, rfl⟩
  change ambientConnection (ambientMonodromy (psi n x)) =
    ambientMonodromy (ambientConnection (psi n x))
  simpa [iota_seq] using
    (ambientConnection_monodromy_commute_on_finiteImage R A_inf psi psi_comm
      ambientConnection ambientMonodromy ambientConnection_comm
      ambientMonodromy_comm n 0 x)

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeGenerationClosure
