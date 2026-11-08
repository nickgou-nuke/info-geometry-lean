import InfoGeometry.Clifford.Cl55WittPinProjectiveNullAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittPinParity

namespace InfoGeometry.Clifford.Clifford55

/-!
# Projective parity bridge for the native `Pin(5,5)` action

The ordinary and twisted Pin actions differ by the Clifford parity sign on
odd units.  Projectivization removes that sign, so both actions induce the
same action on projective rays.  This file records that consequence without
identifying the two linear actions.
-/

noncomputable section

open InfoGeometry.Canonical.ProjectiveFoundation
open InfoGeometry.Canonical.Cl55ProjectiveBoundary
open scoped LinearAlgebra.Projectivization

noncomputable def pinTwistedV55LinearAction :
    Pin55 →* (V55 ≃ₗ[ℝ] V55) where
  toFun := pinTwistedActionEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change pinTwistedAction (1 : Pin55) v = v
    rw [pinTwistedAction_one]
    rfl
  map_mul' := by
    intro g h
    exact pinTwistedActionEquiv_mul g h

noncomputable def pinTwistedProjectiveRepresentation :
    ProjectiveRepresentation ℝ Pin55 V55 :=
  ProjectiveRepresentation.ofLinearHom pinTwistedV55LinearAction

theorem pin_projective_representations_agree_on_rays
    (g : Pin55) (p : ℙ ℝ V55) :
    pinTwistedProjectiveRepresentation.projectivizationMap g p =
      pinProjectiveRepresentation.projectivizationMap g p := by
  induction p using Projectivization.ind with
  | h v hv =>
      rw [ProjectiveRepresentation.projectivizationMap_mk,
        ProjectiveRepresentation.projectivizationMap_mk]
      change Projectivization.mk ℝ (pinTwistedActionEquiv g v) _ =
        Projectivization.mk ℝ (pinConjActionEquiv g v) _
      change Projectivization.mk ℝ (pinTwistedAction g v) _ =
        Projectivization.mk ℝ (pinConjAction g v) _
      have hparity := lipschitzUnit_involute_eq_or_neg
        (pinToUnits g) (pin_units_mem_lipschitz g)
      rcases hparity with hplus | hminus
      · apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
        refine ⟨Units.mk0 (1 : ℝ) (by norm_num), ?_⟩
        simpa using congrArg (fun f => f v)
          (pinTwistedAction_eq_pinConjAction_of_involute_eq g hplus).symm
      · apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
        refine ⟨Units.mk0 (-1 : ℝ) (by norm_num), ?_⟩
        simpa using congrArg (fun f => f v)
          (pinTwistedAction_eq_neg_pinConjAction_of_involute_eq_neg g hminus).symm

theorem pin_projective_actions_agree :
    pinTwistedProjectiveRepresentation.projectivizationAction =
      pinProjectiveRepresentation.projectivizationAction := by
  apply MonoidHom.ext
  intro g
  funext p
  exact pin_projective_representations_agree_on_rays g p

theorem pinTwistedProjectivization_preserves_null
    (g : Pin55) (p : ℙ ℝ V55)
    (hp : IsProjectiveNull Q55 p) :
    IsProjectiveNull Q55
      (pinTwistedProjectiveRepresentation.projectivizationMap g p) := by
  rw [pin_projective_representations_agree_on_rays]
  exact pinProjectivization_preserves_null g p hp

end

end InfoGeometry.Clifford.Clifford55
