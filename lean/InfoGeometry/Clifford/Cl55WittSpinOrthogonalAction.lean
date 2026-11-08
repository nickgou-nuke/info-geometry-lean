import InfoGeometry.Clifford.Cl55WittPinAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittPinOrthogonalAction
import InfoGeometry.Clifford.Cl55WittReflectionSubgroup

namespace InfoGeometry.Clifford.Clifford55

/-!
# Spin action on the native Witt orthogonal group

This owner packages the already proved spinor twisted action as an element of
the native orthogonal subgroup.  It does not assert surjectivity onto the
full orthogonal group or identify a Pin cover.
-/

noncomputable def spinActionOrthogonal (g : Spin55) : orthogonalGroup55 :=
  ⟨pinTwistedActionEquiv (spinToPin g), by
    intro v
    exact spinAction_preserves_Q55 g v⟩

theorem spinActionOrthogonal_apply (g : Spin55) (v : V55) :
    (spinActionOrthogonal g : V55 ≃ₗ[ℝ] V55) v = spinAction g v := by
  rfl

theorem spinActionOrthogonal_preserves_Q55 (g : Spin55) (v : V55) :
    Q55 ((spinActionOrthogonal g : V55 ≃ₗ[ℝ] V55) v) = Q55 v := by
  exact (spinActionOrthogonal g).property v

theorem spinActionOrthogonal_eq_pinOrthogonalAction (g : Spin55) :
    spinActionOrthogonal g = pinOrthogonalAction (spinToPin g) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply ι55_injective
  change ι55 (pinTwistedAction (spinToPin g) v) =
    ι55 (pinConjAction (spinToPin g) v)
  rw [pinTwistedAction_apply_ι, pinConjAction_apply_ι]
  have hu : pinToUnits (spinToPin g) = spinGroup.toUnits g := by
    apply Units.ext
    rfl
  have hinv :
      CliffordAlgebra.involute (spinGroup.toUnits g : Cl55) =
        (spinGroup.toUnits g : Cl55) := by
    simpa using (spinGroup.involute_eq g.property)
  simpa only [pinTwistedAdj, hu, hinv]

noncomputable def spinActionOrthogonalHom : Spin55 →* orthogonalGroup55 :=
  pinOrthogonalAction.comp spinToPinHom

theorem spinActionOrthogonalHom_eq_pinOrthogonalAction_comp :
    spinActionOrthogonalHom =
      pinOrthogonalAction.comp spinToPinHom :=
  rfl

theorem spinActionOrthogonalHom_apply (g : Spin55) :
    spinActionOrthogonalHom g = spinActionOrthogonal g := by
  rw [spinActionOrthogonal_eq_pinOrthogonalAction]
  rfl

end InfoGeometry.Clifford.Clifford55
