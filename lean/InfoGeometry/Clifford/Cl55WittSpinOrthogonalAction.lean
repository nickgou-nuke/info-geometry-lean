import InfoGeometry.Clifford.Cl55WittPinAction
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

noncomputable def fNegPinTwistedOrthogonal (i : Fin 5) : orthogonalGroup55 :=
  ⟨pinTwistedActionEquiv (fNegPin i), by
    rw [pinTwistedActionEquiv_fNegPin_eq_negativeReflection]
    exact negativeReflection_preserves_Q55 i⟩

theorem fNegPinTwistedOrthogonal_eq_coordinateReflection (i : Fin 5) :
    fNegPinTwistedOrthogonal i = coordinateReflectionGenerator i := by
  apply Subtype.ext
  exact pinTwistedActionEquiv_fNegPin_eq_negativeReflection i

noncomputable def globalSheetPinTwistedOrthogonal : orthogonalGroup55 :=
  ⟨pinTwistedActionEquiv globalSheetPin, by
    rw [pinTwistedActionEquiv_globalSheetPin_eq_globalSheetReflection]
    exact globalSheetReflection_preserves_Q55⟩

theorem globalSheetPinTwistedOrthogonal_eq_coordinateReflection :
    globalSheetPinTwistedOrthogonal = globalSheetReflectionGenerator := by
  apply Subtype.ext
  exact pinTwistedActionEquiv_globalSheetPin_eq_globalSheetReflection

noncomputable def spinActionOrthogonalHom : Spin55 →* orthogonalGroup55 where
  toFun := spinActionOrthogonal
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change pinTwistedActionEquiv (spinToPin (1 : Spin55)) v = v
    rw [show spinToPin (1 : Spin55) = 1 by rfl]
    change pinTwistedAction (1 : Pin55) v = v
    rw [pinTwistedAction_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change pinTwistedActionEquiv (spinToPin (g * h)) v =
      (pinTwistedActionEquiv (spinToPin g) *
        pinTwistedActionEquiv (spinToPin h)) v
    rw [show spinToPin (g * h) = spinToPin g * spinToPin h by rfl]
    exact pinTwistedActionEquiv_mul_apply (spinToPin g) (spinToPin h) v

end InfoGeometry.Clifford.Clifford55
