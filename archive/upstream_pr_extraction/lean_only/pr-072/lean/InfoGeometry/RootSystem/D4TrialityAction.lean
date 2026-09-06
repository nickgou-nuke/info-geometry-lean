import InfoGeometry.RootSystem.D4DualTriality

/-!
# Explicit permutation action on the three nonzero `D₄` discriminant classes

The three classes are represented by the first-coordinate, half-coordinate,
and signed-half-coordinate representatives.  Their permutation group acts on
the nonzero quotient classes by conjugation through this explicit equivalence.
This is the finite triality permutation layer; it does not assert that every
permutation has already been identified with a lattice automorphism.
-/

namespace InfoGeometry.RootSystem.D4

abbrev TrialityClass := {x : discriminantCarrier // x ≠ 0}

def trialityRepresentatives (i : Fin 3) : TrialityClass :=
  ⟨discriminantRepresentatives i.succ, by
    fin_cases i
    · exact discriminantMap_firstCoordinate_ne_zero
    · exact discriminantMap_halfCoordinate_ne_zero
    · exact discriminantMap_signedHalfCoordinate_ne_zero⟩

theorem trialityRepresentatives_injective :
    Function.Injective trialityRepresentatives := by
  intro i j h
  have h' : discriminantRepresentatives i.succ =
      discriminantRepresentatives j.succ := by
    simpa [trialityRepresentatives] using congrArg Subtype.val h
  have hs : i.succ = j.succ := discriminantRepresentatives_injective h'
  exact Fin.succ_inj.mp hs

theorem trialityRepresentatives_surjective :
    Function.Surjective trialityRepresentatives := by
  intro x
  obtain ⟨u, hu⟩ := discriminantMap_surjective x.1
  obtain ⟨i, hi⟩ := discriminantMap_eq_one_of_four_representatives u
  have hxi : x.1 = discriminantRepresentatives i := hu.symm.trans hi
  fin_cases i
  · exact False.elim (x.2 hxi)
  · exact ⟨0, Subtype.ext (by simpa [trialityRepresentatives] using hxi.symm)⟩
  · exact ⟨1, Subtype.ext (by simpa [trialityRepresentatives] using hxi.symm)⟩
  · exact ⟨2, Subtype.ext (by simpa [trialityRepresentatives] using hxi.symm)⟩

noncomputable def trialityRepresentativeEquiv :
    Fin 3 ≃ TrialityClass :=
  Equiv.ofBijective trialityRepresentatives
    ⟨trialityRepresentatives_injective, trialityRepresentatives_surjective⟩

noncomputable def trialityAction (σ : Equiv.Perm (Fin 3)) :
    TrialityClass ≃ TrialityClass :=
  trialityRepresentativeEquiv.symm.trans
    (σ.trans trialityRepresentativeEquiv)

theorem trialityAction_apply (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    trialityAction σ (trialityRepresentatives i) =
      trialityRepresentatives (σ i) := by
  simp [trialityAction, trialityRepresentativeEquiv]

theorem trialityAction_one :
    trialityAction (1 : Equiv.Perm (Fin 3)) = Equiv.refl TrialityClass := by
  ext x
  obtain ⟨i, rfl⟩ := trialityRepresentatives_surjective x
  simp [trialityAction_apply]

theorem trialityAction_mul (σ τ : Equiv.Perm (Fin 3)) :
    trialityAction (σ * τ) =
      trialityAction σ * trialityAction τ := by
  ext x
  obtain ⟨i, rfl⟩ := trialityRepresentatives_surjective x
  simp [trialityAction_apply]

noncomputable def trialityActionHom :
    (Equiv.Perm (Fin 3)) →* (Equiv.Perm TrialityClass) where
  toFun := trialityAction
  map_one' := trialityAction_one
  map_mul' := trialityAction_mul

theorem trialityActionHom_apply (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    trialityActionHom σ (trialityRepresentatives i) =
      trialityRepresentatives (σ i) :=
  trialityAction_apply σ i

theorem trialityActionHom_injective :
    Function.Injective trialityActionHom := by
  intro σ τ h
  ext i
  have hi := congrArg (fun g : Equiv.Perm TrialityClass =>
      g (trialityRepresentatives i)) h
  have hi'' : trialityRepresentatives (σ i) =
      trialityRepresentatives (τ i) := by
    simpa [trialityActionHom_apply] using hi
  have hi' : σ i = τ i := trialityRepresentativeEquiv.injective hi''
  exact congrArg Fin.val hi'

end InfoGeometry.RootSystem.D4
