import InfoGeometry.Clifford.Cl55RealSplitPinVectorReflection

namespace InfoGeometry.Clifford.Clifford55

/-!
# The reflection-generated subgroup of the native split orthogonal group

This owner records the genuine reflection subgroup.  It does not identify it
with the full orthogonal group; that equality is the remaining
Cartan--Dieudonne theorem for the split form.
-/

noncomputable def quadraticReflectionElement
    (v : V55) (hv : Q55 v ≠ 0) : orthogonalGroup55 :=
  orthogonalGroup55FromIsometry (quadraticReflection_isometry v hv)

def quadraticReflectionGeneratorSet : Set orthogonalGroup55 :=
  {g | ∃ (v : V55) (hv : Q55 v ≠ 0),
      g = quadraticReflectionElement v hv}

def quadraticReflectionSubgroup : Subgroup orthogonalGroup55 :=
  Subgroup.closure quadraticReflectionGeneratorSet

theorem quadraticReflectionElement_mem_subgroup
    (v : V55) (hv : Q55 v ≠ 0) :
    quadraticReflectionElement v hv ∈ quadraticReflectionSubgroup := by
  apply Subgroup.subset_closure
  exact ⟨v, hv, rfl⟩

theorem normalizedVectorAction_mem_quadraticReflectionSubgroup
    (v : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v)) :
    realSplitPinOrthogonalAction
        ⟨normalizedVectorUnit v hunit,
          normalizedVectorUnit_mem_realSplitPin v hv hunit⟩ ∈
      quadraticReflectionSubgroup := by
  let g : realSplitPin55 :=
    ⟨normalizedVectorUnit v hunit,
      normalizedVectorUnit_mem_realSplitPin v hv hunit⟩
  have hne : Q55 v ≠ 0 := by
    rcases hv with hv | hv <;> simp [hv]
  have heq : realSplitPinTwistedActionEquiv g =
      quadraticReflection v hne := by
    apply LinearEquiv.ext
    intro x
    apply ι55_injective
    change ι55 (realSplitPinTwistedAction g x) = _
    rw [normalizedVector_action_apply_ι v x hv hunit]
    rw [normalizedVectorReflection_eq_quadraticReflection v hv hunit]
    rfl
  have hgroup : realSplitPinOrthogonalAction g =
      quadraticReflectionElement v hne := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact congrArg (fun f => f x) heq
  rw [show realSplitPinOrthogonalAction
      ⟨normalizedVectorUnit v hunit,
        normalizedVectorUnit_mem_realSplitPin v hv hunit⟩ =
      realSplitPinOrthogonalAction g by rfl, hgroup]
  exact quadraticReflectionElement_mem_subgroup v hne

end InfoGeometry.Clifford.Clifford55
