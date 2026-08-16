import InfoGeometry.Clifford.Cl55WittPinAction
import InfoGeometry.Clifford.Cl55WittPinParity

noncomputable section
namespace InfoGeometry.Clifford.Clifford55

open CliffordAlgebra

theorem lipschitz_units_involute_sign
    {x : (Cl55)ˣ} (hx : x ∈ lipschitzGroup Q55) :
    involute (Q := Q55) (x : Cl55) = (x : Cl55) ∨
      involute (Q := Q55) (x : Cl55) = -(x : Cl55) := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' with
  | mem x hgen =>
      obtain ⟨a, ha⟩ := hgen
      refine Or.inr ?_
      rw [← ha, involute_ι]
  | one =>
      exact Or.inl (by simp)
  | mul x y hx hy ihx ihy =>
      rcases ihx with hx | hx <;> rcases ihy with hy | hy
      · left; change involute ((x : Cl55) * (y : Cl55)) = _
        rw [Units.val_mul, map_mul, hx, hy]
      · right; change involute ((x : Cl55) * (y : Cl55)) = _
        rw [Units.val_mul, map_mul, hx, hy, mul_neg]
      · right; change involute ((x : Cl55) * (y : Cl55)) = _
        rw [Units.val_mul, map_mul, hx, hy, neg_mul]
      · left; change involute ((x : Cl55) * (y : Cl55)) = _
        rw [Units.val_mul, map_mul, hx, hy, neg_mul, mul_neg, neg_neg]
  | inv_mem x hgen =>
      obtain ⟨a, ha⟩ := hgen
      letI : Invertible (ι Q55 a) := by
        rw [ha]
        exact x.invertible
      letI : Invertible (Q55 a) := invertibleOfInvertibleι Q55 a
      refine Or.inr ?_
      simp_rw [← invOf_units x, ← ha, invOf_ι, map_smul, involute_ι]
      simp [smul_neg]

theorem pinToUnits_involute_sign (g : Pin55) :
    involute (Q := Q55) (pinToUnits g : Cl55) =
        (pinToUnits g : Cl55) ∨
      involute (Q := Q55) (pinToUnits g : Cl55) =
        -(pinToUnits g : Cl55) :=
  lipschitz_units_involute_sign (pinGroup.units_mem_lipschitzGroup g.property)

theorem pinTwistedAction_preserves_Q55_all (g : Pin55) (v : V55) :
    Q55 (pinTwistedAction g v) = Q55 v := by
  exact pinTwistedAction_preserves_Q55 g v

def pinIsometryPredicate (g : Pin55) : Prop :=
  ∀ v : V55, Q55 (pinTwistedAction g v) = Q55 v

def pinIsometrySubgroup : Subgroup Pin55 where
  carrier := {g | pinIsometryPredicate g}
  one_mem' := by
    intro v
    rw [pinTwistedAction_one]
    rfl
  mul_mem' := by
    intro g h hg hh v
    rw [pinTwistedAction_mul]
    simpa [LinearMap.comp_apply] using
      (hg (pinTwistedAction h v)).trans (hh v)
  inv_mem' := by
    intro g hg v
    have hcomp := hg (pinTwistedAction g⁻¹ v)
    have hact :
        pinTwistedAction g (pinTwistedAction g⁻¹ v) = v := by
      calc
        pinTwistedAction g (pinTwistedAction g⁻¹ v) =
            ((pinTwistedAction g).comp (pinTwistedAction g⁻¹)) v := rfl
        _ = pinTwistedAction (g * g⁻¹) v := by
          rw [← pinTwistedAction_mul]
        _ = v := by
          rw [mul_inv_cancel, pinTwistedAction_one]
          rfl
    have hleft :
        Q55 (pinTwistedAction g (pinTwistedAction g⁻¹ v)) = Q55 v := by
      rw [hact]
    exact (hleft.symm.trans hcomp).symm

theorem pinIsometrySubgroup_eq_top :
    pinIsometrySubgroup = ⊤ := by
  ext g
  change pinIsometryPredicate g ↔ True
  constructor
  · intro _
    trivial
  · intro _
    exact pinTwistedAction_preserves_Q55_all g

def Pin55Isometric : Subgroup Pin55 :=
  pinIsometrySubgroup

def orthogonalV55Predicate (e : V55 ≃ₗ[ℝ] V55) : Prop :=
  ∀ v : V55, Q55 (e v) = Q55 v

def OrthogonalV55 : Subgroup (V55 ≃ₗ[ℝ] V55) where
  carrier := {e | orthogonalV55Predicate e}
  one_mem' := by
    intro v
    rfl
  mul_mem' := by
    intro e f he hf v
    exact (he (f v)).trans (hf v)
  inv_mem' := by
    intro e he v
    have h := he (e.symm v)
    simpa using h.symm

noncomputable def pinToLinearEquiv :
    Pin55Isometric →* (V55 ≃ₗ[ℝ] V55) :=
  { toFun := fun g => pinTwistedActionEquiv g.1
    map_one' := by
      apply LinearEquiv.ext
      intro v
      change pinTwistedAction (1 : Pin55) v = v
      rw [pinTwistedAction_one]
      rfl
    map_mul' := by
      intro g h
      exact pinTwistedActionEquiv_mul g.1 h.1 }

noncomputable def pinToOrthogonalV55 :
    Pin55Isometric →* OrthogonalV55 :=
  { toFun := fun g =>
      ⟨pinTwistedActionEquiv g.1, g.2⟩
    map_one' := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      change pinTwistedAction (1 : Pin55) v = v
      rw [pinTwistedAction_one]
      rfl
    map_mul' := by
      intro g h
      apply Subtype.ext
      exact pinTwistedActionEquiv_mul g.1 h.1 }

theorem pinToOrthogonalV55_apply (g : Pin55Isometric) (v : V55) :
    (pinToOrthogonalV55 g : V55 ≃ₗ[ℝ] V55) v = pinTwistedAction g.1 v := by
  change pinTwistedActionEquiv g.1 v = pinTwistedAction g.1 v
  rfl

theorem pinToOrthogonalV55_map_mul_apply
    (g h : Pin55Isometric) (v : V55) :
    (pinToOrthogonalV55 (g * h) : V55 ≃ₗ[ℝ] V55) v =
      (pinToOrthogonalV55 g : V55 ≃ₗ[ℝ] V55)
        ((pinToOrthogonalV55 h : V55 ≃ₗ[ℝ] V55) v) := by
  change pinTwistedActionEquiv (g.1 * h.1) v =
    pinTwistedActionEquiv g.1 (pinTwistedActionEquiv h.1 v)
  exact pinTwistedActionEquiv_mul_apply g.1 h.1 v

noncomputable def fNegPinIsometric (i : Fin 5) : Pin55Isometric :=
  ⟨fNegPin i, fun v => pinTwistedAction_f_neg_preserves_Q55 i v⟩

theorem pinToOrthogonalV55_fNegPin
    (i : Fin 5) :
    (pinToOrthogonalV55 (fNegPinIsometric i) : V55 ≃ₗ[ℝ] V55) =
      negativeReflectionLinearEquiv i := by
  apply LinearEquiv.ext
  intro v
  change pinTwistedAction (fNegPin i) v = _
  rw [pinTwistedAction_f_neg_eq_negativeReflection]
  rfl

noncomputable def globalSheetPinIsometric : Pin55Isometric :=
  ⟨globalSheetPin, fun v => pinTwistedAction_globalSheetPin_preserves_Q55 v⟩

theorem pinToOrthogonalV55_globalSheetPin :
    (pinToOrthogonalV55 globalSheetPinIsometric : V55 ≃ₗ[ℝ] V55) =
      globalSheetReflectionLinearEquiv := by
  apply LinearEquiv.ext
  intro v
  change pinTwistedAction globalSheetPin v = _
  rw [pinTwistedAction_globalSheetPin_eq_globalSheetReflection]
  rfl

noncomputable def spinToOrthogonalV55 :
    Spin55 →* OrthogonalV55 :=
  { toFun := fun g =>
      ⟨spinActionIsometryEquiv g, spinAction_preserves_Q55 g⟩
    map_one' := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      change spinActionIsometryEquiv (1 : Spin55) v = v
      rw [spinActionIsometryEquiv_apply]
      change pinTwistedAction (spinToPin (1 : Spin55)) v = v
      have hpin : spinToPin (1 : Spin55) = (1 : Pin55) := rfl
      rw [hpin]
      rw [pinTwistedAction_one]
      rfl
    map_mul' := by
      intro g h
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      exact spinActionIsometryEquiv_mul_apply g h v }

theorem spinToOrthogonalV55_apply (g : Spin55) (v : V55) :
    (spinToOrthogonalV55 g : V55 ≃ₗ[ℝ] V55) v = spinAction g v := by
  change spinActionIsometryEquiv g v = spinAction g v
  rfl

noncomputable def pinToQ55Isometry (g : Pin55Isometric) :
    Q55.IsometryEquiv Q55 :=
  pinTwistedActionIsometryEquiv g.1 g.2

theorem pinToQ55Isometry_apply (g : Pin55Isometric) (v : V55) :
    pinToQ55Isometry g v = pinTwistedAction g.1 v := by
  change pinTwistedActionIsometryEquiv g.1 g.2 v = pinTwistedAction g.1 v
  rfl

theorem pinToQ55Isometry_mul_apply (g h : Pin55Isometric) (v : V55) :
    pinToQ55Isometry (g * h) v =
      pinToQ55Isometry g (pinToQ55Isometry h v) := by
  change pinTwistedAction (g.1 * h.1) v =
    pinTwistedAction g.1 (pinTwistedAction h.1 v)
  rw [pinTwistedAction_mul]
  rfl

end InfoGeometry.Clifford.Clifford55
