import InfoGeometry.Topology.KleinBottleOrbitQuotient

noncomputable section

namespace InfoGeometry.Topology.KleinGlideSeamDescent

open KleinBrillouinBase KleinBottleOrbitQuotient

theorem continuous_descent_iff (field : C(BrillouinTorus, ℝ)) :
    (∃! descended : C(KleinBrillouinQuotient, ℝ),
      ∀ point, descended (quotientMap point) = field point) ↔
      ∀ point, field (torusGlide point) = field point := by
  constructor
  · rintro ⟨descended, evaluation, _⟩ point
    rw [← evaluation, quotientMap_glide, evaluation]
  · intro invariant
    have respects : ∀ first second, glideSetoid.r first second →
        field first = field second := by
      intro first second related
      rcases related with rfl | related
      · rfl
      · rw [related, invariant]
    let descended : C(KleinBrillouinQuotient, ℝ) :=
      ⟨Quotient.lift field respects, field.continuous.quotient_lift respects⟩
    refine ⟨descended, fun _ => rfl, ?_⟩
    intro candidate evaluation
    apply ContinuousMap.ext
    intro point
    obtain ⟨representative, rfl⟩ := quotientMap_surjective point
    exact evaluation representative

theorem seam_matching (field : C(BrillouinTorus, ℝ))
    (invariant : ∀ point, field (torusGlide point) = field point)
    (coordinate : MomentumCircle) :
    field (coordinate + (Real.pi : MomentumCircle), 0) = field (coordinate, 0) := by
  simpa only [torusGlide, neg_zero] using invariant (coordinate, 0)

theorem seam_points_identified (coordinate : MomentumCircle) :
    quotientMap (coordinate + (Real.pi : MomentumCircle), 0) =
      quotientMap (coordinate, 0) := by
  simpa only [torusGlide, neg_zero] using quotientMap_glide (coordinate, 0)

theorem seam_points_distinct (coordinate : MomentumCircle) :
    (coordinate + (Real.pi : MomentumCircle), (0 : MomentumCircle)) ≠
      (coordinate, 0) := by
  simpa only [torusGlide, neg_zero] using torusGlide_ne_self (coordinate, 0)

def symmetricField (field : C(BrillouinTorus, ℝ)) : C(BrillouinTorus, ℝ) where
  toFun point := field point + field (torusGlide point)
  continuous_toFun := field.continuous.add (field.continuous.comp torusGlide_continuous)

theorem symmetricField_invariant (field : C(BrillouinTorus, ℝ))
    (point : BrillouinTorus) :
    symmetricField field (torusGlide point) = symmetricField field point := by
  change field (torusGlide point) + field (torusGlide (torusGlide point)) =
    field point + field (torusGlide point)
  rw [torusGlide_involutive, add_comm]

theorem symmetricField_descends (field : C(BrillouinTorus, ℝ)) :
    ∃! descended : C(KleinBrillouinQuotient, ℝ),
      ∀ point, descended (quotientMap point) =
        field point + field (torusGlide point) := by
  exact (continuous_descent_iff (symmetricField field)).mpr
    (symmetricField_invariant field)

theorem odd_scalar_descent_forces_zero (field : C(BrillouinTorus, ℝ))
    (odd : ∀ point, field (torusGlide point) = -field point)
    (descended : C(KleinBrillouinQuotient, ℝ))
    (evaluation : ∀ point, descended (quotientMap point) = field point)
    (point : BrillouinTorus) : field point = 0 := by
  have invariant : field (torusGlide point) = field point := by
    rw [← evaluation, quotientMap_glide, evaluation]
  have sign := odd point
  linarith

end InfoGeometry.Topology.KleinGlideSeamDescent
