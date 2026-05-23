import InfoGeometry.Projective.Projective

namespace InfoGeometry.PositiveMeasure

lemma SameRay.refl (μ : PositiveMeasure α ℝ) : SameRay μ μ :=
  InfoGeometry.PositiveMeasure.PositiveMeasure.SameRay.refl μ

lemma SameRay.symm {μ ν : PositiveMeasure α ℝ} (h : SameRay μ ν) : SameRay ν μ :=
  InfoGeometry.PositiveMeasure.PositiveMeasure.SameRay.symm h

lemma SameRay.trans {μ ν κ : PositiveMeasure α ℝ}
    (h₁ : SameRay μ ν) (h₂ : SameRay ν κ) : SameRay μ κ :=
  InfoGeometry.PositiveMeasure.PositiveMeasure.SameRay.trans h₁ h₂

end InfoGeometry.PositiveMeasure

namespace InfoGeometry.Projective

lemma same_ray_refl (μ : PositiveMeasure α ℝ) : PositiveMeasure.SameRay μ μ :=
  InfoGeometry.PositiveMeasure.Projective.same_ray_refl μ

lemma same_ray_symm {μ ν : PositiveMeasure α ℝ} (h : PositiveMeasure.SameRay μ ν) :
    PositiveMeasure.SameRay ν μ :=
  InfoGeometry.PositiveMeasure.Projective.same_ray_symm h

lemma same_ray_trans {μ ν κ : PositiveMeasure α ℝ}
    (h₁ : PositiveMeasure.SameRay μ ν) (h₂ : PositiveMeasure.SameRay ν κ) :
    PositiveMeasure.SameRay μ κ :=
  InfoGeometry.PositiveMeasure.Projective.same_ray_trans h₁ h₂

end InfoGeometry.Projective
