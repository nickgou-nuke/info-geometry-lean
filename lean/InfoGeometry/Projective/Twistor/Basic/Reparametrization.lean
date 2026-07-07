import InfoGeometry.Projective.Twistor.Basic.StatisticalFamily

namespace InfoGeometry.Information

open MeasureTheory

/-- Re-indexing a statistical family along a parameter map. -/
noncomputable def reparam
    {α : Type*} [MeasurableSpace α] {Θ Ξ : Type*}
    (family : StatisticalFamily α Θ) (f : Ξ → Θ) : StatisticalFamily α Ξ where
  base := family.base
  model := fun ξ => family.model (f ξ)
  dominated := fun ξ => family.dominated (f ξ)
  decomposition := fun ξ => family.decomposition (f ξ)

lemma dominated_reparam
    {α : Type*} [MeasurableSpace α] {Θ Ξ : Type*}
    (family : StatisticalFamily α Θ) (f : Ξ → Θ) (ξ : Ξ) :
    (reparam family f).model ξ ≪ (reparam family f).base := by
  dsimp [reparam]
  exact family.dominated (f ξ)

end InfoGeometry.Information
