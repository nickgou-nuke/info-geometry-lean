import InfoGeometry.Canonical.BCFWMeromorphicResidueRecursion

namespace InfoGeometry.Topology.BCFWMeromorphic

open InfoGeometry.Canonical

noncomputable section

def poleComplement {I : Type*} (z_star : I → ℂ) : Set ℂ :=
  {z | ∀ i, z ≠ z_star i}

theorem isOpen_poleComplement
    {I : Type*} [Fintype I] (z_star : I → ℂ) :
    IsOpen (poleComplement z_star) := by
  unfold poleComplement
  rw [show {z : ℂ | ∀ i, z ≠ z_star i} =
      ⋂ i : I, ({z_star i} : Set ℂ)ᶜ by
    ext z
    simp]
  apply isOpen_iInter_of_finite
  intro i
  exact isClosed_singleton.isOpen_compl

theorem continuousOn_algebraicAmplitude
    {I : Type*} [Fintype I]
    (c z_star : I → ℂ) :
    ContinuousOn (algebraicAmplitude c z_star) (poleComplement z_star) := by
  unfold algebraicAmplitude poleComplement
  apply continuousOn_finset_sum
  intro i hi
  apply ContinuousOn.div continuousOn_const
    (continuousOn_id.sub continuousOn_const)
  intro z hz
  exact sub_ne_zero.mpr (hz i)

end

end InfoGeometry.Topology.BCFWMeromorphic
