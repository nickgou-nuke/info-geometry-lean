import InfoGeometry.Canonical.PeircePositiveCell

namespace InfoGeometry.Canonical

/-! The identity external-data matrix gives a direct image bridge from the
Peirce flattening to the finite amplituhedron chart. -/

def peirceExternalIdentity :
    Matrix (Fin 4) (Fin 4) ℝ := 1

theorem peirceChannelFlatten_identity_amplituhedronMap
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    amplituhedronMap (k := 1) (n := 4) (m := 4)
        peirceExternalIdentity (peirceChannelFlatten M) =
      peirceChannelFlatten M := by
  simp [amplituhedronMap, peirceExternalIdentity]

theorem peirceChannelFlatten_mem_amplituhedronImage
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M ∈ peircePositiveChannelCell) :
    peirceChannelFlatten M ∈
      amplituhedronImage (k := 1) (n := 4) (m := 4)
        peirceExternalIdentity := by
  rw [← peirceChannelFlatten_identity_amplituhedronMap M]
  apply amplituhedronMap_mem_image
  · exact peircePositiveChannel_mem_grassmannianChart M hM

theorem peirceStrictlyPositiveChannel_mem_amplituhedronImage
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M ∈ peirceStrictlyPositiveChannelCell) :
    peirceChannelFlatten M ∈
      amplituhedronImage (k := 1) (n := 4) (m := 4)
        peirceExternalIdentity := by
  rw [← peirceChannelFlatten_identity_amplituhedronMap M]
  apply amplituhedronMap_mem_image
  exact positiveGrassmannianInterior_subset_chart
    (peirceStrictlyPositiveChannel_mem_grassmannianInterior M hM)

end InfoGeometry.Canonical
