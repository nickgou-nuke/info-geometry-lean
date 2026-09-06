import InfoGeometry.Canonical.G2Cl55FiniteFredholmIndexBridge

noncomputable section

namespace InfoGeometry.Canonical.FiniteCl55GroupEquivariance

open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.Canonical.G2Cl55FiniteHodgeEquivarianceDatum

theorem mulVec_preserves_hodge_kernel
    {G : Type*} [Group G]
    (action : G →* (Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ))ˣ)
    (commutes_hodge : ∀ g,
      (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) * Matrix.mulVecLin embeddedSplitOctonionHodgeDirac =
        Matrix.mulVecLin embeddedSplitOctonionHodgeDirac *
          (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)))
    (g : G) {v : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ}
    (hv : embeddedSplitOctonionHodgeDirac.mulVec v = 0) :
    embeddedSplitOctonionHodgeDirac.mulVec
      ((action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) v) = 0 := by
  have htransport :
      embeddedSplitOctonionHodgeDirac.mulVec
          ((action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) v) =
        (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ))
          (embeddedSplitOctonionHodgeDirac.mulVec v) := by
    change (Matrix.mulVecLin embeddedSplitOctonionHodgeDirac)
          ((action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) v) =
      (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ))
        ((Matrix.mulVecLin embeddedSplitOctonionHodgeDirac) v)
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp,
      ← commutes_hodge g, Module.End.mul_eq_comp, LinearMap.comp_apply]
  rw [htransport, hv, map_zero]

theorem mulVec_preserves_chirality_kernel
    {G : Type*} [Group G]
    (action : G →* (Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ))ˣ)
    (commutes_chirality : ∀ g,
      (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) *
          Matrix.mulVecLin MasterChirality =
        Matrix.mulVecLin MasterChirality *
          (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)))
    (g : G) {v : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ}
    (hv : MasterChirality.mulVec v = 0) :
    MasterChirality.mulVec
      ((action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) v) = 0 := by
  have htransport :
      MasterChirality.mulVec
          ((action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) v) =
        (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ))
          (MasterChirality.mulVec v) := by
    change (Matrix.mulVecLin MasterChirality)
          ((action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) v) =
      (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ))
        ((Matrix.mulVecLin MasterChirality) v)
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp,
      ← commutes_chirality g, Module.End.mul_eq_comp, LinearMap.comp_apply]
  rw [htransport, hv, map_zero]

theorem mulVec_preserves_joint_kernel
    {G : Type*} [Group G]
    (action : G →* (Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ))ˣ)
    (commutes_hodge : ∀ g,
      (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) *
          Matrix.mulVecLin embeddedSplitOctonionHodgeDirac =
        Matrix.mulVecLin embeddedSplitOctonionHodgeDirac *
          (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)))
    (commutes_chirality : ∀ g,
      (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) *
          Matrix.mulVecLin MasterChirality =
        Matrix.mulVecLin MasterChirality *
          (action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)))
    (g : G) {v : InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ}
    (hv : embeddedSplitOctonionHodgeDirac.mulVec v = 0 ∧
      MasterChirality.mulVec v = 0) :
    embeddedSplitOctonionHodgeDirac.mulVec
          ((action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) v) = 0 ∧
      MasterChirality.mulVec
          ((action g : Module.End ℝ (InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ)) v) = 0 := by
  exact ⟨mulVec_preserves_hodge_kernel action commutes_hodge g hv.1,
    mulVec_preserves_chirality_kernel action commutes_chirality g hv.2⟩

end InfoGeometry.Canonical.FiniteCl55GroupEquivariance
