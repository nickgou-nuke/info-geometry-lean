import InfoGeometry.Canonical.G2Cl55FiniteFredholmIndexBridge

/-!
# Group-level socket for finite `Cl(5,5)` equivariance

This owner separates the missing integration step from its consequences.  A
supplied group action is represented by a monoid hom into the finite matrix
endomorphisms, together with explicit covariance laws for the Hodge operator
and chirality.  The resulting preservation theorems are unconditional once
those fields are supplied; no split-real `G₂` integration is assumed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteCl55GroupEquivarianceSocket

open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.Canonical.G2Cl55FiniteHodgeEquivarianceDatum

abbrev SpinorCarrier32 := InfoGeometry.Clifford.TowerMatrix.Idx 5 → ℝ
abbrev SpinorEnd32 := Module.End ℝ SpinorCarrier32
abbrev SpinorGL32 := SpinorEnd32ˣ

structure GroupEquivarianceDatum (G : Type*) [Group G] where
  /-- A genuine group action by invertible linear maps, not merely endomorphisms. -/
  action : G →* SpinorGL32
  commutes_hodge : ∀ g,
    (action g : SpinorEnd32) * Matrix.mulVecLin embeddedSplitOctonionHodgeDirac =
      Matrix.mulVecLin embeddedSplitOctonionHodgeDirac * (action g : SpinorEnd32)
  commutes_chirality : ∀ g,
    (action g : SpinorEnd32) * Matrix.mulVecLin MasterChirality =
      Matrix.mulVecLin MasterChirality * (action g : SpinorEnd32)

variable {G : Type*} [Group G]
variable (E : GroupEquivarianceDatum G)

theorem action_preserves_hodge_kernel
    (g : G) {v : SpinorCarrier32}
    (hv : embeddedSplitOctonionHodgeDirac.mulVec v = 0) :
    embeddedSplitOctonionHodgeDirac.mulVec ((E.action g : SpinorEnd32) v) = 0 := by
  have htransport :
      embeddedSplitOctonionHodgeDirac.mulVec ((E.action g : SpinorEnd32) v) =
        (E.action g : SpinorEnd32) (embeddedSplitOctonionHodgeDirac.mulVec v) := by
    change (Matrix.mulVecLin embeddedSplitOctonionHodgeDirac) ((E.action g : SpinorEnd32) v) =
      (E.action g : SpinorEnd32) ((Matrix.mulVecLin embeddedSplitOctonionHodgeDirac) v)
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp,
      ← E.commutes_hodge g, Module.End.mul_eq_comp, LinearMap.comp_apply]
  rw [htransport, hv, map_zero]

theorem action_preserves_hodge_kernel_set
    (g : G) {v : SpinorCarrier32}
    (hv : v ∈ hodgeKernel) :
    (E.action g : SpinorEnd32) v ∈ hodgeKernel := by
  change embeddedSplitOctonionHodgeDirac.mulVec v = 0 at hv
  change embeddedSplitOctonionHodgeDirac.mulVec ((E.action g : SpinorEnd32) v) = 0
  exact action_preserves_hodge_kernel E g hv

/-- The invertibility of the supplied group action upgrades preservation to
    an exact iff for the Hodge kernel. -/
theorem action_preserves_hodge_kernel_iff
    (g : G) (v : SpinorCarrier32) :
    embeddedSplitOctonionHodgeDirac.mulVec ((E.action g : SpinorEnd32) v) = 0 ↔
      embeddedSplitOctonionHodgeDirac.mulVec v = 0 := by
  constructor
  · intro hv
    have hinv := action_preserves_hodge_kernel E g⁻¹ hv
    have hunit :
        (E.action g⁻¹ : SpinorEnd32) * (E.action g : SpinorEnd32) = 1 := by
      rw [← Units.val_mul, E.action.map_inv]
      exact Units.inv_val (E.action g)
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, hunit] at hinv
    simpa using hinv
  · exact action_preserves_hodge_kernel E g

theorem action_preserves_hodge_range
    (g : G) {v : SpinorCarrier32}
    (hv : v ∈ LinearMap.range (Matrix.mulVecLin embeddedSplitOctonionHodgeDirac)) :
    (E.action g : SpinorEnd32) v ∈
      LinearMap.range (Matrix.mulVecLin embeddedSplitOctonionHodgeDirac) := by
  rcases hv with ⟨u, rfl⟩
  refine ⟨(E.action g : SpinorEnd32) u, ?_⟩
  change Matrix.mulVecLin embeddedSplitOctonionHodgeDirac ((E.action g : SpinorEnd32) u) =
    (E.action g : SpinorEnd32) (Matrix.mulVecLin embeddedSplitOctonionHodgeDirac u)
  rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp,
    ← E.commutes_hodge g, Module.End.mul_eq_comp, LinearMap.comp_apply]

theorem action_preserves_chirality_kernel
    (g : G) {v : SpinorCarrier32}
    (hv : MasterChirality.mulVec v = 0) :
    MasterChirality.mulVec ((E.action g : SpinorEnd32) v) = 0 := by
  have htransport :
      MasterChirality.mulVec ((E.action g : SpinorEnd32) v) =
        (E.action g : SpinorEnd32) (MasterChirality.mulVec v) := by
    change (Matrix.mulVecLin MasterChirality) ((E.action g : SpinorEnd32) v) =
      (E.action g : SpinorEnd32) ((Matrix.mulVecLin MasterChirality) v)
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp,
      ← E.commutes_chirality g, Module.End.mul_eq_comp, LinearMap.comp_apply]
  rw [htransport, hv, map_zero]

/-- Invertibility also makes preservation of the chirality kernel an iff. -/
theorem action_preserves_chirality_kernel_iff
    (g : G) (v : SpinorCarrier32) :
    MasterChirality.mulVec ((E.action g : SpinorEnd32) v) = 0 ↔
      MasterChirality.mulVec v = 0 := by
  constructor
  · intro hv
    have hinv := action_preserves_chirality_kernel E g⁻¹ hv
    have hunit :
        (E.action g⁻¹ : SpinorEnd32) * (E.action g : SpinorEnd32) = 1 := by
      rw [← Units.val_mul, E.action.map_inv]
      exact Units.inv_val (E.action g)
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, hunit] at hinv
    simpa using hinv
  · exact action_preserves_chirality_kernel E g

theorem action_preserves_hodge_kernel_trivial :
    ∀ v : SpinorCarrier32,
      embeddedSplitOctonionHodgeDirac.mulVec v = 0 → v = 0 := by
  intro v hv
  exact hodge_kernel_trivial hv

end InfoGeometry.Canonical.FiniteCl55GroupEquivarianceSocket
