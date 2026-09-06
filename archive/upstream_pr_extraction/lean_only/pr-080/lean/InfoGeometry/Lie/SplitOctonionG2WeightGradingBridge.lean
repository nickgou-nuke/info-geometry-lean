import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum

/-!
# Weight grading of the native split-octonion derivation algebra

The native derivation owner already supplies a fourteen-dimensional Cartan
eigenbasis.  This bridge packages that proved spectrum as a genuine additive
weight grading: brackets of weight `α` and weight `β` lie in weight `α + β`.

This is the classical Cartan grading actually present in the repository.  It
does not silently identify it with the separate `(ZMod 2)^3` cochain grading
of the octonion basis; such a binary grading transport requires an additional
derivation-level construction.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionG2WeightGradingBridge

open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum

abbrev Der := CanonicalZornCartanAdjointRootDecomposition.Der
abbrev Weight := CanonicalZornCartanAdjointSpectrum.Weight

/-- The native weight component of the split-octonion derivation algebra. -/
def g2WeightComponent (α : Weight) : Submodule ℝ Der :=
  jointEigenspace α

theorem g2WeightComponent_mem_iff (α : Weight) (D : Der) :
    D ∈ g2WeightComponent α ↔
      ∀ k, adCartan k D = (α k) • D :=
  Iff.rfl

theorem rootDerivation_mem_g2WeightComponent (j : Fin 14) :
    rootDerivation j ∈ g2WeightComponent (rootWeight j) := by
  intro k
  exact adCartan_rootDerivation k j

theorem g2Bracket_mem_weight_add
    (α β : Weight) {X Y : Der}
    (hX : X ∈ g2WeightComponent α)
    (hY : Y ∈ g2WeightComponent β) :
    ⁅X, Y⁆ ∈ g2WeightComponent (α + β) := by
  exact lie_mem_jointEigenspace_add α β hX hY

theorem g2Cartan_zero_weight
    (k : SplitOctonionAxialCartanErlangen.TracelessWeight) :
    (SplitOctonionAxialCartanErlangen.axialCartanLieEquiv k : Der) ∈
      g2WeightComponent 0 := by
  exact cartan_mem_jointEigenspace_zero k

theorem g2RootWeightBasis_spans :
    Submodule.span ℝ (Set.range rootDerivationBasis) = ⊤ :=
  rootDerivationBasis_span

theorem g2WeightComponent_additive
    (α β : Weight) :
    ∀ {X Y : Der},
      X ∈ g2WeightComponent α →
      Y ∈ g2WeightComponent β →
      ⁅X, Y⁆ ∈ g2WeightComponent (α + β) := by
  intro X Y hX hY
  exact g2Bracket_mem_weight_add α β hX hY

end InfoGeometry.Lie.SplitOctonionG2WeightGradingBridge
