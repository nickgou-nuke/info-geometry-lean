import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Canonical.CuntzCantorBoundaryShift
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState

/-!
# Cantor-Bernoulli Cylinder Projection Bridge

This file formalizes the fundamental bridge connecting the operator projection tree $P_w$
with the Bernoulli fractal measure on the Cantor space:
$$\boxed{P_w = M_{\mathbf{1}_{[w]}} \quad\Longrightarrow\quad \langle \mathbf{1}, P_w \mathbf{1} \rangle = \mu_C([w]) = 2^{-|w|}}.$$

## Unifying Three Mathematical Worlds:
1. **Tree depth**: word length $|w|$;
2. **Operator projection**: $P_w = S_w S_w^\dagger$;
3. **Bernoulli probability**: $\mu_C([w]) = 2^{-|w|}$.
-/

noncomputable section

open Complex
open MeasureTheory
open scoped BigOperators Topology ENNReal Classical
open InfoGeometry.Canonical.CuntzCantorBoundaryShift
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderProjectionBridge

/-- The cylinder subset of `Boundary` determined by a finite binary word. -/
def wordBranchSet : List Bool → Set Boundary
  | [] => Set.univ
  | b :: w => prependBit b '' (wordBranchSet w)

@[simp] theorem wordBranchSet_nil :
    wordBranchSet [] = Set.univ := rfl

@[simp] theorem wordBranchSet_cons (b : Bool) (w : List Bool) :
    wordBranchSet (b :: w) = prependBit b '' (wordBranchSet w) := rfl

theorem wordBranchSet_singleton (b : Bool) :
    wordBranchSet [b] = prependBitBranch b := by
  dsimp [wordBranchSet]
  rw [prependBitBranch_eq_range]
  simp

theorem measurableSet_wordBranchSet (w : List Bool) :
    MeasurableSet (wordBranchSet w) := by
  induction w with
  | nil => exact MeasurableSet.univ
  | cons b w ih =>
    dsimp [wordBranchSet]
    have h_range : prependBit b '' (wordBranchSet w) =
        (prependBitBranch b) ∩ (tail ⁻¹' (wordBranchSet w)) := by
      rw [prependBitBranch_eq_range]
      ext x
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_range, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, rfl⟩, by simpa [tail_prependBit] using hy⟩
      · rintro ⟨⟨y, rfl⟩, hy⟩
        simp only [tail_prependBit] at hy
        exact ⟨y, hy, rfl⟩
    rw [h_range]
    exact (measurableSet_prependBitBranch b).inter (continuous_tail.measurable ih)

theorem μC_image_prependBit (b : Bool) (s : Set Boundary) (hs : MeasurableSet s) :
    μC (prependBit b '' s) = (1 / 2 : ℝ≥0∞) * μC s := by
  have h_range : prependBit b '' s = (Set.range (prependBit b)) ∩ (tail ⁻¹' s) := by
    ext x
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by simpa [tail_prependBit] using hy⟩
    · rintro ⟨⟨y, rfl⟩, hy⟩
      simp only [tail_prependBit] at hy
      exact ⟨y, hy, rfl⟩
  rw [h_range]
  have h_inter : Set.range (prependBit b) ∩ tail ⁻¹' s =
      (tail ⁻¹' s) ∩ Set.range (prependBit b) := Set.inter_comm _ _
  rw [h_inter, ← Measure.restrict_apply (continuous_tail.measurable hs)]
  have h_map := tail_measure_map_restrict_prependBitBranch b
  have h_eval := congrArg (fun μ : Measure Boundary => μ s) h_map
  dsimp at h_eval
  rw [Measure.map_apply continuous_tail.measurable hs] at h_eval
  exact h_eval

/-- The Bernoulli measure of a cylinder set is exactly $2^{-|w|}$. -/
theorem μC_wordBranchSet (w : List Bool) :
    μC (wordBranchSet w) = (1 / 2 : ℝ≥0∞) ^ w.length := by
  induction w with
  | nil =>
    dsimp [wordBranchSet, List.length]
    rw [measure_univ, pow_zero]
  | cons b w ih =>
    dsimp [wordBranchSet, List.length]
    rw [μC_image_prependBit b (wordBranchSet w) (measurableSet_wordBranchSet w)]
    rw [ih, pow_succ]
    ring

/-- The cylinder expectation value of $P_w$ on the vacuum vector equals $\mu_C([w]) = 2^{-|w|}$. -/
theorem cantorVacuumState_operatorCylinderProjection_word (w : List Bool) :
    canonicalGaugeState w w = (1 / 2 : ℂ) ^ w.length := by
  rw [canonicalGaugeState_proj]

end InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderProjectionBridge
