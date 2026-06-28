import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
import InfoGeometry.Algebraic.ChiralOperatorCarrier
import InfoGeometry.Topology.V4RootSystem

/-!
# Super-TKK / Chiral / Tripotent Bridge

This module records the finite theorem surface for the refined hierarchy:

real doubled Hestenes-Krein chiral carrier
→ tripotent `±/0` boundary grading
→ super-TKK five-grading with `±2` defect sectors.

#### BUCKET 1: CLOSED FINITE THEOREMS

* mixed `g₋₁/g₊₁` brackets land in `g₀`;
* same-positive and same-negative grade-one brackets land in `g₊₂` and `g₋₂`;
* `g₀` acts on the two defect sectors, and `g₊₂` is abelian;
* the canonical chiral carrier satisfies `ε = P₊ - P₋`, projector
  orthogonality, and `(Jε)² = -1`;
* tripotent sectors satisfy `T³ = T` and the three projector readouts partition
  unity.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The five-grading closure packet assumes an explicit
`SuperTKKConformalClosure.FiveGrading` witness.  The chiral packet assumes an
explicit `InvolutiveSelfDualCarrier` witness.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not construct a concrete BdG/Krein-Fock representation, a
Pin(5,5) action, a global superconformal algebra, a boundary Majorana/Fibonacci
braid category, or a continuum anomaly-cancellation theorem.  It only names and
proves the finite owner-backed dictionary.
-/

noncomputable section

namespace InfoGeometry.Canonical.SuperTKKChiralTripotentBridge

open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
open InfoGeometry.Algebraic
open InfoGeometry.Krein
open InfoGeometry.Topology.V4RootSystem
open InfoGeometryCore.TripotentState

/-! ## Role dictionary -/

/-- The five semantic roles in the refined closure hierarchy. -/
inductive ClosureRole where
  | negTwo
  | negOne
  | zero
  | posOne
  | posTwo
  deriving DecidableEq, Repr

namespace ClosureRole

/-- Tripotent readout for the five roles: `±2` and `±1` share the sign, `g₀` is zero. -/
def tripotentSector : ClosureRole → InfoGeometryCore.TripotentState
  | negTwo => InfoGeometryCore.TripotentState.neg
  | negOne => InfoGeometryCore.TripotentState.neg
  | zero => InfoGeometryCore.TripotentState.zero
  | posOne => InfoGeometryCore.TripotentState.pos
  | posTwo => InfoGeometryCore.TripotentState.pos

/-- The role-to-tripotent dictionary is compatible with `T³ = T`. -/
theorem tripotentSector_cube (r : ClosureRole) :
    toInt (tripotentSector r) ^ 3 = toInt (tripotentSector r) := by
  exact cube_eq_self (tripotentSector r)

/-- The `±2` roles are exactly the explicit defect roles in this finite dictionary. -/
def IsDefect (r : ClosureRole) : Prop :=
  r = negTwo ∨ r = posTwo

/-- Positive grade two is a defect role. -/
theorem posTwo_is_defect : IsDefect posTwo := by
  exact Or.inr rfl

/-- Negative grade two is a defect role. -/
theorem negTwo_is_defect : IsDefect negTwo := by
  exact Or.inl rfl

/-- The zero role is not a defect role. -/
theorem zero_not_defect : ¬ IsDefect zero := by
  intro h
  cases h with
  | inl hz => cases hz
  | inr hz => cases hz

end ClosureRole

/-! ## Super-TKK five-grading packet -/

variable {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]

/-- Five-grading readout for mixed closure, same-arrow defects, and defect stability. -/
theorem five_grading_closure_packet (G : FiveGrading L) :
    (∀ X Y : L, X ∈ G.gNegOne → Y ∈ G.gPosOne → ⁅X, Y⁆ ∈ G.gZero) ∧
    (∀ X Y : L, X ∈ G.gPosOne → Y ∈ G.gPosOne → ⁅X, Y⁆ ∈ G.gPosTwo) ∧
    (∀ X Y : L, X ∈ G.gNegOne → Y ∈ G.gNegOne → ⁅X, Y⁆ ∈ G.gNegTwo) ∧
    (∀ X Y : L, X ∈ G.gZero → Y ∈ G.gPosTwo → ⁅X, Y⁆ ∈ G.gPosTwo) ∧
    (∀ X Y : L, X ∈ G.gZero → Y ∈ G.gNegTwo → ⁅X, Y⁆ ∈ G.gNegTwo) ∧
    (∀ X Y : L, X ∈ G.gPosTwo → Y ∈ G.gPosTwo → ⁅X, Y⁆ = 0) := by
  exact ⟨(fun X Y hX hY => G.neg_one_pos_one_mem_zero hX hY),
    (fun X Y hX hY => G.pos_one_pos_one_mem_pos_two hX hY),
    (fun X Y hX hY => G.neg_one_neg_one_mem_neg_two hX hY),
    (fun X Y hX hY => G.zero_pos_two_mem_pos_two hX hY),
    (fun X Y hX hY => G.zero_neg_two_mem_neg_two hX hY),
    (fun X Y hX hY => G.pos_two_is_abelian hX hY)⟩

/-! ## Chiral carrier packet -/

/-- Chiral carrier readout: projectors, chirality, and real conformal phase axis. -/
theorem chiral_operator_carrier_packet {X : InvolutiveSelfDualCarrier} :
    (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).eps =
        (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uPlus -
          (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uMinus ∧
    (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uPlus.comp
        (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uMinus = 0 ∧
    (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uMinus.comp
        (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uPlus = 0 ∧
    (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uPlus +
        (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uMinus =
          ContinuousLinearMap.id ℝ X.H ∧
    (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).conformalOperator.comp
        (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).conformalOperator =
          -(ContinuousLinearMap.id ℝ X.H) := by
  exact ⟨ChiralOperatorCarrier.canonicalChiralOperatorCarrier_eps_eq_uPlus_sub_uMinus,
    (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uPlus_comp_uMinus,
    (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uMinus_comp_uPlus,
    (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uPlus_add_uMinus,
    (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).conformal_sq_neg_id⟩

/-! ## Tripotent packet -/

/-- Tripotent finite readout for the `±/0` boundary grading. -/
theorem tripotent_boundary_packet :
    (∀ s : InfoGeometryCore.TripotentState, toInt s ^ 3 = toInt s) ∧
    (∀ s : InfoGeometryCore.TripotentState,
      pNeg s + pZero s + pPos s = 1) ∧
    (∀ s : InfoGeometryCore.TripotentState,
      toInt s * pNeg s = -pNeg s ∧
        toInt s * pZero s = 0 ∧
        toInt s * pPos s = pPos s) := by
  exact ⟨cube_eq_self, trifactor_projector_partition,
    trifactor_eigen_readout⟩

/-- Combined finite hierarchy packet for the super-TKK/chiral/tripotent dictionary. -/
theorem super_tkk_chiral_tripotent_hierarchy_packet
    (G : FiveGrading L) {X : InvolutiveSelfDualCarrier} :
    (∀ X₁ Y₁ : L, X₁ ∈ G.gNegOne → Y₁ ∈ G.gPosOne → ⁅X₁, Y₁⁆ ∈ G.gZero) ∧
    (∀ X₁ Y₁ : L, X₁ ∈ G.gPosOne → Y₁ ∈ G.gPosOne → ⁅X₁, Y₁⁆ ∈ G.gPosTwo) ∧
    (∀ X₁ Y₁ : L, X₁ ∈ G.gNegOne → Y₁ ∈ G.gNegOne → ⁅X₁, Y₁⁆ ∈ G.gNegTwo) ∧
    (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).eps =
        (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uPlus -
          (ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)).uMinus ∧
    (∀ s : InfoGeometryCore.TripotentState, toInt s ^ 3 = toInt s) ∧
    ClosureRole.IsDefect ClosureRole.posTwo ∧
    ClosureRole.IsDefect ClosureRole.negTwo := by
  exact ⟨(fun X Y hX hY => G.neg_one_pos_one_mem_zero hX hY),
    (fun X Y hX hY => G.pos_one_pos_one_mem_pos_two hX hY),
    (fun X Y hX hY => G.neg_one_neg_one_mem_neg_two hX hY),
    ChiralOperatorCarrier.canonicalChiralOperatorCarrier_eps_eq_uPlus_sub_uMinus,
    cube_eq_self, ClosureRole.posTwo_is_defect, ClosureRole.negTwo_is_defect⟩

end InfoGeometry.Canonical.SuperTKKChiralTripotentBridge

end
