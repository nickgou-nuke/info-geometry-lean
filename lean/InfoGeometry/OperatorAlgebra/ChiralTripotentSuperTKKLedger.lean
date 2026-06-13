import InfoGeometry.Algebraic.ChiralOperatorCarrier
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
import InfoGeometry.Topology.V4RootSystem

/-!
# Chiral / tripotent / Super-TKK hierarchy ledger

This module records the finite theorem-owned hierarchy:

* the doubled Hestenes-Krein chiral carrier supplies `uPlus`, `uMinus`, and
  `eps = uPlus - uMinus`;
* the finite tripotent classifier supplies the `+1`, `0`, and `-1` branches;
* the Super-TKK owner supplies the five-grade closure envelope
  `g₋₂ ⊕ g₋₁ ⊕ g₀ ⊕ g₊₁ ⊕ g₊₂`.

The file is only a dictionary/ledger over existing owners.  It does not assert a
physical BdG theorem, CPT theorem, Pin/O(5,5) representation theorem, QCD
confinement, GR/vielbein geometry, continuum anomaly cancellation, or a braid
statistics theorem.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralTripotentSuperTKKLedger

open InfoGeometry.Algebraic
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
open InfoGeometry.Topology.V4RootSystem

/-! ## Chiral carrier readbacks -/

variable {X : InvolutiveSelfDualCarrier}

/-- The canonical chiral carrier has the expected projector and phase-axis laws. -/
theorem chiral_carrier_packet :
    let C := ChiralOperatorCarrier.canonicalChiralOperatorCarrier (X := X)
    C.eps = C.uPlus - C.uMinus ∧
      C.uPlus.comp C.uPlus = C.uPlus ∧
      C.uMinus.comp C.uMinus = C.uMinus ∧
      C.uPlus + C.uMinus = ContinuousLinearMap.id ℝ X.H ∧
      C.uPlus.comp C.uMinus = 0 ∧
      C.uMinus.comp C.uPlus = 0 ∧
      C.conformalOperator.comp C.conformalOperator =
        -(ContinuousLinearMap.id ℝ X.H) := by
  intro C
  exact ⟨
    ChiralOperatorCarrier.canonicalChiralOperatorCarrier_eps_eq_uPlus_sub_uMinus,
    C.uPlus_idempotent,
    C.uMinus_idempotent,
    C.uPlus_add_uMinus,
    C.uPlus_comp_uMinus,
    C.uMinus_comp_uPlus,
    C.conformal_sq_neg_id⟩

/-! ## Tripotent classifier readbacks -/

/-- The zero branch is the tripotent defect/kernel branch in the finite classifier. -/
theorem tripotent_zero_branch_packet :
    TripotentState.toInt TripotentState.zero = 0 ∧
      TripotentState.pZero TripotentState.zero = 1 ∧
      TripotentState.pPos TripotentState.zero = 0 ∧
      TripotentState.pNeg TripotentState.zero = 0 := by
  simp [TripotentState.toInt, TripotentState.pZero, TripotentState.pPos,
    TripotentState.pNeg]

/-- The finite tripotent classifier carries `T³=T` and projector partition laws. -/
theorem tripotent_classifier_packet :
    (∀ s : TripotentState, TripotentState.toInt s ^ 3 = TripotentState.toInt s) ∧
      (∀ s : TripotentState,
        TripotentState.pNeg s + TripotentState.pZero s + TripotentState.pPos s = 1) ∧
      (∀ s : TripotentState,
        TripotentState.pNeg s * TripotentState.pNeg s = TripotentState.pNeg s ∧
          TripotentState.pZero s * TripotentState.pZero s = TripotentState.pZero s ∧
          TripotentState.pPos s * TripotentState.pPos s = TripotentState.pPos s) := by
  exact ⟨TripotentState.cube_eq_self,
    TripotentState.trifactor_projector_partition,
    TripotentState.trifactor_projector_idempotent⟩

/-! ## Super-TKK five-grade routing -/

variable {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (G : FiveGrading L)

/-- Same and mixed grade-one brackets are routed to the Super-TKK five-grade targets. -/
theorem five_grading_particle_hole_defect_packet
    {Xminus Xplus Yminus Yplus : L}
    (hXm : Xminus ∈ G.gNegOne)
    (hYm : Yminus ∈ G.gNegOne)
    (hXp : Xplus ∈ G.gPosOne)
    (hYp : Yplus ∈ G.gPosOne) :
    ⁅Xminus, Xplus⁆ ∈ G.gZero ∧
      ⁅Xplus, Yplus⁆ ∈ G.gPosTwo ∧
      ⁅Xminus, Yminus⁆ ∈ G.gNegTwo := by
  exact ⟨G.neg_one_pos_one_mem_zero hXm hXp,
    G.pos_one_pos_one_mem_pos_two hXp hYp,
    G.neg_one_neg_one_mem_neg_two hXm hYm⟩

/-- Grade zero is the internal/stable bracket carrier and acts on both defect grades. -/
theorem five_grading_zero_and_defect_action_packet
    {Z₁ Z₂ P₂ N₂ : L}
    (hZ₁ : Z₁ ∈ G.gZero)
    (hZ₂ : Z₂ ∈ G.gZero)
    (hP₂ : P₂ ∈ G.gPosTwo)
    (hN₂ : N₂ ∈ G.gNegTwo) :
    ⁅Z₁, Z₂⁆ ∈ G.gZero ∧
      ⁅Z₁, P₂⁆ ∈ G.gPosTwo ∧
      ⁅Z₁, N₂⁆ ∈ G.gNegTwo := by
  exact ⟨G.zero_zero_mem_zero hZ₁ hZ₂,
    G.zero_pos_two_mem_pos_two hZ₁ hP₂,
    G.zero_neg_two_mem_neg_two hZ₁ hN₂⟩

/-- Positive extremal grade-two defects are abelian in the Super-TKK owner. -/
theorem five_grading_pos_two_abelian_packet
    {P Q : L}
    (hP : P ∈ G.gPosTwo)
    (hQ : Q ∈ G.gPosTwo) :
    ⁅P, Q⁆ = 0 :=
  G.pos_two_is_abelian hP hQ

/-- Consolidated finite hierarchy packet over the existing owners. -/
theorem chiral_tripotent_super_tkk_hierarchy_packet
    {Xminus Xplus Yminus Yplus Z₁ Z₂ P₂ N₂ : L}
    (hXm : Xminus ∈ G.gNegOne)
    (hYm : Yminus ∈ G.gNegOne)
    (hXp : Xplus ∈ G.gPosOne)
    (hYp : Yplus ∈ G.gPosOne)
    (hZ₁ : Z₁ ∈ G.gZero)
    (hZ₂ : Z₂ ∈ G.gZero)
    (hP₂ : P₂ ∈ G.gPosTwo)
    (hN₂ : N₂ ∈ G.gNegTwo) :
    (∀ s : TripotentState, TripotentState.toInt s ^ 3 = TripotentState.toInt s) ∧
      TripotentState.toInt TripotentState.zero = 0 ∧
      ⁅Xminus, Xplus⁆ ∈ G.gZero ∧
      ⁅Xplus, Yplus⁆ ∈ G.gPosTwo ∧
      ⁅Xminus, Yminus⁆ ∈ G.gNegTwo ∧
      ⁅Z₁, Z₂⁆ ∈ G.gZero ∧
      ⁅Z₁, P₂⁆ ∈ G.gPosTwo ∧
      ⁅Z₁, N₂⁆ ∈ G.gNegTwo := by
  exact ⟨TripotentState.cube_eq_self, rfl,
    G.neg_one_pos_one_mem_zero hXm hXp,
    G.pos_one_pos_one_mem_pos_two hXp hYp,
    G.neg_one_neg_one_mem_neg_two hXm hYm,
    G.zero_zero_mem_zero hZ₁ hZ₂,
    G.zero_pos_two_mem_pos_two hZ₁ hP₂,
    G.zero_neg_two_mem_neg_two hZ₁ hN₂⟩

end InfoGeometry.OperatorAlgebra.ChiralTripotentSuperTKKLedger

end noncomputable section
