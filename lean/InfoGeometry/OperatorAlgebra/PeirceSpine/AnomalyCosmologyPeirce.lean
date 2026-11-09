/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorBogoliubovSpinePoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.DiracPolynomialAction
import InfoGeometry.OperatorAlgebra.PeirceSpine.CayleyDicksonHopfPoset
import InfoGeometry.Meta.ArchetypePipeline

/-!
# Algebraic anomaly and quartic-polynomial synthesis

This module records consequences in an associative ring with an idempotent
Peirce cut. The trace statement is a commutator cancellation identity; it does
not model a regularized quantum-field anomaly. The quartic identity is an
operator polynomial identity, not a cosmological action.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.MetaCompiler

variable {B : Type*} [Ring B]

variable {P : B} (hP : P * P = P)
include hP

/-- The algebraic double-commutator flow used to package the quartic
operator identity. This is an endomorphism of the ring, not a time evolution. -/
def quarticAdjointFlow (A C X : B) : B :=
  comm (genSig P A C) X + comm (genJ P A C) (comm (genJ P A C) X)

/-- The nested commutator readout on the odd generator. -/
def currentDoubleCommutator (A C : B) : B :=
  comm (genJ P A C) (comm (genJ P A C) (genPhi P A C))

/-- The cubic Peirce term is the commutator defect supplied by the A₅₀
operator identity. -/
theorem cubic_chiral_term_is_half_commutator (A C : B) :
    (2 : ℤ) • (genV P A C * genJ P A C) =
      comm (genSig P A C) (genPhi P A C) := by
  simp only [genV, genJ, genSig, genPhi, anticomm, comm]
  peirce_nf hP

omit hP in
/-- The charge difference depends on the weak-sector idempotents; the color and
scalar terms cancel without orthogonality assumptions. No classification of
gauge groups follows from this identity. -/
theorem charge_difference_from_sector_data
    {P_O2 P_H1 P_H2 P_C : B} :
    chargeQ6 P_O2 P_H2 P_C - chargeY6 P_O2 P_H1 P_H2 P_C =
      (3 : ℤ) • quatChiralInv P_H1 P_H2 := by
  unfold chargeQ6 chargeY6 quatChiralInv
  simp only [zsmul_add, zsmul_sub]
  abel

omit hP in
/-- If the two quaternionic corner readouts balance, the post-minus-pre
charge difference has zero additive trace. This is a trace statement about
the sector operators; it does not assert cancellation of a field-theoretic
gauge anomaly. -/
theorem balanced_quaternionic_charge_trace_cancellation
    {R : Type*} [Ring R] (τ : B →+ R)
    {P_O2 P_H1 P_H2 P_C : B}
    (hBalance : τ P_H2 = τ P_H1) :
    τ (chargeQ6 P_O2 P_H2 P_C - chargeY6 P_O2 P_H1 P_H2 P_C) = 0 := by
  have hCharge := charge_difference_from_sector_data
    (P_O2 := P_O2) (P_H1 := P_H1) (P_H2 := P_H2) (P_C := P_C)
  have hInv : τ (quatChiralInv P_H1 P_H2) = τ P_H2 - τ P_H1 := by
    unfold quatChiralInv
    exact map_sub τ P_H2 P_H1
  calc
    τ (chargeQ6 P_O2 P_H2 P_C - chargeY6 P_O2 P_H1 P_H2 P_C)
        = τ ((3 : ℤ) • quatChiralInv P_H1 P_H2) := by rw [hCharge]
    _ = (3 : ℤ) • τ (quatChiralInv P_H1 P_H2) := by
      exact map_zsmul τ (3 : ℤ) (quatChiralInv P_H1 P_H2)
    _ = 0 := by
      rw [hInv, hBalance, sub_self, zsmul_zero]

omit hP in
/-- A cyclic additive trace kills the commutator appearing in the cubic
identity. This conclusion is strictly algebraic. -/
lemma cubic_commutator_trace_zero
    {R : Type*} [Ring R] (τ : B →+ R)
    (hCyc : ∀ X Y : B, τ (X * Y) = τ (Y * X)) (A C : B) :
    τ (comm (genSig P A C) (genPhi P A C)) = 0 := by
  unfold comm
  rw [map_sub, hCyc (genSig P A C) (genPhi P A C), sub_self]

/-- The fourth power of the grading-plus-Peirce operator has the exact
operator-polynomial decomposition into a constant term, a linear interaction,
and its idempotency defect. -/
theorem quartic_operator_decomposition (A C : B) :
    (peirceMassDirac P A C * peirceMassDirac P A C) *
      (peirceMassDirac P A C * peirceMassDirac P A C) =
      1 + (3 : ℤ) • genV P A C + idempotencyDefect (genV P A C) := by
  have hsq := peirce_mass_dirac_square hP A C
  rw [hsq]
  change (1 + genV P A C) * (1 + genV P A C) =
    1 + (3 : ℤ) • genV P A C +
      (genV P A C * genV P A C - genV P A C)
  noncomm_ring

/-- The algebraic quartic flow vanishes on the fourth power of the massive
Peirce operator. -/
theorem quartic_flow_fixes_fourth_power (A C : B) :
    quarticAdjointFlow (P := P) A C
      ((peirceMassDirac P A C * peirceMassDirac P A C) *
        (peirceMassDirac P A C * peirceMassDirac P A C)) = 0 := by
  have hSigV : comm (genSig P A C) (genV P A C) = 0 := by
    peirce_nf hP
  have hJV : comm (genJ P A C) (genV P A C) = 0 := by
    peirce_nf hP
  have hSigVmul : genSig P A C * genV P A C =
      genV P A C * genSig P A C := sub_eq_zero.mp hSigV
  have hJVmul : genJ P A C * genV P A C =
      genV P A C * genJ P A C := sub_eq_zero.mp hJV
  have hSigV2 : genSig P A C * (genV P A C * genV P A C) =
      (genV P A C * genV P A C) * genSig P A C := by
    calc
      genSig P A C * (genV P A C * genV P A C) =
          (genSig P A C * genV P A C) * genV P A C := by rw [mul_assoc]
      _ = (genV P A C * genSig P A C) * genV P A C := by rw [hSigVmul]
      _ = genV P A C * (genSig P A C * genV P A C) := by rw [mul_assoc]
      _ = genV P A C * (genV P A C * genSig P A C) := by rw [hSigVmul]
      _ = (genV P A C * genV P A C) * genSig P A C := by rw [mul_assoc]
  have hJV2 : genJ P A C * (genV P A C * genV P A C) =
      (genV P A C * genV P A C) * genJ P A C := by
    calc
      genJ P A C * (genV P A C * genV P A C) =
          (genJ P A C * genV P A C) * genV P A C := by rw [mul_assoc]
      _ = (genV P A C * genJ P A C) * genV P A C := by rw [hJVmul]
      _ = genV P A C * (genJ P A C * genV P A C) := by rw [mul_assoc]
      _ = genV P A C * (genV P A C * genJ P A C) := by rw [hJVmul]
      _ = (genV P A C * genV P A C) * genJ P A C := by rw [mul_assoc]
  have hSigPoly : comm (genSig P A C)
      (1 + (3 : ℤ) • genV P A C + idempotencyDefect (genV P A C)) = 0 := by
    unfold comm idempotencyDefect
    noncomm_ring [hSigVmul, hSigV2]
  have hJPoly : comm (genJ P A C)
      (1 + (3 : ℤ) • genV P A C + idempotencyDefect (genV P A C)) = 0 := by
    unfold comm idempotencyDefect
    noncomm_ring [hJVmul, hJV2]
  rw [quartic_operator_decomposition hP A C]
  unfold quarticAdjointFlow
  rw [hSigPoly, hJPoly]
  simp [comm]

/-- The double commutator by the current acts on the odd generator as left
multiplication by the negative fourfold metric. -/
theorem current_double_commutator_identity (A C : B) :
  currentDoubleCommutator (P := P) A C =
      -((4 : ℤ) • (genV P A C * genPhi P A C)) := by
  simp only [currentDoubleCommutator]
  abel_nf; peirce_nf hP

/-- The commutator and anticommutator squares agree for the two opposite
Peirce round-trip blocks. -/
theorem square_defect_is_zero :
    genSig P A C * genSig P A C - genV P A C * genV P A C = 0 := by
  peirce_nf hP

/-! ## Proof-carrying operator archetypes -/

/-- Idempotent cuts are represented by a subtype, so their defining equation
is carried by the operator input itself. -/
abbrev ACIdempotentCut (B : Type*) [Ring B] := {P : B // P * P = P}

/-- Data for operator identities generated by one Peirce cut. -/
structure ACOperatorInput (B : Type*) [Ring B] where
  cut : ACIdempotentCut B
  forwardAmplitude : B
  backwardAmplitude : B

/-- The cubic chiral term is twice a commutator, for arbitrary ring-valued
amplitudes and an idempotent cut. -/
def acCubicCommutatorArchetype {B : Type*} [Ring B] :
    TypedArchetype (ACOperatorInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acCubicCommutatorArchetype
  phase := 62
  claim := fun input =>
    (2 : ℤ) • (genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
      genJ (input.cut : B) input.forwardAmplitude input.backwardAmplitude) =
      comm (genSig (input.cut : B) input.forwardAmplitude input.backwardAmplitude)
        (genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude)
  evidence := fun input => cubic_chiral_term_is_half_commutator
    input.cut.property input.forwardAmplitude input.backwardAmplitude

/-- The massive Peirce operator's fourth power splits into its constant term,
three times the metric term, and the metric's idempotency defect. -/
def acQuarticDecompositionArchetype {B : Type*} [Ring B] :
    TypedArchetype (ACOperatorInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acQuarticDecompositionArchetype
  phase := 62
  claim := fun input =>
    (peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
      peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude) *
      (peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude) =
      1 + (3 : ℤ) • genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude +
        idempotencyDefect
          (genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude)
  evidence := fun input => quartic_operator_decomposition
    input.cut.property input.forwardAmplitude input.backwardAmplitude

/-- The quartic polynomial is fixed by the algebraically defined adjoint
commutator flow. This is an operator identity, not a time-evolution law. -/
def acQuarticFlowArchetype {B : Type*} [Ring B] :
    TypedArchetype (ACOperatorInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acQuarticFlowArchetype
  phase := 62
  claim := fun input =>
    quarticAdjointFlow (P := (input.cut : B)) input.forwardAmplitude
      input.backwardAmplitude
      ((peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude) *
       (peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        peirceMassDirac (input.cut : B) input.forwardAmplitude input.backwardAmplitude)) = 0
  evidence := fun input => quartic_flow_fixes_fourth_power
    input.cut.property input.forwardAmplitude input.backwardAmplitude

/-- The commutator-square and anticommutator-square coincide for the two
opposite Peirce round-trip blocks. -/
def acSquareDefectArchetype {B : Type*} [Ring B] :
    TypedArchetype (ACOperatorInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acSquareDefectArchetype
  phase := 62
  claim := fun input =>
    genSig (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        genSig (input.cut : B) input.forwardAmplitude input.backwardAmplitude -
      genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude = 0
  evidence := fun input => square_defect_is_zero
    (P := (input.cut : B)) (hP := input.cut.property)
    (A := input.forwardAmplitude) (C := input.backwardAmplitude)

/-- The nested commutator is left multiplication by minus four times the
metric interaction, with the integer coefficient interpreted in the ring. -/
def acDoubleCommutatorArchetype {B : Type*} [Ring B] :
    TypedArchetype (ACOperatorInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acDoubleCommutatorArchetype
  phase := 62
  claim := fun input =>
    currentDoubleCommutator (P := (input.cut : B)) input.forwardAmplitude
        input.backwardAmplitude =
      -((4 : ℤ) • (genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude))
  evidence := fun input => current_double_commutator_identity
    input.cut.property input.forwardAmplitude input.backwardAmplitude

/-- Data for the sector-balance trace statement. The charge operators retain
their color, weak, and scalar sector entries; this trace conclusion requires
only equality of the two weak-sector traces. -/
structure ACChargeBalanceInput (B R : Type*) [Ring B] [Ring R] where
  trace : B →+ R
  colorSector : B
  weakSectorOne : B
  weakSectorTwo : B
  scalarSector : B
  traceBalance : trace weakSectorTwo = trace weakSectorOne

/-- Under the exact sector and trace-balance premises, the charge-difference
operator has zero trace. This is a conditional algebraic archetype. -/
def acBalancedChargeTraceArchetype {B R : Type*} [Ring B] [Ring R] :
    TypedArchetype (ACChargeBalanceInput B R) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology.acBalancedChargeTraceArchetype
  phase := 62
  claim := fun input =>
    let chargeTrace := input.trace
      (chargeQ6 input.colorSector input.weakSectorTwo input.scalarSector -
        chargeY6 input.colorSector input.weakSectorOne input.weakSectorTwo
          input.scalarSector)
    chargeTrace = 0
  evidence := fun input => balanced_quaternionic_charge_trace_cancellation
    input.trace
    input.traceBalance

/-! ## Proof-carrying causal order

Each direct edge carries the corresponding operator identity (or conditional
sector-trace conclusion), rather than a tautological `True`. -/

variable {R : Type*} [Ring R]

omit hP in
inductive ACStage (B : Type*) [Ring B] (R : Type*) [Ring R] where
  | peirceCut
  | cubicCommutator
  | chargeSectorData
  | chargeDifference
  | traceLaws
  | sectorBalance
  | balancedChargeTrace
  | quarticDefect
  | quarticFlow
  | doubleCommutatorIdentity
  | squareDefect
  deriving DecidableEq, Repr

omit hP in
def ACStage.edge : ACStage B R → ACStage B R → Prop
  | .peirceCut, .cubicCommutator =>
      ∀ input : ACOperatorInput B, acCubicCommutatorArchetype.claim input
  | .peirceCut, .quarticDefect =>
      ∀ input : ACOperatorInput B, acQuarticDecompositionArchetype.claim input
  | .peirceCut, .quarticFlow =>
      ∀ input : ACOperatorInput B, acQuarticFlowArchetype.claim input
  | .peirceCut, .doubleCommutatorIdentity =>
      ∀ input : ACOperatorInput B, acDoubleCommutatorArchetype.claim input
  | .peirceCut, .squareDefect =>
      ∀ input : ACOperatorInput B, acSquareDefectArchetype.claim input
  | .quarticDefect, .quarticFlow =>
      ∀ input : ACOperatorInput B, acQuarticFlowArchetype.claim input
  | .chargeSectorData, .chargeDifference =>
      ∀ input : ACChargeBalanceInput B R,
        chargeQ6 input.colorSector input.weakSectorTwo input.scalarSector -
          chargeY6 input.colorSector input.weakSectorOne input.weakSectorTwo input.scalarSector =
            (3 : ℤ) • quatChiralInv input.weakSectorOne input.weakSectorTwo
  | .chargeDifference, .balancedChargeTrace =>
      ∀ input : ACChargeBalanceInput B R, acBalancedChargeTraceArchetype.claim input
  | .traceLaws, .balancedChargeTrace =>
      ∀ input : ACChargeBalanceInput B R, acBalancedChargeTraceArchetype.claim input
  | .sectorBalance, .balancedChargeTrace =>
      ∀ input : ACChargeBalanceInput B R, acBalancedChargeTraceArchetype.claim input
  | _, _ => False

omit hP in
inductive ACStage.Reachable : ACStage B R → ACStage B R → Prop where
  | refl (a : ACStage B R) : Reachable a a
  | edge {a b : ACStage B R} : a.edge b → Reachable a b
  | trans {a b c : ACStage B R} : Reachable a b → Reachable b c → Reachable a c

/-- Causal order generated by the direct premise edges. -/
def ACStage.causalLE : ACStage B R → ACStage B R → Prop := Reachable

omit hP in
def ACStage.rank : ACStage B R → Nat
  | .peirceCut => 0
  | .cubicCommutator => 1
  | .chargeSectorData => 0
  | .chargeDifference => 1
  | .traceLaws => 0
  | .sectorBalance => 0
  | .balancedChargeTrace => 2
  | .quarticDefect => 1
  | .quarticFlow => 2
  | .doubleCommutatorIdentity => 1
  | .squareDefect => 1

omit hP in
theorem ACStage.causalLE_refl (x : ACStage B R) : x.causalLE x := by
  exact Reachable.refl x

omit hP in
theorem ACStage.causalLE_trans {x y z : ACStage B R}
    (hxy : x.causalLE y) (hyz : y.causalLE z) : x.causalLE z := by
  exact Reachable.trans hxy hyz

omit hP in
theorem ACStage.edge_rank_strict {x y : ACStage B R} (h : x.edge y) : x.rank < y.rank := by
  cases x <;> cases y <;> simp_all [rank, ACStage.edge]

omit hP in
theorem ACStage.reachable_rank_strict_of_ne {x y : ACStage B R}
    (h : x.Reachable y) (hne : x ≠ y) : x.rank < y.rank := by
  induction h with
  | @refl a => exact (hne rfl).elim
  | edge h => exact edge_rank_strict h
  | @trans a b c hab hbc ihab ihbc =>
      by_cases habEq : a = b
      · subst b
        exact ihbc hne
      · by_cases hbcEq : b = c
        · subst c
          exact ihab hne
        · exact lt_trans (ihab habEq) (ihbc hbcEq)

omit hP in
theorem ACStage.causalLE_antisymm {x y : ACStage B R}
    (hxy : x.causalLE y) (hyx : y.causalLE x) : x = y := by
  by_cases hEq : x = y
  · exact hEq
  · exact (lt_asymm (reachable_rank_strict_of_ne hxy hEq)
      (reachable_rank_strict_of_ne hyx (Ne.symm hEq))).elim

omit hP in
instance : PartialOrder (ACStage B R) where
  le := ACStage.causalLE
  le_refl := ACStage.causalLE_refl
  le_trans := fun _ _ _ hab hbc => ACStage.causalLE_trans hab hbc
  le_antisymm := fun _ _ hab hba => ACStage.causalLE_antisymm hab hba

omit hP in
theorem ACStage.edge_causalLE {x y : ACStage B R} (h : x.edge y) : x.causalLE y :=
  ACStage.Reachable.edge h


#register_archetype acCubicCommutatorArchetype
#audit_archetype acCubicCommutatorArchetype
#register_archetype acQuarticDecompositionArchetype
#audit_archetype acQuarticDecompositionArchetype
#register_archetype acQuarticFlowArchetype
#audit_archetype acQuarticFlowArchetype
#register_archetype acSquareDefectArchetype
#audit_archetype acSquareDefectArchetype
#register_archetype acDoubleCommutatorArchetype
#audit_archetype acDoubleCommutatorArchetype
#register_archetype acBalancedChargeTraceArchetype
#audit_archetype acBalancedChargeTraceArchetype

end InfoGeometry.OperatorAlgebra.PeirceSpine.AnomalyCosmology
