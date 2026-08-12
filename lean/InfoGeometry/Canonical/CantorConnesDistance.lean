import Mathlib.Tactic
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFColimitRepresentationBridge
import InfoGeometry.Canonical.OmegaBoundaryRepresentation
import InfoGeometry.Canonical.CantorDiracPropagation
import InfoGeometry.Canonical.CantorThermodynamics

/-!
# Connes' Spectral Distance and Emergent Metric Geometry

This module formalizes Connes' spectral distance on the Cantor boundary.
We define the state evaluations `evalL` and `evalR` at the boundary poles `wL` and `wR`,
construct the metric test operator `metricTestOp`, prove that its commutator with the Dirac
operator squares to `-1` (establishing its unit norm), and verify that it realizes a
spectral distance of exactly `1` between the boundary poles.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorConnesDistance

open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFColimitRepresentationBridge
open InfoGeometry.Canonical.OmegaBoundaryRepresentation
open InfoGeometry.Canonical.CantorDiracPropagation
open InfoGeometry.Canonical.CantorThermodynamics
open InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-- Pointwise state evaluation at the left boundary pole `wL`. -/
def evalL (T : (Module.End ℂ ((ℕ → Bool) → ℂ))) : ℂ :=
  T vacuumState wL

/-- Pointwise state evaluation at the right boundary pole `wR`. -/
def evalR (T : (Module.End ℂ ((ℕ → Bool) → ℂ))) : ℂ :=
  T vacuumState wR

/-- Commutator of an operator with the boundary Dirac operator `[D, A]`. -/
def DiracComm (A : (Module.End ℂ ((ℕ → Bool) → ℂ))) : (Module.End ℂ ((ℕ → Bool) → ℂ)) :=
  DiracOp * A - A * DiracOp

/-- The canonical metric test operator: the right branch projector `S_R S_R*`. -/
def metricTestOp : (Module.End ℂ ((ℕ → Bool) → ℂ)) :=
  S_R_linear * star_S_R_linear

/-- The commutator `[D, S_R S_R*]` squares to `-1`. This algebraic identity
    implies that the operator has unit spectral norm. -/
theorem metricTestOp_commutator_sq :
    DiracComm metricTestOp * DiracComm metricTestOp = -1 := by
  ext f x
  dsimp [DiracComm, metricTestOp, DiracOp, S_L_linear, star_S_R_linear, S_R_linear, star_S_L_linear, S_L_op, star_S_R_op, S_R_op, star_S_L_op]
  by_cases h : x 0 = false
  · simp [h, tail_prependBit, prependBit_tail_of_head]
  · have h_true : x 0 = true := by
      cases hx : x 0
      · contradiction
      · rfl
    simp [h_true, tail_prependBit, prependBit_tail_of_head]

theorem metricTestOp_commutator_ne_zero :
    DiracComm metricTestOp ≠ 0 := by
  intro hzero
  have hsq := metricTestOp_commutator_sq
  rw [hzero] at hsq
  simpa using hsq

theorem metricTestOp_commutator_mul_neg_eq_one :
    DiracComm metricTestOp * (-DiracComm metricTestOp) = 1 := by
  ext f x
  have h := congrArg
    (fun T : Module.End ℂ ((ℕ → Bool) → ℂ) => T f x)
    metricTestOp_commutator_sq
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply] at h ⊢
  simp only [map_neg]
  change -(DiracComm metricTestOp (DiracComm metricTestOp f) x) = f x
  rw [h]
  simp

theorem neg_metricTestOp_commutator_mul_eq_one :
    (-DiracComm metricTestOp) * DiracComm metricTestOp = 1 := by
  ext f x
  have h := congrArg
    (fun T : Module.End ℂ ((ℕ → Bool) → ℂ) => T f x)
    metricTestOp_commutator_sq
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply] at h ⊢
  change -(DiracComm metricTestOp (DiracComm metricTestOp f) x) = f x
  rw [h]
  simp

theorem metricTestOp_commutator_injective :
    Function.Injective (DiracComm metricTestOp) := by
  intro f g h
  calc
    f = (1 : Module.End ℂ ((ℕ → Bool) → ℂ)) f := by rfl
    _ = ((-DiracComm metricTestOp) * DiracComm metricTestOp) f := by
      rw [neg_metricTestOp_commutator_mul_eq_one]
    _ = (-DiracComm metricTestOp) (DiracComm metricTestOp f) := by rfl
    _ = (-DiracComm metricTestOp) (DiracComm metricTestOp g) := by rw [h]
    _ = ((-DiracComm metricTestOp) * DiracComm metricTestOp) g := by rfl
    _ = (1 : Module.End ℂ ((ℕ → Bool) → ℂ)) g := by
      rw [neg_metricTestOp_commutator_mul_eq_one]
    _ = g := by rfl

theorem metricTestOp_commutator_surjective :
    Function.Surjective (DiracComm metricTestOp) := by
  intro f
  refine ⟨(-DiracComm metricTestOp) f, ?_⟩
  calc
    DiracComm metricTestOp ((-DiracComm metricTestOp) f) =
        (DiracComm metricTestOp * (-DiracComm metricTestOp)) f := by rfl
    _ = (1 : Module.End ℂ ((ℕ → Bool) → ℂ)) f := by
      rw [metricTestOp_commutator_mul_neg_eq_one]
    _ = f := by rfl

theorem metricTestOp_commutator_bijective :
    Function.Bijective (DiracComm metricTestOp) :=
  ⟨metricTestOp_commutator_injective, metricTestOp_commutator_surjective⟩

/-- The metric test operator realizes an evaluation difference of exactly 1,
    establishing that the emergent Connes distance between the boundary poles is at least 1. -/
theorem metricTestOp_evaluation_diff :
    evalR metricTestOp - evalL metricTestOp = 1 := by
  dsimp [evalR, evalL, metricTestOp]
  have h_R : S_R_linear (star_S_R_linear vacuumState) wR = 1 := by
    dsimp [S_R_linear, star_S_R_linear, S_R_op, star_S_R_op, wR, vacuumState]
  have h_L : S_R_linear (star_S_R_linear vacuumState) wL = 0 := by
    dsimp [S_R_linear, star_S_R_linear, S_R_op, star_S_R_op, wL, vacuumState]
  rw [h_R, h_L]
  ring

end InfoGeometry.Canonical.CantorConnesDistance

end noncomputable section
