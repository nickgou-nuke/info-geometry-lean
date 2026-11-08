/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FrechetPeirceStabilizerWitness

/-! # Lie stabilizer of an idempotent and continuous derivations

The carrier is the existing native real Lie algebra of Leibniz derivations.
Continuity is not assumed of every element: the existing adapter embeds each
continuous Fréchet–Leibniz derivation into this algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.FrechetPeirceLieStabilizer

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.OperatorFrechetDerivationJet.FrechetBridge
open InfoGeometry.Canonical.FrechetPeirceStabilizer

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Native Lie subalgebra of algebraic Leibniz derivations fixing a cut. -/
def cutStabilizer (P : A) : LieSubalgebra ℝ (InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ A) where
  carrier := {D | D.1 P = 0}
  zero_mem' := by
    change (0 : Module.End ℝ A) P = 0
    simp
  add_mem' := by
    intro D E hD hE
    change D.1 P = 0 at hD
    change E.1 P = 0 at hE
    change D.1 P + E.1 P = 0
    rw [hD, hE, add_zero]
  smul_mem' := by
    intro r D hD
    change D.1 P = 0 at hD
    change r • D.1 P = 0
    rw [hD, smul_zero]
  lie_mem' := by
    intro D E hD hE
    change D.1 P = 0 at hD
    change E.1 P = 0 at hE
    change D.1 (E.1 P) - E.1 (D.1 P) = 0
    simp only [hD, hE, map_zero, sub_self]

/-- Membership for an arbitrary continuous Leibniz derivation is equivalent
to commuting with the even Peirce projection. -/
theorem continuous_mem_iff_preserves_even (P : A) (hP : P * P = P)
    (D : FrechetOperatorDerivation ℝ A) :
    toRealDerivation D ∈ cutStabilizer P ↔
      ∀ X : A, D (evenGrade P X) = evenGrade P (D X) := by
  change D P = 0 ↔ _
  exact (derivation_commutes_evenGrade_iff D P hP).symm

open scoped Matrix Matrix.Norms.Operator
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorStageFrechetConnection
open InfoGeometry.Canonical.FrechetPeirceStabilizerWitness
open InfoGeometry.Examples.RealMatrixModeWitness

/-- The dense square-zero mode defines a continuous derivation outside the
cut stabilizer on the genuine noncommutative matrix stage. -/
theorem denseMode_not_mem_cutStabilizer :
    toRealDerivation (stageInnerFrechet 2 x) ∉ cutStabilizer p := by
  change stageInnerFrechet 2 x p ≠ 0
  rw [denseMode_derivation_cut]
  exact neg_ne_zero.mpr denseMode_ne_zero

/-- The inner derivation of the cut belongs to the stabilizer, yet acts
nontrivially on the dense off-diagonal mode. -/
theorem cut_inner_stabilizes_and_acts_nontrivially :
    toRealDerivation (stageInnerFrechet 2 p) ∈ cutStabilizer p ∧
      stageInnerFrechet 2 p x ≠ 0 := by
  constructor
  · change p * p - p * p = 0
    exact sub_self _
  · change p * x - x * p ≠ 0
    rw [p_mul_x, x_mul_p, sub_zero]
    exact denseMode_ne_zero

/-- The concrete matrix-stage stabilizer contains a nonzero derivation and
is a proper subalgebra of the full Leibniz derivation algebra. -/
theorem dense_cut_stabilizer_nontrivial_proper :
    (∃ D : InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ (Stage 2),
      D ∈ cutStabilizer p ∧ D ≠ 0) ∧
    (∃ D : InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ (Stage 2),
      D ∉ cutStabilizer p) := by
  constructor
  · refine ⟨toRealDerivation (stageInnerFrechet 2 p),
      cut_inner_stabilizes_and_acts_nontrivially.1, ?_⟩
    intro hz
    have he := congrArg
      (fun D : InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ (Stage 2) => D.1 x) hz
    change (stageInnerFrechet 2 p).toContinuousLinearMap x =
      (0 : Module.End ℝ (Stage 2)) x at he
    have hzero : stageInnerFrechet 2 p x = 0 := by simpa using he
    exact cut_inner_stabilizes_and_acts_nontrivially.2 hzero
  · exact ⟨toRealDerivation (stageInnerFrechet 2 x), denseMode_not_mem_cutStabilizer⟩

end InfoGeometry.Canonical.FrechetPeirceLieStabilizer

end
