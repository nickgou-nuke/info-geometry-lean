/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PolynomialCalculus
import InfoGeometry.Clifford.Cl11StarAlgebraColimit
import InfoGeometry.Canonical.TensorExactCurvatureTrace

/-!
# Polynomial Peirce calculus on the existing matrix direct limit

All operators belong to the existing algebraic direct limit of full real
matrix algebras. Polynomial evaluation is transported through the existing
faithful star-algebra inclusions. The graded readout uses the already
constructed compatible normalized trace; no new limit or trace is postulated.

The initial scalar stage cannot support a nonzero Peirce corner. The results
therefore allow an arbitrary finite starting stage and do not require a
noncentral cut to descend from stage zero. No topological completion or
analytic interpretation is asserted.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.PeircePolynomialColimit

open Polynomial
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11StarAlgebraColimit
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PolynomialCalculus
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.Canonical.TensorExactCurvatureTrace

/-- Native polynomial evaluation is preserved by the actual canonical
stage inclusion, with real coefficients unchanged. -/
theorem ofStage_aeval (n : ℕ) (X : Stage n) (f : ℝ[X]) :
    ofStage n (aeval X f) = aeval (ofStage n X) f := by
  exact (Polynomial.aeval_algHom_apply (ofStageStarAlgHom n) X f).symm

/-- Refinement does not change the represented polynomial observable. -/
theorem polynomial_refinement (n : ℕ) (X : Stage n) (f : ℝ[X]) :
    ofStage (n + 1) (aeval (stageEmbed n X) f) = ofStage n (aeval X f) := by
  rw [ofStage_aeval, ofStage_apply_bond, ofStage_aeval]

/-- The image of an upper Peirce corner is nonzero exactly when its finite
matrix representative is nonzero. This uses faithfulness, not only naturality. -/
theorem ofStage_conePlus_ne_zero_iff (n : ℕ) (P A : Stage n) :
    conePlus (ofStage n P) (ofStage n A) ≠ 0 ↔ conePlus P A ≠ 0 := by
  rw [← map_conePlus]
  exact not_congr (InfoGeometry.Clifford.Cl11StarAlgebraColimit.ofStage_eq_zero_iff
    n (conePlus P A))

/-- The exact divided-difference formula holds for finite-stage Peirce
perturbations represented in the actual direct limit. -/
theorem ofStage_aeval_add_conePlus (n : ℕ) (f : ℝ[X])
    {P : Stage n} (hP : P * P = P) (A : Stage n) :
    ofStage n (aeval (P + conePlus P A) f) = aeval (ofStage n P) f +
      algebraMap ℝ Limit (f.eval 1 - f.eval 0) *
        conePlus (ofStage n P) (ofStage n A) := by
  rw [ofStage_aeval, map_add, map_conePlus]
  exact aeval_add_conePlus f (map_idempotent (ofStage n) hP) (ofStage n A)

/-- Central scalar nilpotent calculus applies to the genuine off-diagonal
operator represented by any finite matrix corner. -/
theorem aeval_scalar_add_stage_corner (n : ℕ) (f : ℝ[X]) (r : ℝ)
    {P : Stage n} (hP : P * P = P) (A : Stage n) :
    aeval (algebraMap ℝ Limit r + conePlus (ofStage n P) (ofStage n A)) f =
      algebraMap ℝ Limit (f.eval r) + algebraMap ℝ Limit (f.derivative.eval r) *
        conePlus (ofStage n P) (ofStage n A) := by
  exact InfoGeometry.Algebra.NilpotentPolynomial.aeval_scalar_add_of_sq_zero f r
    (conePlus_mul_conePlus (map_idempotent (ofStage n) hP) _ _)

/-- Stage zero is scalar, so every idempotent originating there has zero
upper Peirce corner against every element of the full direct limit. -/
theorem stage_zero_conePlus_eq_zero {P : Stage 0} (hP : P * P = P) (X : Limit) :
    conePlus (ofStage 0 P) X = 0 := by
  have hscalar : P = algebraMap ℝ (Stage 0) (P default default) := by
    ext i j
    have hi : i = default := Subsingleton.elim _ _
    have hj : j = default := Subsingleton.elim _ _
    subst i
    subst j
    simp [Matrix.algebraMap_eq_diagonal]
  have hc : Commute (ofStage 0 P) X := by
    rw [hscalar]
    change Commute (algebraMap ℝ Limit (P default default)) X
    exact Algebra.commutes _ _
  have hp : ofStage 0 P * ofStage 0 P = ofStage 0 P := map_idempotent (ofStage 0) hP
  simp only [conePlus, hc.eq, mul_assoc, mul_sub, mul_one, hp, sub_self]

/-- The actual descended trace reads a polynomial in the Peirce metric
only through its constant coefficient after multiplication by the grading. -/
theorem normalizedTraceLimit_grading_aeval_metric (f : ℝ[X])
    {P : Limit} (hP : P * P = P) (A C : Limit) :
    normalizedTraceLimit (invS P * aeval (genV P A C) f) =
      f.eval 0 * normalizedTraceLimit (invS P) := by
  exact cyclic_grading_aeval_metric normalizedTraceLimit
    normalizedTraceLimit_cyclic f hP A C

/-- Reading a represented polynomial moment with the colimit trace is
exactly its finite normalized-matrix trace, with multiplication order intact. -/
theorem normalizedTraceLimit_grading_aeval_ofStage (n : ℕ) (f : ℝ[X])
    (P A C : Stage n) :
    normalizedTraceLimit
      (invS (ofStage n P) * aeval (genV (ofStage n P) (ofStage n A) (ofStage n C)) f) =
      normalizedTrace n (invS P * aeval (genV P A C) f) := by
  rw [← map_invS, ← map_genV, ← ofStage_aeval, ← map_mul]
  rfl

/-- The normalized graded polynomial moment is independent of a refinement
step. This is compatibility of the actual trace cocone, not a limit argument. -/
theorem normalizedTrace_grading_aeval_refinement (n : ℕ) (f : ℝ[X])
    (P A C : Stage n) :
    normalizedTrace (n + 1)
      (invS (stageEmbed n P) *
        aeval (genV (stageEmbed n P) (stageEmbed n A) (stageEmbed n C)) f) =
      normalizedTrace n (invS P * aeval (genV P A C) f) := by
  rw [← normalizedTraceLimit_grading_aeval_ofStage,
    ← normalizedTraceLimit_grading_aeval_ofStage]
  simp only [ofStage_apply_bond]

end InfoGeometry.Canonical.PeircePolynomialColimit

end
