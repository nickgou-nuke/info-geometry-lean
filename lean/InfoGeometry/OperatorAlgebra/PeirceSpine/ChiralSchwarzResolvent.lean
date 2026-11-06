/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.SquareZeroCStarRigidity
import InfoGeometry.OperatorAlgebra.QuadraticResolventCalculus
import InfoGeometry.OperatorAlgebra.LogarithmicResolventPositivity

/-!
# Peirce Schwarz action and native resolvent synthesis

The first part retains an exact characteristic-free consequence of the
two wing tests: twice the square of the interaction vanishes. It then connects
the displaced cut to every finite level of the existing orthogonal defect
tower. These statements do not impose a positive star or an analytic norm.

The second part uses a positive C*-adjoint pairing. The existing Peirce square
identity supplies the analytic denominator, positivity supplies its unit
domain in the plus case, and the new native inverse calculus supplies the
actual Fréchet derivative. The final theorem assembles these implications on
one arbitrary C*-algebra carrier. The minus domain remains explicit.

Inner-derivation commutators, rational-map derivatives, and logarithmic
residuals are distinct constructions. No equality with an operator-log
derivative, Umegaki divergence, BKM metric, or geometric curvature is asserted.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzResolvent

open InfoGeometry.Core.IdempotentGraphGrassmannian
open QuadraticResolventCalculus LogarithmicResolventPositivity

attribute [local instance 100] LieRing.ofAssociativeRing

section Ring

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

/-- The two zero wing tests imply a doubled square-zero interaction, not a
zero interaction. No cancellation or positivity is used here. -/
theorem twice_interaction_square_eq_zero_of_wing_tests (A C : B)
    (hplus : comm (genSig P A C) (conePlus P A) = 0)
    (hminus : comm (genSig P A C) (coneMinus P C) = 0) :
    (2 : ℤ) • (genV P A C * genV P A C) = 0 := by
  have h : (2 : ℤ) • (genV P A C * genV P A C) =
      comm (genSig P A C) (conePlus P A) * coneMinus P C -
        comm (genSig P A C) (coneMinus P C) * conePlus P A := by
    peirce_nf hP
  simpa only [hplus, hminus, zero_mul, sub_self] using h

/-- In a torsion-free additive carrier the factor two can be cancelled.
The resulting square-zero condition still need not imply `genV = 0`. -/
theorem interaction_square_eq_zero_of_wing_tests [NoZeroSMulDivisors ℤ B]
    (A C : B)
    (hplus : comm (genSig P A C) (conePlus P A) = 0)
    (hminus : comm (genSig P A C) (coneMinus P C) = 0) :
    genV P A C * genV P A C = 0 := by
  exact (smul_eq_zero.mp
    (twice_interaction_square_eq_zero_of_wing_tests hP A C hplus hminus)).resolve_left
      (by decide)

/-- The initial displaced cut feeds every finite level of the already-owned
orthogonal Peirce defect tower. The iteration depth is arbitrary. -/
theorem displaced_defect_iterates_cycle_split (A C : B) (n : ℕ) :
    idempotencyDefect^[n + 1] (P + genPhi P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) +
        idempotencyDefect^[n] (qgtMinus P A C) := by
  have hstart : idempotencyDefect (P + genPhi P A C) = genV P A C := by
    simp only [idempotencyDefect]
    peirce_nf hP
  rw [Function.iterate_succ_apply, hstart]
  exact genV_defect_iterates_cycle_split hP A C n

end Ring

section CStar

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {P : B}

/-- The adjoint-paired Peirce interaction is a positive Gram sum in the
ambient C*-algebra. Idempotence is unnecessary for this positivity alone. -/
theorem adjoint_interaction_nonneg (hPs : star P = P) (X : B) :
    0 ≤ genV P X (star X) := by
  have hs : star (conePlus P X) = coneMinus P (star X) := by
    simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPs, mul_assoc]
  rw [genV, anticomm, ← hs]
  exact add_nonneg (mul_star_self_nonneg _) (star_mul_self_nonneg _)

/-- The plus denominator is automatically strictly positive, hence a unit,
for every positive adjoint-paired Peirce deformation. -/
theorem plus_denominator_strictlyPositive (hPs : star P = P) (X : B) :
    IsStrictlyPositive (1 + genV P X (star X)) :=
  isStrictlyPositive_one.add_nonneg (adjoint_interaction_nonneg hPs X)

omit [PartialOrder B] [StarOrderedRing B] in
/-- The Peirce quadratic identity transports the explicit unit-domain
condition to native Fréchet calculus on the entire operator algebra. -/
theorem peirce_resolvent_coordinate_hasFDerivAt
    (hP : P * P = P) (A C : B) (s : ℝ)
    (hunit : IsUnit (1 + s • genV P A C)) :
    HasFDerivAt (resolventCoordinate s)
      (resolventCoordinateDerivative s (genPhi P A C)) (genPhi P A C) := by
  have hsq := (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1
  apply hasFDerivAt_resolventCoordinate
  simpa only [hsq] using hunit

/-- No extra invertibility assumption is needed in the plus domain. -/
theorem adjoint_plus_coordinate_hasFDerivAt
    (hP : P * P = P) (hPs : star P = P) (X : B) :
    HasFDerivAt (resolventCoordinate (1 : ℝ))
      (resolventCoordinateDerivative (1 : ℝ) (genPhi P X (star X)))
      (genPhi P X (star X)) := by
  apply peirce_resolvent_coordinate_hasFDerivAt hP X (star X) 1
  simpa only [one_smul] using (plus_denominator_strictlyPositive hPs X).isUnit

omit [StarOrderedRing B] in
/-- The minus coordinate is differentiated on its separately stated domain. -/
theorem adjoint_minus_coordinate_hasFDerivAt
    (hP : P * P = P) (X : B)
    (hminus : IsStrictlyPositive (1 - genV P X (star X))) :
    HasFDerivAt (resolventCoordinate (-1 : ℝ))
      (resolventCoordinateDerivative (-1 : ℝ) (genPhi P X (star X)))
      (genPhi P X (star X)) := by
  apply peirce_resolvent_coordinate_hasFDerivAt hP X (star X) (-1)
  simpa only [neg_one_smul, sub_eq_add_neg] using hminus.isUnit

omit [PartialOrder B] [StarOrderedRing B] in
/-- In the adjoint-paired setting the rational coordinate and the native
Schwarz action have exactly the same zero locus, on the stated unit domain. -/
theorem peirce_schwarz_iff_resolventCoordinate_zero
    (hP : P * P = P) (hPs : star P = P) (X : B) (s : ℝ)
    (hunit : IsUnit (1 + s • genV P X (star X))) :
    (⁅LieAlgebra.ad ℝ B (conePlus P X),
       LieAlgebra.ad ℝ B (coneMinus P (star X))⁆ = 0) ↔
      resolventCoordinate s (genPhi P X (star X)) = 0 := by
  have hs : star (conePlus P X) = coneMinus P (star X) := by
    simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPs, mul_assoc]
  have hsq := (archetype_A3_nilpotent_cones_and_tetraktys_table hP X (star X)).2.2.1
  have hunit' : IsUnit (1 + s • (genPhi P X (star X) * genPhi P X (star X))) := by
    simpa only [hsq] using hunit
  rw [SquareZeroCStarRigidity.peirce_ad_commutator_eq_zero_iff ℝ hP hPs X,
    resolventCoordinate_eq_zero_iff s _ hunit']
  constructor
  · intro h
    simp only [genPhi, ← hs, h, star_zero, add_zero]
  · intro h
    apply (SquareZeroCStarRigidity.square_zero_coupled_square_eq_zero_iff
      (conePlus_mul_conePlus hP X X)).mp
    have he : conePlus P X + star (conePlus P X) = genPhi P X (star X) := by
      rw [hs]
      rfl
    rw [he, h, zero_mul]

/-- The positive logarithmic residual detects exactly the same vanishing
condition as the native inner-derivation commutator. -/
theorem peirce_schwarz_iff_plus_residual_zero
    (hP : P * P = P) (hPs : star P = P) (X : B) :
    (⁅LieAlgebra.ad ℝ B (conePlus P X),
       LieAlgebra.ad ℝ B (coneMinus P (star X))⁆ = 0) ↔
      CFC.log (1 + genV P X (star X)) -
        genV P X (star X) * Ring.inverse (1 + genV P X (star X)) = 0 :=
  (SquareZeroCStarRigidity.peirce_ad_commutator_eq_zero_iff_genV ℝ hP hPs X).trans
    (plus_residual_eq_zero_iff _ (plus_denominator_strictlyPositive hPs X)).symm

/-- The analogous minus equivalence keeps the independent positive-domain
condition visible. -/
theorem peirce_schwarz_iff_minus_residual_zero
    (hP : P * P = P) (hPs : star P = P) (X : B)
    (hminus : IsStrictlyPositive (1 - genV P X (star X))) :
    (⁅LieAlgebra.ad ℝ B (conePlus P X),
       LieAlgebra.ad ℝ B (coneMinus P (star X))⁆ = 0) ↔
      genV P X (star X) * Ring.inverse (1 - genV P X (star X)) +
        CFC.log (1 - genV P X (star X)) = 0 :=
  (SquareZeroCStarRigidity.peirce_ad_commutator_eq_zero_iff_genV ℝ hP hPs X).trans
    (minus_residual_eq_zero_iff _ hminus).symm

/-- The positive-star result connects vanishing native Schwarz action,
actual rational-map differentiability, and logarithmic residual positivity.
All conclusions concern the same operator algebra and the same Peirce pair. -/
theorem peirce_positive_resolvent_synthesis
    (hP : P * P = P) (hPs : star P = P) (X : B)
    (hminus : IsStrictlyPositive (1 - genV P X (star X))) :
    IsStrictlyPositive (1 + genV P X (star X)) ∧
    (⁅LieAlgebra.ad ℝ B (conePlus P X),
       LieAlgebra.ad ℝ B (coneMinus P (star X))⁆ = 0 ↔ genV P X (star X) = 0) ∧
    HasFDerivAt (resolventCoordinate (1 : ℝ))
      (resolventCoordinateDerivative (1 : ℝ) (genPhi P X (star X)))
      (genPhi P X (star X)) ∧
    HasFDerivAt (resolventCoordinate (-1 : ℝ))
      (resolventCoordinateDerivative (-1 : ℝ) (genPhi P X (star X)))
      (genPhi P X (star X)) ∧
    0 ≤ CFC.log (1 + genV P X (star X)) -
      genV P X (star X) * Ring.inverse (1 + genV P X (star X)) ∧
    0 ≤ genV P X (star X) * Ring.inverse (1 - genV P X (star X)) +
      CFC.log (1 - genV P X (star X)) := by
  exact ⟨plus_denominator_strictlyPositive hPs X,
    SquareZeroCStarRigidity.peirce_ad_commutator_eq_zero_iff_genV ℝ hP hPs X,
    adjoint_plus_coordinate_hasFDerivAt hP hPs X,
    adjoint_minus_coordinate_hasFDerivAt hP X hminus,
    plus_residual_nonneg _ (plus_denominator_strictlyPositive hPs X),
    minus_residual_nonneg _ hminus⟩

end CStar

end InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralSchwarzResolvent

end
