/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionFiveGradeOperatorBridge
import InfoGeometry.Algebra.ZornLeftMultiplicationDefect
import InfoGeometry.Canonical.OperatorZornFourPotentialGauge

/-!
# Nonassociative Zorn Operator Closure, Five-Graded Endomorphism Algebra, and Curvature/Bianchi Defects

This module packages the three kernel-checked algebraic pillars connecting
nonassociative Zorn multiplication defects, five-graded operator closure, and
noncommutative-coefficient gauge curvature:

1. **Five-Grading on the Full Zorn Endomorphism Algebra (`SplitOctonionFiveGradeOperatorBridge`)**:
   On the canonical real Zorn carrier `O`, the normalized left/right multiplication
   difference `t = (1 / 2) • (L_ℓ - R_ℓ)` satisfies `t³ = t`, decomposes
   `E = Module.End ℝ O` into the five adjoint eigenspaces `{-2, -1, 0, +1, +2}` with
   exact reconstruction, satisfies `E_i · E_j ⊆ E_{i+j}` and `[E_i, E_j] ⊆ E_{i+j}`,
   and obeys `(ad_t)⁵ - 5 (ad_t)³ + 4 ad_t = 0`.
2. **Strict Lie-Span Enlargement by Nonassociative Multiplication Defects (`ZornLeftMultiplicationDefect`)**:
   The associator operator `A_{X,Y} = L_{X Y} - L_X L_Y` satisfies
   `[L_X, L_Y] = L_{[X,Y]} - 2 • A_{X,Y}`, belongs to the Lie subalgebra generated
   by `range(L)`, annihilates the unit `1`, and strictly enlarges the linear space
   of left multiplications: `LinearMap.range leftMultiplication < (LieSubalgebra.lieSpan ℝ (Module.End ℝ Z) (Set.range leftMultiplication)).toSubmodule`.
3. **Full Noncommutative-Coefficient Zorn Curvature & Six-Term Bianchi Identity (`OperatorZornFourPotentialGauge`)**:
   Over an arbitrary associative coefficient ring `A`, the covariant derivative
   `∇_μ X = δ_{p_μ} X + Φ_μ X` has curvature retaining the background commutator
   derivation and both ordered associators (`curvatureAction_eq`), and cyclic
   Bianchi sum retaining the full six-term Akivis associator alternation (`bianchi_eq`).

Scope note: The five-grading acts on the full endomorphism ring `Module.End ℝ O`,
whereas `left_action_range_lt_native_lieSpan` establishes strict enlargement of
`range(L)` inside its generated Lie subalgebra. No unproved identification of
that generated Lie subalgebra with all of `Module.End ℝ O` is asserted.
-/

namespace InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis

open InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge
open InfoGeometry.Lie.SplitOctonionFiveGradeOperatorBridge
open InfoGeometry.Physics.Algebra
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornPinorReconstruction
open InfoGeometry.Algebra.ZornLeftCAR
open InfoGeometry.Canonical.OperatorZornFourPotentialGauge

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Three-Pillar Synthesis of Zorn Five-Grade Closure, Associator Lie Enlargement,
and Noncommutative-Coefficient Curvature/Bianchi Defects**:
Simultaneously witnesses:
1. The Zorn tripotent `t = peirceDefectOperator = (1/2)(L_ℓ - R_ℓ)` (`t³ = t`),
   exact 5-grade endomorphism reconstruction, native adjoint eigenspace
   identification, and quintic annihilator `(ad_t)⁵ - 5(ad_t)³ + 4 ad_t = 0`;
2. The commutator-associator relation `[L_X, L_Y] = L_{[X,Y]} - 2 • A_{X,Y}` and
   strict Lie-closure enlargement `range(L) < LieSpan(range(L))`;
3. The noncommutative-coefficient Zorn curvature decomposition with both ordered
   associators (`curvatureAction_eq`) and the cyclic Bianchi identity with the
   six-term alternating associator (`bianchi_eq`). -/
theorem zorn_five_grade_associator_enlargement_and_curvature_bianchi
    {A : Type*} [Ring A]
    (T : CarrierEnd) (k : FiveGrade)
    (X Y : Z)
    (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu rho : Fin 4) (Ψ : OperatorZornMatrix A) :
    -- Pillar 1: Zorn left/right tripotent and 5-graded endomorphism decomposition
    (peirceDefectOperator =
       (1 / 2 : ℝ) •
         (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.leftMultiplication
           InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit -
          InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.rightMultiplication
           InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) ∧
     peirceDefectOperator * peirceDefectOperator * peirceDefectOperator =
       peirceDefectOperator ∧
     fiveGradeRecomposeLinear peirceDefectOperator
       (fiveGradeDecomposeLinear peirceDefectOperator T) = T ∧
     fiveGradeRange peirceDefectOperator k =
       (LieAlgebra.ad ℝ CarrierEnd peirceDefectOperator).eigenspace
         (fiveGradeValue k : ℝ) ∧
     LieAlgebra.ad ℝ CarrierEnd peirceDefectOperator ^ 5 -
       (5 : ℝ) • LieAlgebra.ad ℝ CarrierEnd peirceDefectOperator ^ 3 +
       (4 : ℝ) • LieAlgebra.ad ℝ CarrierEnd peirceDefectOperator = 0) ∧
    -- Pillar 2: Associator multiplication defect and strict Lie-span enlargement
    (leftMultiplication X * leftMultiplication Y -
       leftMultiplication Y * leftMultiplication X =
       leftMultiplication (ZornVectorMatrix.commutator X Y) -
         2 • multiplicationDefect X Y ∧
     multiplicationDefect X Y ∈
       LieSubalgebra.lieSpan ℝ (Module.End ℝ Z)
         (Set.range leftMultiplication) ∧
     LinearMap.range leftMultiplication <
       (LieSubalgebra.lieSpan ℝ (Module.End ℝ Z)
         (Set.range leftMultiplication)).toSubmodule) ∧
    -- Pillar 3: Noncommutative-coefficient Zorn curvature and 6-term Akivis Bianchi identity
    (curvatureAction p Phi mu nu Ψ =
       coefficientDeriv (coefficientBracket (p mu) (p nu)) Ψ +
         fieldStrength p Phi mu nu * Ψ -
           associator (Phi mu) (Phi nu) Ψ + associator (Phi nu) (Phi mu) Ψ ∧
     bianchi p Phi mu nu rho =
       coefficientDeriv (coefficientBracket (p mu) (p nu)) (Phi rho) +
         coefficientDeriv (coefficientBracket (p nu) (p rho)) (Phi mu) +
           coefficientDeriv (coefficientBracket (p rho) (p mu)) (Phi nu) -
             associatorAlternation (Phi mu) (Phi nu) (Phi rho)) := by
  rcases zorn_tripotent_five_grade_operator_synthesis T k with
    ⟨hT1, hT2, _, _, hT5, hT6, hT7⟩
  exact ⟨⟨hT1, hT2, hT5, hT6, hT7⟩,
    ⟨leftMultiplication_commutator_defect X Y,
     multiplicationDefect_mem_native_lieSpan X Y,
     left_action_range_lt_native_lieSpan⟩,
    ⟨curvatureAction_eq p Phi mu nu Ψ,
     bianchi_eq p Phi mu nu rho⟩⟩

end InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis
