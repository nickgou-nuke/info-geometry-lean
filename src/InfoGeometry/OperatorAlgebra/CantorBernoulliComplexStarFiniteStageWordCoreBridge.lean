/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-!
# Arbitrary finite matrix stages and the algebraic gauge word core

This owner connects the complete finite noncommutative matrix stage to the
existing algebraic word-core functional `phi0`.  The matrix is arbitrary: the
proof expands it in all matrix units and lets the gauge kernel annihilate only
unequal word pairs.  No diagonalization, commutativity, or spatial-state
identification is used.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageWordCoreBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

abbrev WordCore :=
  InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge.WordCore

def wordCoreFiniteStageElement (n : ℕ) (A : BitWordMatrixStage n) : WordCore :=
  ∑ u : BitWord n, ∑ v : BitWord n,
    A u v • wordMonomial (List.ofFn u) (List.ofFn v)

theorem phi0_wordCoreFiniteStageElement_eq_complexStarFiniteStageTrace
    (n : ℕ) (A : BitWordMatrixStage n) :
    phi0 (wordCoreFiniteStageElement n A) =
      complexStarFiniteStageTrace n A := by
  calc
    phi0 (wordCoreFiniteStageElement n A) =
        bitWordMatrixGaugeReadout n A := by
      unfold wordCoreFiniteStageElement bitWordMatrixGaugeReadout
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [map_sum, Finset.sum_eq_single u]
      · rw [map_smul, phi0_monomial, canonicalGaugeState_word]
        simp only [List.length_ofFn]
        simp
      · intro v hv hvu
        rw [map_smul, phi0_monomial, canonicalGaugeState_word]
        simp only [List.length_ofFn]
        have hlist : List.ofFn u ≠ List.ofFn v := by
          intro h
          exact hvu (List.ofFn_injective h).symm
        simp [hlist]
      · simp
    _ = bitWordMatrixTraceFunctional n A :=
      bitWordMatrixGaugeReadout_eq_trace n A
    _ = complexStarFiniteStageTrace n A :=
      (complexStarFiniteStageTrace_eq_matrixTrace n A).symm

end InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageWordCoreBridge
