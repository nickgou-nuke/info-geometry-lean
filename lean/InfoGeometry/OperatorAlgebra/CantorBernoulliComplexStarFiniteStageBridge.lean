/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge

/-!
# Full finite matrix stages inside the corrected complex-* quotient

The corrected complexified-real Cuntz quotient already represents every word
matrix unit on the Bernoulli boundary.  This owner packages the complete
finite noncommutative matrix stage, not merely its diagonal, and proves that
its concrete representation agrees with the existing boundary `StarAlgHom`.
No map from the full infinite Cuntz algebra into a finite matrix algebra is
claimed.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge

open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzStarRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliTensorQuotientPrefixMeasureBridge
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

abbrev Stage (n : ℕ) := BitWordMatrixStage n

def complexStarFiniteStageElement (n : ℕ) (A : Stage n) :
    ComplexStarCuntzAlg Bool :=
  ∑ u : BitWord n, ∑ v : BitWord n,
    A u v •
      (complexStarWord (List.ofFn u) *
        star (complexStarWord (List.ofFn v)))

theorem complexStarFiniteStageElement_representation
    (n : ℕ) (A : Stage n) :
    cantorBernoulliComplexStarLift (complexStarFiniteStageElement n A) =
      boundaryRep n A := by
  unfold complexStarFiniteStageElement
  rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hA :
      (∑ i, ∑ j, Matrix.single i j (A i j)) u v = A u v := by
    exact congrArg (fun M => M u v) (Matrix.matrix_eq_sum_single A).symm
  rw [hA]
  have hsingle : Matrix.single u v (A u v) =
      A u v • Matrix.single u v (1 : ℂ) := by
    ext i j
    simp [Matrix.single]
  rw [hsingle, map_smul,
    complexStarQuotient_bitWordMatrixUnit_eq_boundaryMatrixUnit,
    matrixUnit_generator_transport]
  change A u v • bitWordUnit n u v = A u v • bitWordUnit n u v
  rfl

theorem complexStarFiniteStageElement_matrixUnit
    (n : ℕ) (u v : BitWord n) :
    complexStarFiniteStageElement n (Matrix.single u v (1 : ℂ)) =
      complexStarWord (List.ofFn u) *
        star (complexStarWord (List.ofFn v)) := by
  unfold complexStarFiniteStageElement
  classical
  change (∑ x : BitWord n, ∑ y : BitWord n,
      (Matrix.single u v (1 : ℂ)) x y •
        (complexStarWord (List.ofFn x) *
          star (complexStarWord (List.ofFn y)))) = _
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · simp [Matrix.single]
    · intro b _ hb
      simp [Matrix.single, Ne.symm hb]
    · simp
  · intro b _ hb
    have hne : u ≠ b := Ne.symm hb
    simp [Matrix.single, hne]
  · simp

/-! The quotient stage is read through the already existing positive normalized
finite C⋆ trace family.  This is a stage readout, not a state on the full
quotient and not a replacement for the native colimit construction. -/

def complexStarFiniteStageMatrix (n : ℕ) (A : Stage n) :
    MatrixStage n :=
  bitWordStageStarAlgEquiv n A

def complexStarFiniteStageTrace (n : ℕ) (A : Stage n) : ℂ :=
  matrixTraceState n (complexStarFiniteStageMatrix n A)

theorem complexStarFiniteStageTrace_eq_matrixTrace
    (n : ℕ) (A : Stage n) :
    complexStarFiniteStageTrace n A =
      bitWordMatrixTraceFunctional n A := by
  rw [complexStarFiniteStageTrace,
    complexStarFiniteStageMatrix]
  exact (bitWordStageTrace_transport n A).symm

theorem complexStarFiniteStageTrace_one (n : ℕ) :
    complexStarFiniteStageTrace n (1 : Stage n) = 1 := by
  rw [complexStarFiniteStageTrace]
  rw [complexStarFiniteStageMatrix, bitWordStageStarAlgEquiv_map_one]
  exact matrixTraceState_one n

theorem complexStarFiniteStageTrace_transition
    (n : ℕ) (A : Stage n) :
    complexStarFiniteStageTrace (n + 1)
        (bitWordDyadicStarEmbedding n A) =
      complexStarFiniteStageTrace n A := by
  rw [complexStarFiniteStageTrace_eq_matrixTrace,
    complexStarFiniteStageTrace_eq_matrixTrace]
  exact bitWordDyadicStarEmbedding_trace_compatible n A

/-! The corrected quotient matrix-unit readout agrees with the already
constructed algebraic gauge functional on the corresponding word core
monomial.  This is the noncommutative word-pair compatibility wire; it is not
an extension of `phi0` to the full quotient or its infinite completion. -/

theorem complexStarFiniteStageTrace_matrixUnit_eq_phi0
    (n : ℕ) (u v : BitWord n) :
    complexStarFiniteStageTrace n (Matrix.single u v (1 : ℂ)) =
      phi0 (wordMonomial (List.ofFn u) (List.ofFn v)) := by
  rw [complexStarFiniteStageTrace_eq_matrixTrace,
    bitWordMatrixTraceFunctional_single_eq_gaugeState,
    phi0_monomial]

end InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
