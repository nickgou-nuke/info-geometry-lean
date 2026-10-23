/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
import InfoGeometry.Canonical.ConcreteCompatibleCuntzFaithfulness
import InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageGNSBridge
import InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCore
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixFaithfulness
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
import InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge
import InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy
import InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalHilbertSchmidt
import InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding

/-!
# Finite boundary range and native GNS trace

The concrete boundary representation and the native filtered GNS representation
have different ambient operator spaces.  This owner compares them on their
common finite matrix source by passing through the actual range of the
boundary representation.  It does not identify the spatial boundary vector
state with the gauge state; those states are different on off-diagonal words.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.CantorBernoulliBoundaryRangeGNSBridge

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open InfoGeometry.Canonical.CantorBernoulliComplexStarFiniteStageGNSBridge
open InfoGeometry.Canonical.CantorBernoulliComplexStarBinaryGaugeFiniteCore
open InfoGeometry.OperatorAlgebra.CantorBernoulliComplexStarFiniteStageBridge
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.Canonical.ConcreteCompatibleCuntzFaithfulness
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixFaithfulness
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.CantorBernoulliDiagTraceBridge
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceEnergy
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalHilbertSchmidt
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderProjectionBridge
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure
open scoped ComplexOrder InnerProductSpace
open MeasureTheory

abbrev Stage (n : ℕ) := BitWordMatrixStage n

abbrev BoundaryRange (n : ℕ) :=
  LinearMap.range (bitWordMatrixLinearRepresentation n)

def boundaryRangeEquiv (n : ℕ) :
    Stage n ≃ₗ[ℂ] BoundaryRange n :=
  LinearEquiv.ofBijective
    (bitWordMatrixLinearRepresentation n).rangeRestrict
    ⟨by
      intro A B h
      apply bitWordMatrixLinearRepresentation_injective n
      exact congrArg Subtype.val h,
      LinearMap.surjective_rangeRestrict _⟩

def boundaryRangeElement (n : ℕ) (A : Stage n) : BoundaryRange n :=
  ⟨boundaryRep n A, ⟨A, rfl⟩⟩

def boundaryRangeTrace (n : ℕ) : BoundaryRange n →ₗ[ℂ] ℂ :=
  (bitWordMatrixTraceFunctional n).comp
    (boundaryRangeEquiv n).symm.toLinearMap

theorem boundaryRangeTrace_stage (n : ℕ) (A : Stage n) :
    boundaryRangeTrace n (boundaryRangeElement n A) =
      bitWordMatrixTraceFunctional n A := by
  rw [boundaryRangeTrace]
  change bitWordMatrixTraceFunctional n
    ((boundaryRangeEquiv n).symm (boundaryRangeElement n A)) = _
  rw [show boundaryRangeElement n A = boundaryRangeEquiv n A by rfl]
  simp

/-! The same finite boundary image is also available as the genuine range of
    the finite `StarAlgHom`.  The older `BoundaryRange` is retained for the
    linear trace API; this equivalence supplies the missing multiplicative and
    star carrier without changing that API. -/

abbrev BoundaryStarRange (n : ℕ) := (boundaryRep n).range

def boundaryRangeToStarRange (n : ℕ) :
    BoundaryRange n ≃ₗ[ℂ] BoundaryStarRange n where
  toFun x :=
    ⟨x.1, by
      rcases x.2 with ⟨A, hA⟩
      exact ⟨A, hA⟩⟩
  invFun x :=
    ⟨x.1, by
      rcases x.2 with ⟨A, hA⟩
      exact ⟨A, hA⟩⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

@[simp] theorem boundaryRangeToStarRange_coe
    (n : ℕ) (x : BoundaryRange n) :
    (boundaryRangeToStarRange n x : BoundaryOperator) = x :=
  rfl

def boundaryStarRangeTrace (n : ℕ) :
    BoundaryStarRange n →ₗ[ℂ] ℂ :=
  (boundaryRangeTrace n).comp
    (boundaryRangeToStarRange n).symm.toLinearMap

theorem boundaryStarRangeTrace_stage (n : ℕ) (A : Stage n) :
    boundaryStarRangeTrace n
        ⟨boundaryRep n A, ⟨A, rfl⟩⟩ =
      bitWordMatrixTraceFunctional n A := by
  rw [boundaryStarRangeTrace]
  change boundaryRangeTrace n (boundaryRangeElement n A) = _
  exact boundaryRangeTrace_stage n A

/-! The pulled-back trace on the actual boundary range is compatible with the
native full-matrix `StarAlgHom` successor.  This statement is about arbitrary
matrix stages: no diagonalization, normality, or eigenbasis is used. -/

theorem boundaryRangeTrace_starTransition
    (n : ℕ) (A : Stage n) :
    boundaryRangeTrace (n + 1)
        (boundaryRangeElement (n + 1)
          (bitWordDyadicStarEmbedding n A)) =
      boundaryRangeTrace n (boundaryRangeElement n A) := by
  rw [boundaryRangeTrace_stage, boundaryRangeTrace_stage]
  exact bitWordDyadicStarEmbedding_trace_compatible n A

/-! The projective-limit measure sees the diagonal readout of an arbitrary
finite matrix through the normalized trace.  The source remains the full
noncommutative matrix stage; only this scalar functional factors through
`diagonalPart`. -/

theorem boundaryRangeTrace_projectiveDiagonalReadout
    (n : ℕ) (A : Stage n) :
    boundaryRangeTrace n (boundaryRangeElement n A) =
      ∫ q, diagonalPart n A (π n q) ∂projectiveLimitMeasure := by
  rw [boundaryRangeTrace_stage]
  calc
    bitWordMatrixTraceFunctional n A =
        bitWordMatrixTraceFunctional n
          (Matrix.diagonal (diagonalPart n A)) := by
      rw [bitWordMatrixTraceFunctional_apply,
        bitWordMatrixTraceFunctional_apply]
      simp [Matrix.trace, diagonalPart]
    _ = DiagTrace n (diagonalPart n A) :=
      bitWordMatrixTraceFunctional_diagonal n (diagonalPart n A)
    _ = ∫ q, diagonalPart n A (π n q) ∂projectiveLimitMeasure :=
      (projectiveLimitMeasure_integral_prefix_eq_DiagTrace n
        (diagonalPart n A)).symm

/-! The same finite-stage trace is recovered by the native GNS colimit on
every matrix, including nonnormal and nondiagonalizable matrices. -/

theorem boundaryRangeTrace_gaugeGNS_readout (n : ℕ) (A : Stage n) :
    boundaryRangeTrace n (boundaryRangeElement n A) =
      ⟪gaugeGNSColimitVacuum,
        globalStageRepresentationStarAlgHom
          gaugeStage gaugeSystem gaugeStateFamily n
          (CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n A))
          gaugeGNSColimitVacuum⟫_ℂ := by
  rw [boundaryRangeTrace_stage]
  calc
    bitWordMatrixTraceFunctional n A =
        bitWordMatrixGaugeReadout n A :=
      (bitWordMatrixGaugeReadout_eq_trace n A).symm
    _ = complexStarFiniteStageTrace n A := by
      rw [complexStarFiniteStageTrace_eq_matrixTrace,
        bitWordMatrixGaugeReadout_eq_trace]
    _ =
        ⟪gaugeGNSColimitVacuum,
          globalStageRepresentationStarAlgHom
            gaugeStage gaugeSystem gaugeStateFamily n
            (CStarMatrix.ofMatrixStarAlgEquiv
              (bitWordStageStarAlgEquiv n A))
            gaugeGNSColimitVacuum⟫_ℂ :=
      (gaugeGNSColimitVacuum_complexStarFiniteStage_expectation n A).symm

/-! The pulled-back trace has the full noncommutative Hilbert--Schmidt energy
on the actual represented boundary range.  No diagonal restriction or
simultaneous diagonalization is used. -/

theorem boundaryRangeTrace_star_mul_self_re_eq
    (n : ℕ) (A : Stage n) :
    (boundaryRangeTrace n
        (boundaryRangeElement n (star A * A))).re =
      (1 / (Fintype.card (BitWord n) : ℝ)) *
        (∑ u : BitWord n, ∑ v : BitWord n,
          Complex.normSq (A v u)) := by
  rw [boundaryRangeTrace_stage]
  exact bitWordMatrixTraceFunctional_star_mul_self_re_eq n A

/-! The same noncommutative energy is seen directly in the native filtered-GNS
    vacuum.  This composes the concrete boundary-range trace with the actual
    finite-stage GNS representation; no diagonal or normality hypothesis is
    introduced. -/

theorem boundaryRangeTrace_gaugeGNS_star_mul_self_re_eq
    (n : ℕ) (A : Stage n) :
    (⟪gaugeGNSColimitVacuum,
        globalStageRepresentationStarAlgHom
          gaugeStage gaugeSystem gaugeStateFamily n
          (CStarMatrix.ofMatrixStarAlgEquiv
            (bitWordStageStarAlgEquiv n (star A * A)))
          gaugeGNSColimitVacuum⟫_ℂ).re =
      (1 / (Fintype.card (BitWord n) : ℝ)) *
        (∑ u : BitWord n, ∑ v : BitWord n,
          Complex.normSq (A v u)) := by
  rw [← boundaryRangeTrace_gaugeGNS_readout n (star A * A)]
  exact boundaryRangeTrace_star_mul_self_re_eq n A

/-! The boundary-range trace transports the already proved finite equal-depth
KMS boundary identity.  The statement remains at an arbitrary finite matrix
stage; it is not an analytic KMS theorem for the infinite Cuntz completion. -/

theorem boundaryRangeTrace_finiteCore_kms_boundary
    (z : ℂ) (n : ℕ) (A B : Stage n) :
    boundaryRangeTrace n
        (boundaryRangeElement n (A * finiteCoreFlow n z B)) =
      boundaryRangeTrace n (boundaryRangeElement n (B * A)) := by
  rw [boundaryRangeTrace_stage, boundaryRangeTrace_stage]
  simpa [finiteCoreState] using finiteCore_kms_boundary z n A B

/-! The concrete boundary representation sends a finite diagonal matrix to the
finite sum of the corresponding word-indicator vectors on the vacuum.  The
remaining identification of that sum with the existing cylinder embedding is
deliberately a separate finite-partition theorem. -/

theorem boundaryRep_diagonal_vacuum_wordIndicator (n : ℕ) (f : DiagAlg n) :
    (boundaryRep n (Matrix.diagonal f)) vacuumL2 =
      ∑ u : BitWord n, f u •
        wordIndicatorLp (List.ofFn u) vacuumL2 := by
  rw [boundaryRep_diagonal]
  change
    (∑ u : BitWord n, f u •
      operatorCylinderProjection (List.ofFn u)) vacuumL2 =
      ∑ u : BitWord n, f u •
        wordIndicatorLp (List.ofFn u) vacuumL2
  have hsum :
      (∑ u : BitWord n, f u •
        operatorCylinderProjection (List.ofFn u)) vacuumL2 =
        ∑ u : BitWord n, f u •
          (operatorCylinderProjection (List.ofFn u) vacuumL2) := by
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [operatorCylinderProjection_apply_eq_wordIndicator]

theorem boundaryRep_diagonal_vacuum_eq_diagonalCylinderL2
    (n : ℕ) (f : DiagAlg n) :
    (boundaryRep n (Matrix.diagonal f)) vacuumL2 =
      diagonalCylinderL2 n f := by
  classical
  rw [boundaryRep_diagonal_vacuum_wordIndicator]
  apply Lp.ext
  have hsum :
      ((∑ u : BitWord n, f u •
          wordIndicatorLp (List.ofFn u) vacuumL2 : L2Boundary) :
          Boundary → ℂ) =ᵐ[μC]
        (fun x => ∑ u : BitWord n,
          ((f u • wordIndicatorLp (List.ofFn u) vacuumL2 : L2Boundary) :
            Boundary → ℂ) x) := by
    simpa using
      (Lp.coeFn_fun_finsetSum (μ := μC)
        (s := (Finset.univ : Finset (BitWord n)))
        (f := fun u : BitWord n =>
          f u • wordIndicatorLp (List.ofFn u) vacuumL2))
  have hword (u : BitWord n) :
      ((wordIndicatorLp (List.ofFn u) vacuumL2 : L2Boundary) :
          Boundary → ℂ) =ᵐ[μC]
        wordIndicatorFunction (List.ofFn u) vacuumL2 :=
    (wordIndicatorFunction_memLp (List.ofFn u) vacuumL2).coeFn_toLp
  have hsmul (u : BitWord n) :
      ((f u • wordIndicatorLp (List.ofFn u) vacuumL2 : L2Boundary) :
          Boundary → ℂ) =ᵐ[μC]
        f u • ((wordIndicatorLp (List.ofFn u) vacuumL2 : L2Boundary) :
          Boundary → ℂ) :=
    Lp.coeFn_smul (f u) (wordIndicatorLp (List.ofFn u) vacuumL2)
  have hword_all : ∀ᶠ x in ae μC, ∀ u ∈ (Finset.univ : Finset (BitWord n)),
      ((wordIndicatorLp (List.ofFn u) vacuumL2 : L2Boundary) :
          Boundary → ℂ) x = wordIndicatorFunction (List.ofFn u) vacuumL2 x := by
    rw [Finset.eventually_all]
    intro u hu
    exact hword u
  have hsmul_all : ∀ᶠ x in ae μC, ∀ u ∈ (Finset.univ : Finset (BitWord n)),
      ((f u • wordIndicatorLp (List.ofFn u) vacuumL2 : L2Boundary) :
          Boundary → ℂ) x =
        (f u • ((wordIndicatorLp (List.ofFn u) vacuumL2 : L2Boundary) :
          Boundary → ℂ)) x := by
    rw [Finset.eventually_all]
    intro u hu
    exact hsmul u
  have hvac := vacuumL2_coeFn
  have hdiag := diagonalCylinderL2_coeFn n f
  filter_upwards [hsum, hword_all, hsmul_all, hvac, hdiag]
    with x hsumx hwordx hsmulx hvacx hdiagx
  rw [hsumx, hdiagx]
  calc
    (∑ u : BitWord n,
        ((f u • wordIndicatorLp (List.ofFn u) vacuumL2 : L2Boundary) :
          Boundary → ℂ) x) =
        ∑ u : BitWord n, f u *
          (wordBranchSet (List.ofFn u)).indicator (fun _ => (1 : ℂ)) x := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hsmulx u hu, Pi.smul_apply, hwordx u hu]
      by_cases hmem : x ∈ wordBranchSet (List.ofFn u)
      · rw [wordIndicatorFunction, Set.indicator_of_mem hmem]
        rw [hvacx]
        rw [Set.indicator_of_mem hmem]
        simp
      · simp [wordIndicatorFunction, Set.indicator_apply, hmem]
    _ = f (boundaryPrefix n x) := by
      calc
        (∑ u : BitWord n, f u *
            (wordBranchSet (List.ofFn u)).indicator (fun _ => (1 : ℂ)) x) =
            f (boundaryPrefix n x) *
              (wordBranchSet (List.ofFn (boundaryPrefix n x))).indicator
                (fun _ => (1 : ℂ)) x := by
          refine Finset.sum_eq_single (a := boundaryPrefix n x)
            (s := (Finset.univ : Finset (BitWord n)))
            (f := fun u : BitWord n => f u *
              (wordBranchSet (List.ofFn u)).indicator (fun _ => (1 : ℂ)) x) ?_ ?_
          · intro u hu hne
            have hnot : x ∉ wordBranchSet (List.ofFn u) := by
              intro hmem
              apply hne
              exact ((wordBranchSet_ofFn_mem_iff n u x).mp hmem).symm
            rw [Set.indicator_apply, if_neg hnot]
            simp
          · intro hnotmem
            simp at hnotmem
        _ = f (boundaryPrefix n x) := by
          have hmem : x ∈ wordBranchSet
              (List.ofFn (boundaryPrefix n x)) :=
            (wordBranchSet_ofFn_mem_iff n (boundaryPrefix n x) x).mpr rfl
          rw [Set.indicator_of_mem hmem]
          simp

/-! The concrete boundary vector functional and the native projective-limit
diagonal readout agree on the full finite diagonal stage.  The operator source
is still the finite noncommutative matrix stage; only its diagonal observable
is being evaluated here. -/

theorem boundaryRep_diagonal_vacuum_inner_eq_projectiveIntegral
    (n : ℕ) (f : DiagAlg n) :
    inner ℂ vacuumL2
        ((boundaryRep n (Matrix.diagonal f)) vacuumL2) =
      ∫ q, f (π n q) ∂projectiveLimitMeasure := by
  have hone : diagonalCylinderL2 n (1 : DiagAlg n) = vacuumL2 := by
    apply Lp.ext
    filter_upwards [diagonalCylinderL2_coeFn n (1 : DiagAlg n),
      vacuumL2_coeFn] with x hx hvac
    rw [hx, hvac]
    simp [InfoGeometry.Canonical.UHFInductiveColimitBoundary.cylinder]
  rw [boundaryRep_diagonal_vacuum_eq_diagonalCylinderL2 n f, ← hone,
    diagonalCylinderL2_inner]
  simpa using (projectiveLimitMeasure_integral_prefix_eq_DiagTrace n f).symm

end InfoGeometry.Canonical.CantorBernoulliBoundaryRangeGNSBridge
