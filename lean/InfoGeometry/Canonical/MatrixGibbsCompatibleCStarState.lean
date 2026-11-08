/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
import InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet

/-!
# Native C⋆ states from the compatible matrix Gibbs net

The finite matrix Gibbs functionals already descend through the algebraic
matrix direct limit.  This owner transports those same functionals across the
existing type equivalences to Mathlib's finite C⋆ matrix stages.  It proves
that a compatible Hermitian Hamiltonian net gives a compatible family of
normalized positive C⋆ states, which is the actual input required by the
filtered GNS construction.

These matrix stages are not finite-stage realizations of a Cuntz family; no
Cuntz algebra completion or analytic KMS strip is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixGibbsCompatibleCStarState

open CStarStateColimit.Native
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

open scoped ComplexOrder

local instance cstarMatrixStageRealCFC (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrixStage n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance cstarMatrixStageNonnegSpectrum (n : ℕ) :
    NonnegSpectrumClass ℝ (CStarMatrixStage n) :=
  CStarAlgebra.instNonnegSpectrumClass

private def toMatrix (n : ℕ) : CStarMatrixStage n ≃⋆ₐ[ℂ] MatrixStage n :=
  (CStarMatrix.ofMatrixStarAlgEquiv).symm

/-- The matrix Gibbs functional transported to Mathlib's C⋆ matrix carrier. -/
def stageFunctional (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ) (n : ℕ) :
    CStarMatrixStage n →ₗ[ℂ] ℂ :=
  (gibbsFunctional (H n) (hH n) β).comp
    (toMatrix n).toAlgEquiv.toLinearMap

private theorem stageFunctional_monotone (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ) (n : ℕ) :
    Monotone (stageFunctional H hH β n) := by
  intro A B hAB
  rw [← sub_nonneg] at hAB ⊢
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hAB
  rw [← map_sub, hC]
  let C' : MatrixStage n := (toMatrix n) C
  have hC' : (toMatrix n) (star C * C) = star C' * C' := by
    rw [map_mul, map_star]
  change 0 ≤ gibbsFunctional (H n) (hH n) β ((toMatrix n) (star C * C))
  rw [hC']
  have hreal :
      0 ≤ (gibbsFunctional (H n) (hH n) β (star C' * C')).re :=
    gibbsFunctional_positive (H n) (hH n) β C'
  have hself : star (star C' * C') = star C' * C' := by
    simp only [star_mul, star_star]
  have hstar := gibbsFunctional_star (H n) (hH n) β (star C' * C')
  rw [hself] at hstar
  have him :
      (gibbsFunctional (H n) (hH n) β (star C' * C')).im = 0 := by
    have hstar' := hstar.symm
    exact Complex.conj_eq_iff_im.mp (by
      simpa only [Complex.star_def] using hstar')
  exact Complex.le_def.mpr ⟨hreal, by simpa using him.symm⟩

/-- The transported Gibbs functional is a normalized positive C⋆ state at
each finite matrix stage. -/
def stageState (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ) (n : ℕ) :
    State (CStarMatrixStage n) where
  functional := PositiveLinearMap.mk (stageFunctional H hH β n)
    (stageFunctional_monotone H hH β n)
  normalized := by
    change gibbsFunctional (H n) (hH n) β ((toMatrix n) 1) = 1
    rw [map_one]
    exact gibbsFunctional_one (H n) (hH n) β

/-- The native C⋆ states restrict along the concrete matrix embeddings whenever
the Hamiltonians are transported by those embeddings. -/
def compatibleStageStates (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ)
    (hHamiltonian : ∀ n, H (n + 1) = concreteStep n (H n)) :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      CStarMatrixStage cstarMatrixInductiveSystem where
  state := stageState H hH β
  compatible := by
    intro i j hij
    apply State.ext
    ext A
    change gibbsFunctional (H j) (hH j) β
        ((toMatrix j) (cstarConcreteMap hij A)) =
      gibbsFunctional (H i) (hH i) β ((toMatrix i) A)
    change gibbsFunctional (H j) (hH j) β
        ((CStarMatrix.ofMatrixStarAlgEquiv).symm (cstarConcreteMap hij A)) = _
    rw [cstarConcreteMap_toMatrixStage]
    exact (gibbsStageFunctional_compatible H hH β hHamiltonian hij
      ((toMatrix i) A))

/-- The imaginary-time Gibbs automorphism on a C⋆ matrix stage, transported
from the existing finite matrix Gibbs owner through the stage equivalence. -/
def stageImaginaryTimeAlgEquiv (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ) (n : ℕ) :
    CStarMatrixStage n ≃ₐ[ℂ] CStarMatrixStage n :=
  (toMatrix n).toAlgEquiv.trans
    ((gibbsImaginaryTimeAlgEquiv (H n) (hH n) β).trans
      (toMatrix n).toAlgEquiv.symm)

@[simp] theorem stageImaginaryTimeAlgEquiv_apply
    (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ) (n : ℕ)
    (A : CStarMatrixStage n) :
    stageImaginaryTimeAlgEquiv H hH β n A =
      (toMatrix n).symm
        (gibbsImaginaryTimeAlgEquiv (H n) (hH n) β ((toMatrix n) A)) :=
  rfl

/-- The transported normalized positive Gibbs state on each native C⋆ matrix
stage satisfies the same algebraic imaginary-time boundary identity as its
finite-matrix source.  This is a stagewise boundary theorem; it does not claim
an analytic strip extension or a completed-colimit KMS theorem. -/
theorem stageState_kms_boundary
    (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ) (n : ℕ)
    (A B : CStarMatrixStage n) :
    (stageState H hH β n).functional (A * B) =
      (stageState H hH β n).functional
        (B * stageImaginaryTimeAlgEquiv H hH β n A) := by
  change stageFunctional H hH β n (A * B) =
    stageFunctional H hH β n
      (B * stageImaginaryTimeAlgEquiv H hH β n A)
  change gibbsFunctional (H n) (hH n) β ((toMatrix n) (A * B)) =
    gibbsFunctional (H n) (hH n) β
      ((toMatrix n) (B * stageImaginaryTimeAlgEquiv H hH β n A))
  have hAB : (toMatrix n) (A * B) = (toMatrix n) A * (toMatrix n) B :=
    map_mul (toMatrix n) A B
  have hBσ : (toMatrix n)
      (B * stageImaginaryTimeAlgEquiv H hH β n A) =
      (toMatrix n) B * (toMatrix n)
        (stageImaginaryTimeAlgEquiv H hH β n A) :=
    map_mul (toMatrix n) B (stageImaginaryTimeAlgEquiv H hH β n A)
  have hσ : (toMatrix n) (stageImaginaryTimeAlgEquiv H hH β n A) =
      gibbsImaginaryTimeAlgEquiv (H n) (hH n) β ((toMatrix n) A) := by
    simp [stageImaginaryTimeAlgEquiv]
  rw [hAB, hBσ, hσ]
  exact gibbsFunctional_kms (H n) (hH n) β ((toMatrix n) A) ((toMatrix n) B)

end InfoGeometry.Canonical.MatrixGibbsCompatibleCStarState
