/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteSeedGibbsColimit
import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState

/-! Restrictions of the finite-seed algebraic Gibbs functional are compatible
native C⋆ states. Uncompiled sandbox candidate; no completed-state claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.AlgebraicKMSStateColimit

open CStarStateColimit.Native
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open scoped ComplexOrder

/-- Star preservation follows from Gibbs readback at a common finite stage. -/
theorem finiteSeedGibbs_star {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (x : Carrier) :
    normalizedDeltaWeightedFunctional
        (stageUnitToColimit k (gibbsDensityUnit H hH β)) (star x) =
      star (normalizedDeltaWeightedFunctional
        (stageUnitToColimit k (gibbsDensityUnit H hH β)) x) := by
  induction x using DirectLimit.induction with
  | _ j a =>
      let m := max k j
      have hkm : k ≤ m := le_max_left k j
      have hjm : j ≤ m := le_max_right k j
      let Hm : MatrixStage m := rawMap hkm H
      have hHm : Hm.IsHermitian := by
        change star (rawMap hkm H) = rawMap hkm H
        rw [← map_star]
        exact congrArg (rawMap hkm) hH
      let b : MatrixStage m := rawMap hjm a
      have hx : (⟦⟨j, a⟩⟧ : Carrier) = stageInjection m b :=
        (stageInjection_transition hjm a).symm
      rw [hx, ← stageInjection_star,
        finiteSeedGibbs_later_stage hkm H Hm hH hHm rfl β,
        finiteSeedGibbs_later_stage hkm H Hm hH hHm rfl β]
      exact gibbsFunctional_star Hm hHm β b

/-- Full complex-order positivity, including vanishing imaginary part. -/
theorem finiteSeedGibbs_nonneg_complex {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (x : Carrier) :
    0 ≤ normalizedDeltaWeightedFunctional
      (stageUnitToColimit k (gibbsDensityUnit H hH β)) (star x * x) := by
  have hreal := finiteSeedGibbs_positive H hH β x
  have hstar := finiteSeedGibbs_star H hH β (star x * x)
  have hself : star (star x * x) = star x * x := by
    simp only [star_mul, star_star]
  rw [hself] at hstar
  have him : (normalizedDeltaWeightedFunctional
      (stageUnitToColimit k (gibbsDensityUnit H hH β)) (star x * x)).im = 0 := by
    exact Complex.conj_eq_iff_im.mp (by
      simpa only [Complex.star_def] using hstar.symm)
  exact Complex.le_def.mpr ⟨hreal, by simpa using him.symm⟩

private def seedStageToMatrix (n : ℕ) : CStarMatrixStage n ≃⋆ₐ[ℂ] MatrixStage n :=
  (CStarMatrix.ofMatrixStarAlgEquiv).symm

/-- Restriction of the existing global functional, at every stage including n < k. -/
def finiteSeedStageFunctional {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (n : ℕ) :
    CStarMatrixStage n →ₗ[ℂ] ℂ :=
  (normalizedDeltaWeightedFunctional
    (stageUnitToColimit k (gibbsDensityUnit H hH β))).comp
    ((stageInjection n).toAlgHom.toLinearMap.comp
      (seedStageToMatrix n).toAlgEquiv.toLinearMap)

local instance cstarMatrixStageRealCFC (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrixStage n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance cstarMatrixStageNonnegSpectrum (n : ℕ) :
    NonnegSpectrumClass ℝ (CStarMatrixStage n) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- Positivity of the restriction gives monotonicity on the native C⋆ stage. -/
theorem finiteSeedStageFunctional_monotone {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (n : ℕ) :
    Monotone (finiteSeedStageFunctional H hH β n) := by
  intro A B hAB
  rw [← sub_nonneg] at hAB ⊢
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hAB
  rw [← map_sub, hC]
  change 0 ≤ normalizedDeltaWeightedFunctional
    (stageUnitToColimit k (gibbsDensityUnit H hH β))
    (stageInjection n (seedStageToMatrix n (star C * C)))
  rw [map_mul, map_star, map_mul, map_star]
  exact finiteSeedGibbs_nonneg_complex H hH β
    (stageInjection n (seedStageToMatrix n C))

/-- A normalized positive native state, constructed without a new state carrier. -/
def finiteSeedStageState {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (n : ℕ) :
    State (CStarMatrixStage n) where
  functional := PositiveLinearMap.mk (finiteSeedStageFunctional H hH β n)
    (finiteSeedStageFunctional_monotone H hH β n)
  normalized := by
    change normalizedDeltaWeightedFunctional
      (stageUnitToColimit k (gibbsDensityUnit H hH β))
      (stageInjection n (seedStageToMatrix n 1)) = 1
    rw [map_one, map_one]
    exact finiteSeedGibbs_one H hH β

/-- Readback identifies the constructed state with the given algebraic functional. -/
@[simp] theorem finiteSeedStageState_apply {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (n : ℕ)
    (A : CStarMatrixStage n) :
    (finiteSeedStageState H hH β n).functional A =
      normalizedDeltaWeightedFunctional
        (stageUnitToColimit k (gibbsDensityUnit H hH β))
        (stageInjection n ((CStarMatrix.ofMatrixStarAlgEquiv).symm A)) := rfl

/-- Compatibility comes from the colimit injection law, not Hamiltonian assumptions. -/
theorem finiteSeedStageState_transition {k i j : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)
    (hij : i ≤ j) (A : CStarMatrixStage i) :
    (finiteSeedStageState H hH β j).functional (cstarConcreteMap hij A) =
      (finiteSeedStageState H hH β i).functional A := by
  rw [finiteSeedStageState_apply, finiteSeedStageState_apply,
    cstarConcreteMap_toMatrixStage]
  change normalizedDeltaWeightedFunctional
    (stageUnitToColimit k (gibbsDensityUnit H hH β))
    (stageInjection j (rawMap hij ((CStarMatrix.ofMatrixStarAlgEquiv).symm A))) = _
  rw [stageInjection_transition]

/-- The actual compatible family consumed by the native filtered GNS owners. -/
def finiteSeedCompatibleStageStates {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      CStarMatrixStage cstarMatrixInductiveSystem where
  state := finiteSeedStageState H hH β
  compatible := by
    intro i j hij
    apply State.ext
    ext A
    change (finiteSeedStageState H hH β j).functional (cstarConcreteMap hij A) =
      (finiteSeedStageState H hH β i).functional A
    exact finiteSeedStageState_transition H hH β hij A

end InfoGeometry.Canonical.AlgebraicKMSStateColimit
