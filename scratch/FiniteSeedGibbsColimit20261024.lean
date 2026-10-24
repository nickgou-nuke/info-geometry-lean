/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AlgebraicKMSStateColimitReadback
import InfoGeometry.Canonical.GibbsParityTower

/-! Arbitrary finite Gibbs seeds on the existing algebraic matrix colimit.
Uncompiled sandbox candidate. No completed C⋆ state or analytic KMS assertion.
-/

noncomputable section

namespace InfoGeometry.Canonical.AlgebraicKMSStateColimit

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

/-- Transporting the seed changes its representative, not its colimit unit. -/
theorem stageGibbsUnit_transport {k n : ℕ} (hkn : k ≤ n)
    (H : MatrixStage k) (Hn : MatrixStage n)
    (hH : H.IsHermitian) (hHn : Hn.IsHermitian)
    (htransport : Hn = rawMap hkn H) (β : ℝ) :
    stageUnitToColimit k (gibbsDensityUnit H hH β) =
      stageUnitToColimit n (gibbsDensityUnit Hn hHn β) := by
  apply Units.ext
  simp only [stageUnitToColimit_coe, gibbsDensityUnit_coe]
  rw [← CuntzMatrixCompatibleStateNet.gibbsDensity_rawMap hkn H Hn hH hHn htransport β]
  exact (stageInjection_transition hkn (gibbsDensity H hH β)).symm

/-- Readback holds for every later-stage observable, not only seed images. -/
theorem finiteSeedGibbs_later_stage {k n : ℕ} (hkn : k ≤ n)
    (H : MatrixStage k) (Hn : MatrixStage n)
    (hH : H.IsHermitian) (hHn : Hn.IsHermitian)
    (htransport : Hn = rawMap hkn H) (β : ℝ) (X : MatrixStage n) :
    normalizedDeltaWeightedFunctional
        (stageUnitToColimit k (gibbsDensityUnit H hH β))
        (stageInjection n X) = gibbsFunctional Hn hHn β X := by
  rw [stageGibbsUnit_transport hkn H Hn hH hHn htransport β]
  exact normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional Hn hHn β X

/-- An arbitrary finite seed normalizes the existing global functional. -/
theorem finiteSeedGibbs_one {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    normalizedDeltaWeightedFunctional
        (stageUnitToColimit k (gibbsDensityUnit H hH β)) 1 = 1 := by
  have h := normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional
    H hH β (1 : MatrixStage k)
  simpa only [map_one, gibbsFunctional_one] using h

/-- Positivity for every algebraic-colimit element, using a common finite stage. -/
theorem finiteSeedGibbs_positive {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (x : Carrier) :
    0 ≤ (normalizedDeltaWeightedFunctional
      (stageUnitToColimit k (gibbsDensityUnit H hH β)) (star x * x)).re := by
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
      have hx : (⟦⟨j, a⟩⟧ : Carrier) = stageInjection m b := by
        exact (stageInjection_transition hjm a).symm
      rw [hx, ← stageInjection_star, ← stageInjection_mul]
      rw [finiteSeedGibbs_later_stage hkm H Hm hH hHm rfl β]
      exact gibbsFunctional_positive Hm hHm β b

/-- Seed odd cancellation is a genuine readout of the global functional. -/
theorem finiteSeedGibbs_seed_odd_zero {k : ℕ}
    (H Γ X : MatrixStage k) (hH : H.IsHermitian)
    (hcomm : Commute H Γ) (hΓ : Γ * Γ = 1)
    (hodd : X * Γ = -(Γ * X)) (β : ℝ) :
    normalizedDeltaWeightedFunctional
        (stageUnitToColimit k (gibbsDensityUnit H hH β))
        (stageInjection k X) = 0 := by
  rw [normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional]
  exact gibbsFunctional_odd_zero H Γ X hH hcomm hΓ hodd β

end InfoGeometry.Canonical.AlgebraicKMSStateColimit
