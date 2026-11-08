import InfoGeometry.Canonical.ColeFurySpinorProjectiveChartTransitions
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ColeFurySpinorProjectiveObservable

open InfoGeometry.Canonical.ColeFurySpinorProjectiveChart
open InfoGeometry.Canonical.ColeFurySpinorProjectiveChartTransitions

noncomputable section

/-!
  A concrete continuous observable on a projective spinor chart.

  The coordinate ratios are already invariant under the scalar action, so this
  definition is genuinely projective rather than a function on representatives.
-/

def projectiveCoordinateEnergy (i : Fin 32) : ProjectiveChart i → ℝ :=
  fun x => ∑ j : Fin 32, (coordinateRatioOnProjectiveChart i j x) ^ 2

def projectiveCoordinateProfile (i : Fin 32) :
    ProjectiveChart i → (Fin 32 → ℝ) :=
  fun x j => coordinateRatioOnProjectiveChart i j x

theorem continuous_projectiveCoordinateProfile (i : Fin 32) :
    Continuous (projectiveCoordinateProfile i) := by
  unfold projectiveCoordinateProfile
  exact continuous_pi (fun j => continuous_coordinateRatioOnProjectiveChart i j)

theorem projectiveCoordinateProfile_map (i : Fin 32) (ψ : CoordinateChart i) :
    projectiveCoordinateProfile i (chartMap i ψ) =
      fun j => coordinateRatio i j ψ := by
  funext j
  exact coordinateRatioOnProjectiveChart_map i j ψ

theorem continuous_projectiveCoordinateEnergy (i : Fin 32) :
    Continuous (projectiveCoordinateEnergy i) := by
  unfold projectiveCoordinateEnergy
  apply continuous_finset_sum
  intro j hj
  exact (continuous_coordinateRatioOnProjectiveChart i j).pow 2

theorem projectiveCoordinateEnergy_nonneg (i : Fin 32) (x : ProjectiveChart i) :
    0 ≤ projectiveCoordinateEnergy i x := by
  unfold projectiveCoordinateEnergy
  exact Finset.sum_nonneg (fun j hj => sq_nonneg _)

def projectiveCoordinateEnergySublevel (i : Fin 32) (c : ℝ) : Set (ProjectiveChart i) :=
  {x | projectiveCoordinateEnergy i x ≤ c}

theorem projectiveCoordinateEnergySublevel_isClosed (i : Fin 32) (c : ℝ) :
    IsClosed (projectiveCoordinateEnergySublevel i c) := by
  change IsClosed ((projectiveCoordinateEnergy i) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage (continuous_projectiveCoordinateEnergy i)

theorem projectiveCoordinateEnergy_map (i : Fin 32) (ψ : CoordinateChart i) :
    projectiveCoordinateEnergy i (chartMap i ψ) =
      ∑ j : Fin 32, (coordinateRatio i j ψ) ^ 2 := by
  unfold projectiveCoordinateEnergy
  simp only [coordinateRatioOnProjectiveChart_map]

def transitionCoordinateEnergy (i k : Fin 32) : ChartOverlap i k → ℝ :=
  fun ψ => ∑ j : Fin 32, (transitionMap i j k ψ) ^ 2

theorem continuous_transitionCoordinateEnergy (i k : Fin 32) :
    Continuous (transitionCoordinateEnergy i k) := by
  unfold transitionCoordinateEnergy
  apply continuous_finset_sum
  intro j hj
  exact (continuous_transitionMap i j k).pow 2

theorem projectiveCoordinateEnergy_transition (i k : Fin 32) (ψ : ChartOverlap i k) :
    projectiveCoordinateEnergy i (chartMap i (overlapToChart i k ψ)) =
      transitionCoordinateEnergy i k ψ := by
  unfold projectiveCoordinateEnergy transitionCoordinateEnergy
  apply Finset.sum_congr rfl
  intro j hj
  rw [coordinateRatioOnProjectiveChart_map, chart_transition_formula]

theorem projectiveCoordinateProfile_transition (i k : Fin 32)
    (ψ : ChartOverlap i k) :
    projectiveCoordinateProfile i (chartMap i (overlapToChart i k ψ)) =
      (coordinateRatio i k (overlapToChart i k ψ)) •
        projectiveCoordinateProfile k (chartMap k (overlapToChartK i k ψ)) := by
  funext j
  change coordinateRatioOnProjectiveChart i j (chartMap i (overlapToChart i k ψ)) =
    coordinateRatio i k (overlapToChart i k ψ) *
      coordinateRatioOnProjectiveChart k j (chartMap k (overlapToChartK i k ψ))
  rw [coordinateRatioOnProjectiveChart_map, coordinateRatioOnProjectiveChart_map]
  rw [chart_transition_formula]
  unfold transitionMap
  ring

theorem coordinateRatio_overlap_ne_zero (i k : Fin 32) (ψ : ChartOverlap i k) :
    coordinateRatio i k (overlapToChart i k ψ) ≠ 0 := by
  unfold coordinateRatio overlapToChart
  exact div_ne_zero ψ.2.2 ψ.2.1

theorem projectiveCoordinateEnergy_chart_change (i k : Fin 32)
    (ψ : ChartOverlap i k) :
    projectiveCoordinateEnergy k (chartMap k (overlapToChartK i k ψ)) =
      projectiveCoordinateEnergy i (chartMap i (overlapToChart i k ψ)) /
        (coordinateRatio i k (overlapToChart i k ψ)) ^ 2 := by
  rw [projectiveCoordinateEnergy_map, projectiveCoordinateEnergy_map]
  let q := coordinateRatio i k (overlapToChart i k ψ)
  have hq : q ≠ 0 := coordinateRatio_overlap_ne_zero i k ψ
  have hterm : ∀ j : Fin 32,
      (coordinateRatio k j (overlapToChartK i k ψ)) ^ 2 =
        (coordinateRatio i j (overlapToChart i k ψ)) ^ 2 / q ^ 2 := by
    intro j
    have htrans := chart_transition_formula i j k ψ
    calc
      (coordinateRatio k j (overlapToChartK i k ψ)) ^ 2 =
          (transitionMap i j k ψ) ^ 2 / q ^ 2 := by
            dsimp [transitionMap, q]
            field_simp [hq]
            symm
            exact mul_div_cancel_right₀ _ hq
      _ = (coordinateRatio i j (overlapToChart i k ψ)) ^ 2 / q ^ 2 := by
        rw [htrans]
  change (∑ j : Fin 32,
      (coordinateRatio k j (overlapToChartK i k ψ)) ^ 2) =
    (∑ j : Fin 32,
      (coordinateRatio i j (overlapToChart i k ψ)) ^ 2) / q ^ 2
  calc
    (∑ j : Fin 32,
        (coordinateRatio k j (overlapToChartK i k ψ)) ^ 2) =
        ∑ j : Fin 32,
          (coordinateRatio i j (overlapToChart i k ψ)) ^ 2 / q ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j
    _ = (∑ j : Fin 32,
        (coordinateRatio i j (overlapToChart i k ψ)) ^ 2) / q ^ 2 := by
      rw [Finset.sum_div]

end

end InfoGeometry.Canonical.ColeFurySpinorProjectiveObservable
