import Mathlib
import InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm

/-!
# The five-coordinate relation-bearing positroid cell of `Gr(2,4)`

The support `{02,03,12,13,23}` is outside the `p₀₁ > 0` chart and is not a
simplex cell: its positive Plücker coordinates satisfy `p₀₂ p₁₃ = p₀₃ p₁₂`.
This file gives an explicit projective chart for the entire normalized
stratum and its genuine three-form logarithmic canonical form.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.Gr24FiveCoordinateKleinCellForm

open InfoGeometry.Topology.Gr24PositroidCanonicalForm
open InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm

/-- Three positive parameters on the support `{02,03,12,13,23}`. -/
abbrev FiveCellParameters := {t : Fin 3 → ℝ // ∀ i, 0 < t i}

/-- An unnormalized Plücker vector, in order `01,02,03,12,13,23`:
`(0,u,1,v,v/u,w)`.  The Klein relation is exactly `u (v/u) = 1 v`. -/
noncomputable def fiveCellRaw (t : FiveCellParameters) : Fin 6 → ℝ
  | 0 => 0
  | 1 => t.1 0
  | 2 => 1
  | 3 => t.1 1
  | 4 => t.1 1 / t.1 0
  | 5 => t.1 2

theorem fiveCellRaw_nonneg (t : FiveCellParameters) (i : Fin 6) :
    0 ≤ fiveCellRaw t i := by
  fin_cases i
  · simp [fiveCellRaw]
  · exact (t.2 0).le
  · norm_num [fiveCellRaw]
  · exact (t.2 1).le
  · exact (div_pos (t.2 1) (t.2 0)).le
  · exact (t.2 2).le

/-- The positive projective mass used to normalize the raw Plücker vector. -/
noncomputable def fiveCellMass (t : FiveCellParameters) : ℝ :=
  ∑ i : Fin 6, fiveCellRaw t i

theorem fiveCellMass_pos (t : FiveCellParameters) : 0 < fiveCellMass t := by
  unfold fiveCellMass
  apply Finset.sum_pos'
  · intro i hi
    exact fiveCellRaw_nonneg t i
  · exact ⟨2, Finset.mem_univ _, by norm_num [fiveCellRaw]⟩

/-- The actual normalized nonnegative Klein-quadric point of the cell. -/
noncomputable def fiveCellPoint (t : FiveCellParameters) :
    NormalizedPositivePluckerPoint := by
  let m := fiveCellMass t
  have hm : 0 < m := fiveCellMass_pos t
  refine ⟨fun i => fiveCellRaw t i / m, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (fiveCellRaw_nonneg t i) hm.le
  ·
    rw [← Finset.sum_div]
    change fiveCellMass t / m = 1
    dsimp [m]
    exact div_self (ne_of_gt (fiveCellMass_pos t))
  ·
    simp only [fiveCellRaw]
    field_simp [ne_of_gt hm, ne_of_gt (t.2 0)]
    ring

/-- The projective support is exactly `{02,03,12,13,23}`. -/
theorem fiveCellPoint_support (t : FiveCellParameters) :
    positiveSupport (fiveCellPoint t) = ({1, 2, 3, 4, 5} : Finset (Fin 6)) := by
  apply Finset.ext
  intro i
  fin_cases i
  · have hzero : (fiveCellPoint t).coord 0 = 0 := by
      change fiveCellRaw t 0 / fiveCellMass t = 0
      simp [fiveCellRaw]
    simp [positiveSupport, hzero]
  · have hpos : 0 < (fiveCellPoint t).coord 1 := by
      change 0 < fiveCellRaw t 1 / fiveCellMass t
      exact div_pos (t.2 0) (fiveCellMass_pos t)
    simp [positiveSupport, hpos]
  · have hpos : 0 < (fiveCellPoint t).coord 2 := by
      change 0 < fiveCellRaw t 2 / fiveCellMass t
      exact div_pos (by norm_num [fiveCellRaw]) (fiveCellMass_pos t)
    simp [positiveSupport, hpos]
  · have hpos : 0 < (fiveCellPoint t).coord 3 := by
      change 0 < fiveCellRaw t 3 / fiveCellMass t
      exact div_pos (t.2 1) (fiveCellMass_pos t)
    simp [positiveSupport, hpos]
  · have hpos : 0 < (fiveCellPoint t).coord 4 := by
      change 0 < fiveCellRaw t 4 / fiveCellMass t
      exact div_pos (div_pos (t.2 1) (t.2 0)) (fiveCellMass_pos t)
    simp [positiveSupport, hpos]
  · have hpos : 0 < (fiveCellPoint t).coord 5 := by
      change 0 < fiveCellRaw t 5 / fiveCellMass t
      exact div_pos (t.2 2) (fiveCellMass_pos t)
    simp [positiveSupport, hpos]

theorem fiveCellPoint_ratio02 (t : FiveCellParameters) :
    (fiveCellPoint t).coord 1 / (fiveCellPoint t).coord 2 = t.1 0 := by
  have hm : fiveCellMass t ≠ 0 := ne_of_gt (fiveCellMass_pos t)
  change (fiveCellRaw t 1 / fiveCellMass t) /
      (fiveCellRaw t 2 / fiveCellMass t) = t.1 0
  simp only [fiveCellRaw]
  field_simp

theorem fiveCellPoint_ratio12 (t : FiveCellParameters) :
    (fiveCellPoint t).coord 3 / (fiveCellPoint t).coord 2 = t.1 1 := by
  have hm : fiveCellMass t ≠ 0 := ne_of_gt (fiveCellMass_pos t)
  change (fiveCellRaw t 3 / fiveCellMass t) /
      (fiveCellRaw t 2 / fiveCellMass t) = t.1 1
  simp only [fiveCellRaw]
  field_simp

theorem fiveCellPoint_ratio23 (t : FiveCellParameters) :
    (fiveCellPoint t).coord 5 / (fiveCellPoint t).coord 2 = t.1 2 := by
  have hm : fiveCellMass t ≠ 0 := ne_of_gt (fiveCellMass_pos t)
  change (fiveCellRaw t 5 / fiveCellMass t) /
      (fiveCellRaw t 2 / fiveCellMass t) = t.1 2
  simp only [fiveCellRaw]
  field_simp

/-- The projective chart is injective, with parameters recovered by three
ratios against the positive pivot `p₀₃`. -/
theorem fiveCellPoint_injective : Function.Injective fiveCellPoint := by
  intro t s h
  apply Subtype.ext
  funext i
  fin_cases i
  · have hratio := congrArg (fun P : NormalizedPositivePluckerPoint =>
      P.coord 1 / P.coord 2) h
    rw [fiveCellPoint_ratio02 t, fiveCellPoint_ratio02 s] at hratio
    exact hratio
  · have hratio := congrArg (fun P : NormalizedPositivePluckerPoint =>
      P.coord 3 / P.coord 2) h
    rw [fiveCellPoint_ratio12 t, fiveCellPoint_ratio12 s] at hratio
    exact hratio
  · have hratio := congrArg (fun P : NormalizedPositivePluckerPoint =>
      P.coord 5 / P.coord 2) h
    rw [fiveCellPoint_ratio23 t, fiveCellPoint_ratio23 s] at hratio
    exact hratio

/-- The exact normalized stratum carrying the five-coordinate relation. -/
abbrev FiveCoordinateKleinCell :=
  {P : NormalizedPositivePluckerPoint //
    P ∈ supportStratum ({1, 2, 3, 4, 5} : Finset (Fin 6))}

/-- This cell is relation-bearing rather than one of the projective simplex
strata: both factors in the `p₀₂ p₁₃` Klein monomial are live. -/
theorem fiveCoordinateCell_not_simplex :
    ¬ simplexPositroidSupport ({1, 2, 3, 4, 5} : Finset (Fin 6)) := by
  intro h
  apply h 1
  intro i hi
  simp [kleinComplementaryPairs] at hi
  rcases hi with rfl | rfl <;> simp

/-- Every point of the five-coordinate stratum is represented by the chart
`(0,u,1,v,v/u,w)`, followed by projective sum-one normalization. -/
theorem fiveCellPoint_surjective :
    ∀ P : NormalizedPositivePluckerPoint,
      positiveSupport P = ({1, 2, 3, 4, 5} : Finset (Fin 6)) →
        ∃ t : FiveCellParameters, fiveCellPoint t = P := by
  intro P hsupport
  have hp0 : P.coord 0 = 0 := by
    have hnot : ¬ 0 < P.coord 0 := by
      intro h
      have hm : (0 : Fin 6) ∈ positiveSupport P :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hsupport] at hm
      simp at hm
    exact le_antisymm (le_of_not_gt hnot) (P.coord_nonneg 0)
  have hp1 : 0 < P.coord 1 := by
    have hm : (1 : Fin 6) ∈ positiveSupport P := by rw [hsupport]; simp
    exact (Finset.mem_filter.mp hm).2
  have hp2 : 0 < P.coord 2 := by
    have hm : (2 : Fin 6) ∈ positiveSupport P := by rw [hsupport]; simp
    exact (Finset.mem_filter.mp hm).2
  have hp3 : 0 < P.coord 3 := by
    have hm : (3 : Fin 6) ∈ positiveSupport P := by rw [hsupport]; simp
    exact (Finset.mem_filter.mp hm).2
  have hp4 : 0 < P.coord 4 := by
    have hm : (4 : Fin 6) ∈ positiveSupport P := by rw [hsupport]; simp
    exact (Finset.mem_filter.mp hm).2
  have hp5 : 0 < P.coord 5 := by
    have hm : (5 : Fin 6) ∈ positiveSupport P := by rw [hsupport]; simp
    exact (Finset.mem_filter.mp hm).2
  have hklein : P.coord 1 * P.coord 4 = P.coord 2 * P.coord 3 := by
    have h := P.klein
    rw [hp0] at h
    linarith
  let t : FiveCellParameters :=
    ⟨![P.coord 1 / P.coord 2, P.coord 3 / P.coord 2, P.coord 5 / P.coord 2], by
      intro i
      fin_cases i
      · exact div_pos hp1 hp2
      · exact div_pos hp3 hp2
      · exact div_pos hp5 hp2⟩
  refine ⟨t, ?_⟩
  apply NormalizedPositivePluckerPoint.ext
  funext i
  have hraw (i : Fin 6) : fiveCellRaw t i = P.coord i / P.coord 2 := by
    fin_cases i
    · simp [fiveCellRaw, hp0]
    · simp [fiveCellRaw, t]
    · change (1 : ℝ) = P.coord 2 / P.coord 2
      field_simp [ne_of_gt hp2]
    · simp [fiveCellRaw, t]
    · change (P.coord 3 / P.coord 2) / (P.coord 1 / P.coord 2) =
        P.coord 4 / P.coord 2
      have hratio : P.coord 1 / P.coord 2 ≠ 0 :=
        div_ne_zero (ne_of_gt hp1) (ne_of_gt hp2)
      field_simp [ne_of_gt hp1, ne_of_gt hp2, hratio]
      nlinarith [hklein]
    · simp [fiveCellRaw, t]
  have hmass : fiveCellMass t = 1 / P.coord 2 := by
    unfold fiveCellMass
    calc
      (∑ i : Fin 6, fiveCellRaw t i) =
          ∑ i : Fin 6, P.coord i / P.coord 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hraw i
      _ = (∑ i : Fin 6, P.coord i) / P.coord 2 := (Finset.sum_div ..).symm
      _ = 1 / P.coord 2 := by rw [P.coord_sum_one]
  change fiveCellRaw t i / fiveCellMass t = P.coord i
  rw [hraw, hmass]
  field_simp [ne_of_gt hp2]

/-- The positive-orthant parameter chart is equivalent to the entire
normalized five-coordinate positroid stratum. -/
noncomputable def fiveCellChartEquiv : FiveCellParameters ≃ FiveCoordinateKleinCell where
  toFun t := ⟨fiveCellPoint t, fiveCellPoint_support t⟩
  invFun P := Classical.choose (fiveCellPoint_surjective P.1 P.2)
  left_inv t := fiveCellPoint_injective
    (Classical.choose_spec (fiveCellPoint_surjective
      (fiveCellPoint t) (fiveCellPoint_support t)))
  right_inv P := by
    apply Subtype.ext
    exact Classical.choose_spec (fiveCellPoint_surjective P.1 P.2)

/-- The standard oriented tangent frame of the three-dimensional cell. -/
noncomputable def fiveCellFrame : Fin 3 → (Fin 3 → ℝ) := Pi.basisFun ℝ (Fin 3)

/-- The logarithmic density `dlog u ∧ dlog v ∧ dlog w`. -/
noncomputable def fiveCellDlogDensity (t : FiveCellParameters) : ℝ :=
  (t.1 0)⁻¹ * (t.1 1)⁻¹ * (t.1 2)⁻¹

/-- Taking the logarithmic residue at `u = 0` removes exactly the `u⁻¹`
factor from the three-cell density. -/
theorem fiveCellDlogDensity_residue_u (t : FiveCellParameters) :
    t.1 0 * fiveCellDlogDensity t = (t.1 1)⁻¹ * (t.1 2)⁻¹ := by
  unfold fiveCellDlogDensity
  field_simp [ne_of_gt (t.2 0), ne_of_gt (t.2 1), ne_of_gt (t.2 2)]

/-- Taking the logarithmic residue at `v = 0` removes exactly the `v⁻¹`
factor from the three-cell density. -/
theorem fiveCellDlogDensity_residue_v (t : FiveCellParameters) :
    t.1 1 * fiveCellDlogDensity t = (t.1 0)⁻¹ * (t.1 2)⁻¹ := by
  unfold fiveCellDlogDensity
  field_simp [ne_of_gt (t.2 0), ne_of_gt (t.2 1), ne_of_gt (t.2 2)]

/-- Taking the logarithmic residue at `w = 0` removes exactly the `w⁻¹`
factor from the three-cell density. -/
theorem fiveCellDlogDensity_residue_w (t : FiveCellParameters) :
    t.1 2 * fiveCellDlogDensity t = (t.1 0)⁻¹ * (t.1 1)⁻¹ := by
  unfold fiveCellDlogDensity
  field_simp [ne_of_gt (t.2 0), ne_of_gt (t.2 1), ne_of_gt (t.2 2)]

/-- The genuine alternating three-form on the five-coordinate cell chart. -/
noncomputable def fiveCellCanonicalForm (t : FiveCellParameters) :
    ((Fin 3 → ℝ) [⋀^Fin 3]→ₗ[ℝ] ℝ) :=
  fiveCellDlogDensity t • (Pi.basisFun ℝ (Fin 3)).det

theorem fiveCellCanonicalForm_frame (t : FiveCellParameters) :
    fiveCellCanonicalForm t fiveCellFrame = fiveCellDlogDensity t := by
  rw [fiveCellCanonicalForm, fiveCellFrame]
  change fiveCellDlogDensity t *
    (Pi.basisFun ℝ (Fin 3)).det (Pi.basisFun ℝ (Fin 3)) = _
  rw [Module.Basis.det_self]
  simp

theorem fiveCellCanonicalForm_positive (t : FiveCellParameters) :
    0 < fiveCellCanonicalForm t fiveCellFrame := by
  rw [fiveCellCanonicalForm_frame, fiveCellDlogDensity]
  exact mul_pos (mul_pos (inv_pos.mpr (t.2 0)) (inv_pos.mpr (t.2 1)))
    (inv_pos.mpr (t.2 2))

/-- The canonical form transported to every point of the full projective
five-coordinate positroid stratum. -/
noncomputable def fiveCoordinateKleinCanonicalForm (P : FiveCoordinateKleinCell) :
    ((Fin 3 → ℝ) [⋀^Fin 3]→ₗ[ℝ] ℝ) :=
  fiveCellCanonicalForm (fiveCellChartEquiv.symm P)

theorem fiveCoordinateKleinCanonicalForm_positive (P : FiveCoordinateKleinCell) :
    0 < fiveCoordinateKleinCanonicalForm P fiveCellFrame := by
  exact fiveCellCanonicalForm_positive (fiveCellChartEquiv.symm P)

end InfoGeometry.Canonical.Gr24FiveCoordinateKleinCellForm
