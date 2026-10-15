import Mathlib
import InfoGeometry.Topology.Gr24PositroidCanonicalForm

/-!
# A positroid cell outside the `p₀₁ > 0` chart

The support `{p₀₂,p₀₃,p₁₂,p₁₃}` is a genuine two-dimensional positroid cell
of `Gr(2,4)` which the usual `p₀₁ = 1` network chart does not meet. Its
Plücker relation is `p₀₂ p₁₃ = p₀₃ p₁₂`. Fixing `p₀₃ = 1` gives an
injective two-coordinate parametrization into this cell. The form below is
the actual alternating `dlog u ∧ dlog v` form on the parameter space.

This is one additional cell chart; it does not claim a global canonical form
across all positroid strata.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.Gr24MiddlePositroidCellForm

open InfoGeometry.Topology.Gr24PositroidCanonicalForm

/-- The two positive coordinates on the cell with support `02,03,12,13`.
The projective gauge is `p₀₃ = 1`. -/
abbrev MiddleCellParameters := {t : Fin 2 → ℝ // ∀ i, 0 < t i}

/-- An unnormalized Plücker vector on the middle positroid cell, in order
`01,02,03,12,13,23`: `(0, u, 1, v, v/u, 0)`. -/
noncomputable def middleCellRaw (t : MiddleCellParameters) : Fin 6 → ℝ
  | 0 => 0
  | 1 => t.1 0
  | 2 => 1
  | 3 => t.1 1
  | 4 => t.1 1 / t.1 0
  | 5 => 0

/-- Projective mass used to normalize the representative. -/
noncomputable def middleCellMass (t : MiddleCellParameters) : ℝ :=
  ∑ i : Fin 6, middleCellRaw t i

theorem middleCellRaw_nonneg (t : MiddleCellParameters) (i : Fin 6) :
    0 ≤ middleCellRaw t i := by
  fin_cases i
  · simp [middleCellRaw]
  · exact (t.2 0).le
  · norm_num [middleCellRaw]
  · exact (t.2 1).le
  · exact div_nonneg (t.2 1).le (t.2 0).le
  · simp [middleCellRaw]

theorem middleCellMass_pos (t : MiddleCellParameters) : 0 < middleCellMass t := by
  unfold middleCellMass
  apply Finset.sum_pos'
  · intro i hi
    exact middleCellRaw_nonneg t i
  · exact ⟨2, Finset.mem_univ _, by simp [middleCellRaw]⟩

/-- The normalized Plücker point represented by this cell chart. -/
noncomputable def middleCellPoint (t : MiddleCellParameters) :
    NormalizedPositivePluckerPoint := by
  let m := middleCellMass t
  have hm : 0 < m := middleCellMass_pos t
  refine ⟨fun i => middleCellRaw t i / m, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (middleCellRaw_nonneg t i) hm.le
  · rw [← Finset.sum_div]
    dsimp [m]
    exact div_self (ne_of_gt hm)
  · have hu : t.1 0 ≠ 0 := ne_of_gt (t.2 0)
    change (middleCellRaw t 0 / m) * (middleCellRaw t 5 / m) -
      (middleCellRaw t 1 / m) * (middleCellRaw t 4 / m) +
      (middleCellRaw t 2 / m) * (middleCellRaw t 3 / m) = 0
    simp only [middleCellRaw]
    field_simp
    ring

theorem middleCellPoint_support (t : MiddleCellParameters) :
    positiveSupport (middleCellPoint t) = {1, 2, 3, 4} := by
  ext i
  fin_cases i <;>
    simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
  · simp [middleCellPoint, middleCellRaw]
  · have hm := middleCellMass_pos t
    simp only [middleCellPoint, middleCellRaw]
    constructor
    · intro _; simp
    · intro _
      simpa [middleCellRaw] using div_pos (t.2 0) hm
  · have hm := middleCellMass_pos t
    simp only [middleCellPoint, middleCellRaw]
    constructor
    · intro _; simp
    · intro _
      simpa [middleCellRaw] using div_pos (by norm_num : (0 : ℝ) < 1) hm
  · have hm := middleCellMass_pos t
    simp only [middleCellPoint, middleCellRaw]
    constructor
    · intro _; simp
    · intro _
      simpa [middleCellRaw] using div_pos (t.2 1) hm
  · have hm := middleCellMass_pos t
    simp only [middleCellPoint, middleCellRaw]
    constructor
    · intro _; simp
    · intro _
      simpa [middleCellRaw] using div_pos (div_pos (t.2 1) (t.2 0)) hm
  · simp [middleCellPoint, middleCellRaw]

/-- The chart lies in the exact global support stratum `{02,03,12,13}`. -/
theorem middleCellPoint_mem_cell (t : MiddleCellParameters) :
    middleCellPoint t ∈ supportStratum ({1, 2, 3, 4} : Finset (Fin 6)) :=
  middleCellPoint_support t

/-- The projective coordinate ratios recover the chart parameters. -/
theorem middleCellPoint_ratio02 (t : MiddleCellParameters) :
    (middleCellPoint t).coord 1 / (middleCellPoint t).coord 2 = t.1 0 := by
  have hm : middleCellMass t ≠ 0 := ne_of_gt (middleCellMass_pos t)
  change (middleCellRaw t 1 / middleCellMass t) /
      (middleCellRaw t 2 / middleCellMass t) = t.1 0
  simp only [middleCellRaw]
  field_simp

theorem middleCellPoint_ratio12 (t : MiddleCellParameters) :
    (middleCellPoint t).coord 3 / (middleCellPoint t).coord 2 = t.1 1 := by
  have hm : middleCellMass t ≠ 0 := ne_of_gt (middleCellMass_pos t)
  change (middleCellRaw t 3 / middleCellMass t) /
      (middleCellRaw t 2 / middleCellMass t) = t.1 1
  simp only [middleCellRaw]
  field_simp

/-- The positive cell chart is injective after projective normalization. -/
theorem middleCellPoint_injective : Function.Injective middleCellPoint := by
  intro t s h
  apply Subtype.ext
  funext i
  have hcoord : (middleCellPoint t).coord = (middleCellPoint s).coord :=
    congrArg NormalizedPositivePluckerPoint.coord h
  fin_cases i
  · have hratio := congrArg (fun p : NormalizedPositivePluckerPoint =>
      p.coord 1 / p.coord 2) h
    rw [middleCellPoint_ratio02 t, middleCellPoint_ratio02 s] at hratio
    exact hratio
  · have hratio := congrArg (fun p : NormalizedPositivePluckerPoint =>
      p.coord 3 / p.coord 2) h
    rw [middleCellPoint_ratio12 t, middleCellPoint_ratio12 s] at hratio
    exact hratio

/-- Every normalized nonnegative Plücker point with support `{02,03,12,13}`
is represented by the two-coordinate chart.  The inverse coordinates are
the projective ratios `p₀₂/p₀₃` and `p₁₂/p₀₃`; the Klein relation supplies
the remaining coordinate `p₁₃`. -/
theorem middleCellPoint_surjective :
    ∀ P : NormalizedPositivePluckerPoint,
      P ∈ supportStratum ({1, 2, 3, 4} : Finset (Fin 6)) →
        ∃ t : MiddleCellParameters, middleCellPoint t = P := by
  intro P hP
  have hsupport : positiveSupport P = ({1, 2, 3, 4} : Finset (Fin 6)) := hP
  have hp0 : P.coord 0 = 0 := by
    have hnot : ¬ 0 < P.coord 0 := by
      intro h
      have : (0 : Fin 6) ∈ positiveSupport P := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, h⟩
      rw [hsupport] at this
      simp at this
    exact le_antisymm (le_of_not_gt hnot) (P.coord_nonneg 0)
  have hp5 : P.coord 5 = 0 := by
    have hnot : ¬ 0 < P.coord 5 := by
      intro h
      have : (5 : Fin 6) ∈ positiveSupport P := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, h⟩
      rw [hsupport] at this
      simp at this
    exact le_antisymm (le_of_not_gt hnot) (P.coord_nonneg 5)
  have hp1 : 0 < P.coord 1 := by
    have hmem : (1 : Fin 6) ∈ positiveSupport P := by
      rw [hsupport]
      simp
    exact (Finset.mem_filter.mp hmem).2
  have hp2 : 0 < P.coord 2 := by
    have hmem : (2 : Fin 6) ∈ positiveSupport P := by
      rw [hsupport]
      simp
    exact (Finset.mem_filter.mp hmem).2
  have hp3 : 0 < P.coord 3 := by
    have hmem : (3 : Fin 6) ∈ positiveSupport P := by
      rw [hsupport]
      simp
    exact (Finset.mem_filter.mp hmem).2
  have hp4 : 0 < P.coord 4 := by
    have hmem : (4 : Fin 6) ∈ positiveSupport P := by
      rw [hsupport]
      simp
    exact (Finset.mem_filter.mp hmem).2
  let t : MiddleCellParameters :=
    ⟨fun i => if i = 0 then P.coord 1 / P.coord 2 else P.coord 3 / P.coord 2,
      by
        intro i
        fin_cases i
        · exact div_pos hp1 hp2
        · exact div_pos hp3 hp2⟩
  refine ⟨t, ?_⟩
  apply NormalizedPositivePluckerPoint.ext
  funext i
  have hrel := P.klein
  have hsum := P.coord_sum_one
  have hklein : P.coord 1 * P.coord 4 = P.coord 2 * P.coord 3 := by
    nlinarith [hrel, hp0, hp5]
  have hraw (i : Fin 6) : middleCellRaw t i = P.coord i / P.coord 2 := by
    fin_cases i
    · simp [middleCellRaw, hp0]
    · simp [middleCellRaw, t]
    · change (1 : ℝ) = P.coord 2 / P.coord 2
      field_simp [ne_of_gt hp2]
    · simp [middleCellRaw, t]
    · change (P.coord 3 / P.coord 2) / (P.coord 1 / P.coord 2) =
        P.coord 4 / P.coord 2
      have hratio : P.coord 1 / P.coord 2 ≠ 0 :=
        div_ne_zero (ne_of_gt hp1) (ne_of_gt hp2)
      field_simp [ne_of_gt hp1, ne_of_gt hp2, hratio]
      nlinarith [hklein]
    · simp [middleCellRaw, hp5]
  have hmass : middleCellMass t = 1 / P.coord 2 := by
    unfold middleCellMass
    calc
      (∑ i : Fin 6, middleCellRaw t i) =
          ∑ i : Fin 6, P.coord i / P.coord 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hraw i
      _ = (∑ i : Fin 6, P.coord i) / P.coord 2 := (Finset.sum_div ..).symm
      _ = 1 / P.coord 2 := by rw [hsum]
  change middleCellRaw t i / middleCellMass t = P.coord i
  rw [hraw, hmass]
  field_simp [ne_of_gt hp2]

/-- The two positive parameters give an actual chart equivalence with the
entire normalized middle positroid stratum. -/
noncomputable def middleCellChartEquiv : MiddleCellParameters ≃
    {P : NormalizedPositivePluckerPoint //
      P ∈ supportStratum ({1, 2, 3, 4} : Finset (Fin 6))} where
  toFun t := ⟨middleCellPoint t, middleCellPoint_mem_cell t⟩
  invFun P := Classical.choose (middleCellPoint_surjective P.1 P.2)
  left_inv t := middleCellPoint_injective
    (Classical.choose_spec (middleCellPoint_surjective
      (middleCellPoint t) (middleCellPoint_mem_cell t)))
  right_inv P := by
    apply Subtype.ext
    exact Classical.choose_spec (middleCellPoint_surjective P.1 P.2)

/-- The two-dimensional tangent coordinate frame. -/
noncomputable def middleCellFrame : Fin 2 → (Fin 2 → ℝ) := Pi.basisFun ℝ (Fin 2)

/-- The positive coefficient of the middle-cell logarithmic form. -/
noncomputable def middleCellDlogDensity (t : MiddleCellParameters) : ℝ :=
  (t.1 0)⁻¹ * (t.1 1)⁻¹

/-- The genuine alternating top form `dlog u ∧ dlog v` on the middle cell. -/
noncomputable def middleCellCanonicalForm (t : MiddleCellParameters) :
    ((Fin 2 → ℝ) [⋀^Fin 2]→ₗ[ℝ] ℝ) :=
  middleCellDlogDensity t • (Pi.basisFun ℝ (Fin 2)).det

theorem middleCellCanonicalForm_frame (t : MiddleCellParameters) :
    middleCellCanonicalForm t middleCellFrame = middleCellDlogDensity t := by
  rw [middleCellCanonicalForm, middleCellFrame]
  change middleCellDlogDensity t *
    (Pi.basisFun ℝ (Fin 2)).det (Pi.basisFun ℝ (Fin 2)) = _
  rw [Module.Basis.det_self]
  simp

theorem middleCellCanonicalForm_positive (t : MiddleCellParameters) :
    0 < middleCellCanonicalForm t middleCellFrame := by
  rw [middleCellCanonicalForm_frame]
  unfold middleCellDlogDensity
  exact mul_pos (inv_pos.mpr (t.2 0)) (inv_pos.mpr (t.2 1))

/-- The actual normalized positroid stratum carrying the middle-cell form. -/
abbrev MiddlePositroidCell :=
  {P : NormalizedPositivePluckerPoint //
    P ∈ supportStratum ({1, 2, 3, 4} : Finset (Fin 6))}

/-- The middle-cell canonical form attached to a point of the entire
positroid stratum, using the inverse of the proved projective chart. -/
noncomputable def middlePositroidCellCanonicalForm (P : MiddlePositroidCell) :
    ((Fin 2 → ℝ) [⋀^Fin 2]→ₗ[ℝ] ℝ) :=
  middleCellCanonicalForm (middleCellChartEquiv.symm P)

/-- The cell form evaluates to its positive logarithmic density on the
standard orientation at every point of the positroid cell. -/
theorem middlePositroidCellCanonicalForm_value (P : MiddlePositroidCell) :
    middlePositroidCellCanonicalForm P middleCellFrame =
      middleCellDlogDensity (middleCellChartEquiv.symm P) :=
  middleCellCanonicalForm_frame (middleCellChartEquiv.symm P)

theorem middlePositroidCellCanonicalForm_positive (P : MiddlePositroidCell) :
    0 < middlePositroidCellCanonicalForm P middleCellFrame := by
  rw [middlePositroidCellCanonicalForm_value]
  unfold middleCellDlogDensity
  exact mul_pos
    (inv_pos.mpr ((middleCellChartEquiv.symm P).2 0))
    (inv_pos.mpr ((middleCellChartEquiv.symm P).2 1))

end InfoGeometry.Canonical.Gr24MiddlePositroidCellForm
