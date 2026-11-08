import Mathlib
import InfoGeometry.Topology.Gr24PositroidCanonicalForm

/-!
# The complementary relation-bearing two-cell of `Gr(2,4)`

The exact support `{01,02,13,23}` is a positroid stratum outside the
`p₀₁ = 1` network chart.  Its Klein equation is `p₀₁ p₂₃ = p₀₂ p₁₃`.
This file gives a projective positive chart on the whole stratum and the
intrinsic alternating logarithmic two-form in that chart.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.Gr24ComplementaryKleinPositroidCellForm

open InfoGeometry.Topology.Gr24PositroidCanonicalForm

/-- The two positive chart parameters `u = p₁₃/p₀₂` and `v = p₂₃/p₀₂`.
The Klein equation then forces `p₀₁/p₀₂ = u/v`. -/
abbrev ComplementaryKleinParameters := {t : Fin 2 → ℝ // ∀ i, 0 < t i}

/-- Unnormalized Plücker coordinates, in order `01,02,03,12,13,23`:
`(u/v, 1, 0, 0, u, v)`. -/
noncomputable def complementaryKleinRaw
    (t : ComplementaryKleinParameters) : Fin 6 → ℝ
  | 0 => t.1 0 / t.1 1
  | 1 => 1
  | 2 => 0
  | 3 => 0
  | 4 => t.1 0
  | 5 => t.1 1

theorem complementaryKleinRaw_nonneg
    (t : ComplementaryKleinParameters) (i : Fin 6) :
    0 ≤ complementaryKleinRaw t i := by
  fin_cases i
  · exact (div_pos (t.2 0) (t.2 1)).le
  · norm_num [complementaryKleinRaw]
  · simp [complementaryKleinRaw]
  · simp [complementaryKleinRaw]
  · exact (t.2 0).le
  · exact (t.2 1).le

/-- Positive projective mass used to impose the sum-one gauge. -/
noncomputable def complementaryKleinMass
    (t : ComplementaryKleinParameters) : ℝ :=
  ∑ i : Fin 6, complementaryKleinRaw t i

theorem complementaryKleinMass_pos (t : ComplementaryKleinParameters) :
    0 < complementaryKleinMass t := by
  unfold complementaryKleinMass
  apply Finset.sum_pos'
  · intro i hi
    exact complementaryKleinRaw_nonneg t i
  · exact ⟨1, Finset.mem_univ _, by norm_num [complementaryKleinRaw]⟩

/-- A normalized nonnegative point of the Klein quadric in the target cell. -/
noncomputable def complementaryKleinPoint
    (t : ComplementaryKleinParameters) : NormalizedPositivePluckerPoint := by
  let m := complementaryKleinMass t
  have hm : 0 < m := complementaryKleinMass_pos t
  refine ⟨fun i => complementaryKleinRaw t i / m, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (complementaryKleinRaw_nonneg t i) hm.le
  · rw [← Finset.sum_div]
    change complementaryKleinMass t / m = 1
    dsimp [m]
    exact div_self (ne_of_gt (complementaryKleinMass_pos t))
  · simp only [complementaryKleinRaw]
    field_simp [ne_of_gt hm, ne_of_gt (t.2 1)]
    ring

/-- The chart has exactly the target support `{01,02,13,23}`. -/
theorem complementaryKleinPoint_support (t : ComplementaryKleinParameters) :
    positiveSupport (complementaryKleinPoint t) =
      ({0, 1, 4, 5} : Finset (Fin 6)) := by
  apply Finset.ext
  intro i
  fin_cases i
  · have hp : 0 < (complementaryKleinPoint t).coord 0 := by
      change 0 < complementaryKleinRaw t 0 / complementaryKleinMass t
      exact div_pos (div_pos (t.2 0) (t.2 1)) (complementaryKleinMass_pos t)
    simp [positiveSupport, hp]
  · have hp : 0 < (complementaryKleinPoint t).coord 1 := by
      change 0 < complementaryKleinRaw t 1 / complementaryKleinMass t
      exact div_pos (by norm_num [complementaryKleinRaw])
        (complementaryKleinMass_pos t)
    simp [positiveSupport, hp]
  · have hz : (complementaryKleinPoint t).coord 2 = 0 := by
      change complementaryKleinRaw t 2 / complementaryKleinMass t = 0
      simp [complementaryKleinRaw]
    simp [positiveSupport, hz]
  · have hz : (complementaryKleinPoint t).coord 3 = 0 := by
      change complementaryKleinRaw t 3 / complementaryKleinMass t = 0
      simp [complementaryKleinRaw]
    simp [positiveSupport, hz]
  · have hp : 0 < (complementaryKleinPoint t).coord 4 := by
      change 0 < complementaryKleinRaw t 4 / complementaryKleinMass t
      exact div_pos (t.2 0) (complementaryKleinMass_pos t)
    simp [positiveSupport, hp]
  · have hp : 0 < (complementaryKleinPoint t).coord 5 := by
      change 0 < complementaryKleinRaw t 5 / complementaryKleinMass t
      exact div_pos (t.2 1) (complementaryKleinMass_pos t)
    simp [positiveSupport, hp]

theorem complementaryKleinPoint_ratio13 (t : ComplementaryKleinParameters) :
    (complementaryKleinPoint t).coord 4 /
      (complementaryKleinPoint t).coord 1 = t.1 0 := by
  change (complementaryKleinRaw t 4 / complementaryKleinMass t) /
      (complementaryKleinRaw t 1 / complementaryKleinMass t) = t.1 0
  simp only [complementaryKleinRaw]
  field_simp [ne_of_gt (complementaryKleinMass_pos t), ne_of_gt (t.2 1)]

theorem complementaryKleinPoint_ratio23 (t : ComplementaryKleinParameters) :
    (complementaryKleinPoint t).coord 5 /
      (complementaryKleinPoint t).coord 1 = t.1 1 := by
  change (complementaryKleinRaw t 5 / complementaryKleinMass t) /
      (complementaryKleinRaw t 1 / complementaryKleinMass t) = t.1 1
  simp only [complementaryKleinRaw]
  field_simp [ne_of_gt (complementaryKleinMass_pos t), ne_of_gt (t.2 1)]

/-- The projective chart is injective because its two parameters are
recovered by ratios to the positive pivot `p₀₂`. -/
theorem complementaryKleinPoint_injective :
    Function.Injective complementaryKleinPoint := by
  intro t s h
  apply Subtype.ext
  funext i
  fin_cases i
  · have hr := congrArg (fun P : NormalizedPositivePluckerPoint =>
      P.coord 4 / P.coord 1) h
    rw [complementaryKleinPoint_ratio13 t,
      complementaryKleinPoint_ratio13 s] at hr
    exact hr
  · have hr := congrArg (fun P : NormalizedPositivePluckerPoint =>
      P.coord 5 / P.coord 1) h
    rw [complementaryKleinPoint_ratio23 t,
      complementaryKleinPoint_ratio23 s] at hr
    exact hr

/-- The exact projective positroid stratum supported on `{01,02,13,23}`. -/
abbrev ComplementaryKleinCell :=
  {P : NormalizedPositivePluckerPoint //
    P ∈ supportStratum ({0, 1, 4, 5} : Finset (Fin 6))}

/-- Every point of the exact-support stratum is in the chart.  The Klein
equation determines the remaining coordinate `p₀₁` from `p₁₃` and `p₂₃`. -/
theorem complementaryKleinPoint_surjective :
    ∀ P : NormalizedPositivePluckerPoint,
      P ∈ supportStratum ({0, 1, 4, 5} : Finset (Fin 6)) →
        ∃ t : ComplementaryKleinParameters, complementaryKleinPoint t = P := by
  intro P hP
  have hs : positiveSupport P = ({0, 1, 4, 5} : Finset (Fin 6)) := hP
  have hz2 : P.coord 2 = 0 := by
    have hn : ¬ 0 < P.coord 2 := by
      intro hp
      have hm : (2 : Fin 6) ∈ positiveSupport P :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
      rw [hs] at hm
      simp at hm
    exact le_antisymm (le_of_not_gt hn) (P.coord_nonneg 2)
  have hz3 : P.coord 3 = 0 := by
    have hn : ¬ 0 < P.coord 3 := by
      intro hp
      have hm : (3 : Fin 6) ∈ positiveSupport P :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
      rw [hs] at hm
      simp at hm
    exact le_antisymm (le_of_not_gt hn) (P.coord_nonneg 3)
  have hp0 : 0 < P.coord 0 := by
    have hm : (0 : Fin 6) ∈ positiveSupport P := by rw [hs]; simp
    exact (Finset.mem_filter.mp hm).2
  have hp1 : 0 < P.coord 1 := by
    have hm : (1 : Fin 6) ∈ positiveSupport P := by rw [hs]; simp
    exact (Finset.mem_filter.mp hm).2
  have hp4 : 0 < P.coord 4 := by
    have hm : (4 : Fin 6) ∈ positiveSupport P := by rw [hs]; simp
    exact (Finset.mem_filter.mp hm).2
  have hp5 : 0 < P.coord 5 := by
    have hm : (5 : Fin 6) ∈ positiveSupport P := by rw [hs]; simp
    exact (Finset.mem_filter.mp hm).2
  have hklein : P.coord 0 * P.coord 5 = P.coord 1 * P.coord 4 := by
    have h := P.klein
    rw [hz2, hz3] at h
    linarith
  let t : ComplementaryKleinParameters :=
    ⟨![P.coord 4 / P.coord 1, P.coord 5 / P.coord 1], by
      intro i
      fin_cases i
      · exact div_pos hp4 hp1
      · exact div_pos hp5 hp1⟩
  refine ⟨t, ?_⟩
  apply NormalizedPositivePluckerPoint.ext
  funext i
  have hraw (i : Fin 6) :
      complementaryKleinRaw t i = P.coord i / P.coord 1 := by
    fin_cases i
    · change (P.coord 4 / P.coord 1) / (P.coord 5 / P.coord 1) =
        P.coord 0 / P.coord 1
      have hden : P.coord 5 / P.coord 1 ≠ 0 :=
        div_ne_zero (ne_of_gt hp5) (ne_of_gt hp1)
      field_simp [ne_of_gt hp1, ne_of_gt hp5, hden]
      nlinarith [hklein]
    · change (1 : ℝ) = P.coord 1 / P.coord 1
      field_simp [ne_of_gt hp1]
    · simp [complementaryKleinRaw, hz2]
    · simp [complementaryKleinRaw, hz3]
    · simp [complementaryKleinRaw, t]
    · simp [complementaryKleinRaw, t]
  have hmass : complementaryKleinMass t = 1 / P.coord 1 := by
    unfold complementaryKleinMass
    calc
      (∑ i : Fin 6, complementaryKleinRaw t i) =
          ∑ i : Fin 6, P.coord i / P.coord 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hraw i
      _ = (∑ i : Fin 6, P.coord i) / P.coord 1 := (Finset.sum_div ..).symm
      _ = 1 / P.coord 1 := by rw [P.coord_sum_one]
  change complementaryKleinRaw t i / complementaryKleinMass t = P.coord i
  rw [hraw, hmass]
  field_simp [ne_of_gt hp1]

/-- The positive parameter domain is equivalent to the entire normalized
positroid stratum, not just a subset of it. -/
noncomputable def complementaryKleinChartEquiv :
    ComplementaryKleinParameters ≃ ComplementaryKleinCell where
  toFun t := ⟨complementaryKleinPoint t, complementaryKleinPoint_support t⟩
  invFun P := Classical.choose (complementaryKleinPoint_surjective P.1 P.2)
  left_inv t := complementaryKleinPoint_injective
    (Classical.choose_spec (complementaryKleinPoint_surjective
      (complementaryKleinPoint t) (complementaryKleinPoint_support t)))
  right_inv P := by
    apply Subtype.ext
    exact Classical.choose_spec (complementaryKleinPoint_surjective P.1 P.2)

/-- The oriented coordinate frame on the two-dimensional cell. -/
noncomputable def complementaryKleinFrame :
    Fin 2 → (Fin 2 → ℝ) := Pi.basisFun ℝ (Fin 2)

/-- The logarithmic density `dlog u ∧ dlog v` on the cell. -/
noncomputable def complementaryKleinDlogDensity
    (t : ComplementaryKleinParameters) : ℝ :=
  (t.1 0)⁻¹ * (t.1 1)⁻¹

/-- The logarithmic residue along the `u = 0` coordinate removes its inverse
factor from the two-cell density. -/
theorem complementaryKleinDlogDensity_residue_u
    (t : ComplementaryKleinParameters) :
    t.1 0 * complementaryKleinDlogDensity t = (t.1 1)⁻¹ := by
  unfold complementaryKleinDlogDensity
  field_simp [ne_of_gt (t.2 0), ne_of_gt (t.2 1)]

/-- The logarithmic residue along the `v = 0` coordinate removes its inverse
factor from the two-cell density. -/
theorem complementaryKleinDlogDensity_residue_v
    (t : ComplementaryKleinParameters) :
    t.1 1 * complementaryKleinDlogDensity t = (t.1 0)⁻¹ := by
  unfold complementaryKleinDlogDensity
  field_simp [ne_of_gt (t.2 0), ne_of_gt (t.2 1)]

/-- The genuine alternating two-form in the positive chart. -/
noncomputable def complementaryKleinCanonicalForm
    (t : ComplementaryKleinParameters) :
    ((Fin 2 → ℝ) [⋀^Fin 2]→ₗ[ℝ] ℝ) :=
  complementaryKleinDlogDensity t • (Pi.basisFun ℝ (Fin 2)).det

theorem complementaryKleinCanonicalForm_frame
    (t : ComplementaryKleinParameters) :
    complementaryKleinCanonicalForm t complementaryKleinFrame =
      complementaryKleinDlogDensity t := by
  rw [complementaryKleinCanonicalForm, complementaryKleinFrame]
  change complementaryKleinDlogDensity t *
    (Pi.basisFun ℝ (Fin 2)).det (Pi.basisFun ℝ (Fin 2)) = _
  rw [Module.Basis.det_self]
  simp

theorem complementaryKleinCanonicalForm_positive
    (t : ComplementaryKleinParameters) :
    0 < complementaryKleinCanonicalForm t complementaryKleinFrame := by
  rw [complementaryKleinCanonicalForm_frame, complementaryKleinDlogDensity]
  exact mul_pos (inv_pos.mpr (t.2 0)) (inv_pos.mpr (t.2 1))

/-- The intrinsic two-form transported to every point of the cell. -/
noncomputable def complementaryKleinCellCanonicalForm
    (P : ComplementaryKleinCell) :
    ((Fin 2 → ℝ) [⋀^Fin 2]→ₗ[ℝ] ℝ) :=
  complementaryKleinCanonicalForm (complementaryKleinChartEquiv.symm P)

theorem complementaryKleinCellCanonicalForm_value
    (P : ComplementaryKleinCell) :
    complementaryKleinCellCanonicalForm P complementaryKleinFrame =
      complementaryKleinDlogDensity (complementaryKleinChartEquiv.symm P) :=
  complementaryKleinCanonicalForm_frame (complementaryKleinChartEquiv.symm P)

theorem complementaryKleinCellCanonicalForm_positive
    (P : ComplementaryKleinCell) :
    0 < complementaryKleinCellCanonicalForm P complementaryKleinFrame := by
  rw [complementaryKleinCellCanonicalForm_value,
    complementaryKleinDlogDensity]
  exact mul_pos
    (inv_pos.mpr ((complementaryKleinChartEquiv.symm P).2 0))
    (inv_pos.mpr ((complementaryKleinChartEquiv.symm P).2 1))

end InfoGeometry.Canonical.Gr24ComplementaryKleinPositroidCellForm
