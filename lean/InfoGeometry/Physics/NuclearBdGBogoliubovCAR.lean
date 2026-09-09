import Mathlib
import InfoGeometry.Physics.NuclearBdGTwoLevelExact
import InfoGeometry.Canonical.SplitCliffordTwoModeCAR

/-!
# Normalized two-level BdG eigenmode and CAR-preserving Bogoliubov ladder

For nonzero pairing `Δ`, the positive-energy eigenvector

`(Δ, E - ξ)`, where `E = sqrt(ξ²+Δ²)`,

is nonzero and can be normalized explicitly. Its coefficients `u,v` satisfy
`u²+v²=1`. Substituting the same coefficients into the two-mode CAR algebra
gives an exact Bogoliubov annihilation/creation pair which is nilpotent and
satisfies the canonical anticommutation relation.

For zero pairing the BdG block is already diagonal. The final existence theorem
covers all real parameters by selecting the appropriate coordinate eigenvector.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearBdGBogoliubovCAR

open Matrix
open InfoGeometry.Physics.NuclearBdGTwoLevelExact
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR

abbrev V2R := Fin 2 → ℝ

/-- Squared norm of the explicit positive-energy eigenvector. -/
def rawPositiveNormSq (ξ Δ : ℝ) : ℝ :=
  Δ ^ 2 + (bdgEnergy ξ Δ - ξ) ^ 2

/-- Positive normalization denominator. -/
def positiveNorm (ξ Δ : ℝ) : ℝ :=
  Real.sqrt (rawPositiveNormSq ξ Δ)

/-- Normalized particle coefficient. -/
def uCoeff (ξ Δ : ℝ) : ℝ :=
  Δ / positiveNorm ξ Δ

/-- Normalized hole coefficient. -/
def vCoeff (ξ Δ : ℝ) : ℝ :=
  (bdgEnergy ξ Δ - ξ) / positiveNorm ξ Δ

/-- The raw eigenvector is nonzero when the pairing coefficient is nonzero. -/
theorem rawPositiveNormSq_pos
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    0 < rawPositiveNormSq ξ Δ := by
  have hΔsq : 0 < Δ ^ 2 := sq_pos_of_ne_zero hΔ
  have hv : 0 ≤ (bdgEnergy ξ Δ - ξ) ^ 2 := sq_nonneg _
  unfold rawPositiveNormSq
  linarith

/-- Positivity of the normalization denominator. -/
theorem positiveNorm_pos
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    0 < positiveNorm ξ Δ := by
  exact Real.sqrt_pos.2 (rawPositiveNormSq_pos hΔ)

/-- Square of the normalization denominator. -/
theorem positiveNorm_sq
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    (positiveNorm ξ Δ) ^ 2 = rawPositiveNormSq ξ Δ := by
  exact Real.sq_sqrt (le_of_lt (rawPositiveNormSq_pos hΔ))

/-- Exact coefficient normalization. -/
theorem uCoeff_sq_add_vCoeff_sq
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    (uCoeff ξ Δ) ^ 2 + (vCoeff ξ Δ) ^ 2 = 1 := by
  have hsq := positiveNorm_sq (ξ := ξ) (Δ := Δ) hΔ
  unfold uCoeff vCoeff rawPositiveNormSq at *
  rw [div_pow, div_pow, ← add_div, hsq]
  exact div_self (by
    have hraw := rawPositiveNormSq_pos (ξ := ξ) (Δ := Δ) hΔ
    unfold rawPositiveNormSq at hraw
    exact ne_of_gt hraw)

/-- Normalized positive-energy eigenvector. -/
def normalizedPositiveEigenvector (ξ Δ : ℝ) : V2R :=
  ![uCoeff ξ Δ, vCoeff ξ Δ]

/-- The normalized vector is an actual positive-energy eigenvector. -/
theorem normalizedPositiveEigenvector_eigen
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    mulVec (bdgBlock ξ Δ) (normalizedPositiveEigenvector ξ Δ) =
      bdgEnergy ξ Δ • normalizedPositiveEigenvector ξ Δ := by
  have hnorm : positiveNorm ξ Δ ≠ 0 :=
    ne_of_gt (positiveNorm_pos hΔ)
  have hE := bdgEnergy_sq ξ Δ
  ext i
  fin_cases i
  · simp [bdgBlock, normalizedPositiveEigenvector, uCoeff, vCoeff,
      mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hnorm]
    ring
  · simp [bdgBlock, normalizedPositiveEigenvector, uCoeff, vCoeff,
      mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hnorm]
    nlinarith

/-- Bogoliubov annihilation operator associated with real coefficients. -/
def bogoliubovAnnihilation (u v : ℝ) : M4R :=
  u • a1 + v • a2Dag

/-- Bogoliubov creation operator associated with real coefficients. -/
def bogoliubovCreation (u v : ℝ) : M4R :=
  u • a1Dag + v • a2

/-- The annihilation operator is nilpotent for all coefficients. -/
theorem bogoliubovAnnihilation_sq (u v : ℝ) :
    bogoliubovAnnihilation u v *
      bogoliubovAnnihilation u v = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bogoliubovAnnihilation, a1, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;>
    ring

/-- The creation operator is nilpotent for all coefficients. -/
theorem bogoliubovCreation_sq (u v : ℝ) :
    bogoliubovCreation u v *
      bogoliubovCreation u v = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bogoliubovCreation, a1Dag, a2,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;>
    ring

/-- Exact CAR preservation under a normalized real Bogoliubov rotation. -/
theorem bogoliubov_CAR_of_normalized
    (u v : ℝ) (huv : u ^ 2 + v ^ 2 = 1) :
    bogoliubovAnnihilation u v * bogoliubovCreation u v +
      bogoliubovCreation u v * bogoliubovAnnihilation u v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bogoliubovAnnihilation, bogoliubovCreation,
      a1, a1Dag, a2, a2Dag, Matrix.mul_apply,
      Fin.sum_univ_four] <;>
    nlinarith

/-- The creation matrix is the transpose of the annihilation matrix. -/
theorem bogoliubovCreation_eq_transpose (u v : ℝ) :
    bogoliubovCreation u v =
      (bogoliubovAnnihilation u v)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bogoliubovAnnihilation, bogoliubovCreation,
      a1, a1Dag, a2, a2Dag]

/-- The coefficients constructed from the BdG eigenvector give an exact CAR
pair without an additional normalization hypothesis. -/
theorem normalized_bdg_CAR
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    bogoliubovAnnihilation (uCoeff ξ Δ) (vCoeff ξ Δ) *
        bogoliubovCreation (uCoeff ξ Δ) (vCoeff ξ Δ) +
      bogoliubovCreation (uCoeff ξ Δ) (vCoeff ξ Δ) *
        bogoliubovAnnihilation (uCoeff ξ Δ) (vCoeff ξ Δ) = 1 := by
  exact bogoliubov_CAR_of_normalized _ _
    (uCoeff_sq_add_vCoeff_sq hΔ)

/-- Complete nonzero-pairing Bogoliubov packet. -/
theorem normalized_bdg_bogoliubov_packet
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    mulVec (bdgBlock ξ Δ) (normalizedPositiveEigenvector ξ Δ) =
        bdgEnergy ξ Δ • normalizedPositiveEigenvector ξ Δ ∧
      (uCoeff ξ Δ) ^ 2 + (vCoeff ξ Δ) ^ 2 = 1 ∧
      bogoliubovAnnihilation (uCoeff ξ Δ) (vCoeff ξ Δ) *
          bogoliubovAnnihilation (uCoeff ξ Δ) (vCoeff ξ Δ) = 0 ∧
      bogoliubovCreation (uCoeff ξ Δ) (vCoeff ξ Δ) *
          bogoliubovCreation (uCoeff ξ Δ) (vCoeff ξ Δ) = 0 ∧
      bogoliubovAnnihilation (uCoeff ξ Δ) (vCoeff ξ Δ) *
          bogoliubovCreation (uCoeff ξ Δ) (vCoeff ξ Δ) +
        bogoliubovCreation (uCoeff ξ Δ) (vCoeff ξ Δ) *
          bogoliubovAnnihilation (uCoeff ξ Δ) (vCoeff ξ Δ) = 1 := by
  exact ⟨normalizedPositiveEigenvector_eigen hΔ,
    uCoeff_sq_add_vCoeff_sq hΔ,
    bogoliubovAnnihilation_sq _ _,
    bogoliubovCreation_sq _ _,
    normalized_bdg_CAR hΔ⟩

/-- At zero pairing the BdG block is already diagonal. -/
theorem bdgBlock_zero_pairing (ξ : ℝ) :
    bdgBlock ξ 0 = !![ξ, 0; 0, -ξ] := by
  rfl

/-- Positive-energy value for zero pairing. -/
theorem bdgEnergy_zero_pairing (ξ : ℝ) :
    bdgEnergy ξ 0 = |ξ| := by
  simp [bdgEnergy, Real.sqrt_sq_eq_abs]

/-- Every real two-level BdG block has normalized real coefficients which are
an eigenvector for the nonnegative energy and whose Bogoliubov ladder obeys
CAR.  The nonzero-pairing case uses the explicit normalized vector above; the
zero-pairing cases select the appropriate coordinate vector. -/
theorem exists_normalized_positive_eigenmode_with_CAR (ξ Δ : ℝ) :
    ∃ u v : ℝ,
      u ^ 2 + v ^ 2 = 1 ∧
      mulVec (bdgBlock ξ Δ) ![u, v] =
        bdgEnergy ξ Δ • ![u, v] ∧
      bogoliubovAnnihilation u v * bogoliubovCreation u v +
        bogoliubovCreation u v * bogoliubovAnnihilation u v = 1 := by
  by_cases hΔ : Δ = 0
  · subst Δ
    by_cases hξ : 0 ≤ ξ
    · refine ⟨1, 0, by norm_num, ?_,
        bogoliubov_CAR_of_normalized 1 0 (by norm_num)⟩
      have hE : bdgEnergy ξ 0 = ξ := by
        rw [bdgEnergy_zero_pairing, abs_of_nonneg hξ]
      rw [hE]
      ext i
      fin_cases i <;>
        simp [bdgBlock, mulVec, dotProduct, Fin.sum_univ_two]
    · have hξneg : ξ < 0 := lt_of_not_ge hξ
      refine ⟨0, 1, by norm_num, ?_,
        bogoliubov_CAR_of_normalized 0 1 (by norm_num)⟩
      have hE : bdgEnergy ξ 0 = -ξ := by
        rw [bdgEnergy_zero_pairing, abs_of_neg hξneg]
      rw [hE]
      ext i
      fin_cases i <;>
        simp [bdgBlock, mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨uCoeff ξ Δ, vCoeff ξ Δ,
      uCoeff_sq_add_vCoeff_sq hΔ, ?_, normalized_bdg_CAR hΔ⟩
    simpa [normalizedPositiveEigenvector] using
      normalizedPositiveEigenvector_eigen hΔ

end InfoGeometry.Physics.NuclearBdGBogoliubovCAR
