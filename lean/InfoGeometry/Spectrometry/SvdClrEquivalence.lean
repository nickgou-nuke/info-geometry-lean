import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace InfoGeometry.Spectrometry.SvdClrEquivalence

open scoped BigOperators

namespace ProofDependency

inductive Archetype
  | positiveScale
  | positiveFactorization
  | logarithmicRepresentation
  | transportEquivalence
  | centeredNormalization
  | commonProfileRecovery
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | positiveScale => {positiveScale}
  | positiveFactorization => {positiveScale, positiveFactorization}
  | logarithmicRepresentation =>
      {positiveScale, positiveFactorization, logarithmicRepresentation}
  | transportEquivalence => {positiveScale, transportEquivalence}
  | centeredNormalization =>
      {positiveScale, positiveFactorization, logarithmicRepresentation, centeredNormalization}
  | commonProfileRecovery => Finset.univ

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem dependency_branches :
    positiveScale ≤ positiveFactorization ∧
    positiveFactorization ≤ logarithmicRepresentation ∧
    logarithmicRepresentation ≤ centeredNormalization ∧
    positiveScale ≤ transportEquivalence ∧
    centeredNormalization ≤ commonProfileRecovery ∧
    transportEquivalence ≤ commonProfileRecovery := by
  change
    prerequisites positiveScale ⊆ prerequisites positiveFactorization ∧
    prerequisites positiveFactorization ⊆ prerequisites logarithmicRepresentation ∧
    prerequisites logarithmicRepresentation ⊆ prerequisites centeredNormalization ∧
    prerequisites positiveScale ⊆ prerequisites transportEquivalence ∧
    prerequisites centeredNormalization ⊆ prerequisites commonProfileRecovery ∧
    prerequisites transportEquivalence ⊆ prerequisites commonProfileRecovery
  decide

theorem normalization_and_transport_incomparable :
    ¬ centeredNormalization ≤ transportEquivalence ∧
    ¬ transportEquivalence ≤ centeredNormalization := by
  change
    ¬ prerequisites centeredNormalization ⊆ prerequisites transportEquivalence ∧
    ¬ prerequisites transportEquivalence ⊆ prerequisites centeredNormalization
  decide

end ProofDependency

noncomputable section

variable {rowCount columnCount : ℕ}

def responseMatrix (profile : Fin rowCount → ℝ) (scales : Fin columnCount → ℝ) :
    Matrix (Fin rowCount) (Fin columnCount) ℝ :=
  Matrix.vecMulVec profile scales

def multiplicativeTransport
    (observed : Matrix (Fin rowCount) (Fin columnCount) ℝ)
    (scales : Fin columnCount → ℝ) : Matrix (Fin rowCount) (Fin columnCount) ℝ :=
  fun row column => observed row column / scales column

def logarithmicTransport
    (observed : Matrix (Fin rowCount) (Fin columnCount) ℝ)
    (shifts : Fin columnCount → ℝ) : Matrix (Fin rowCount) (Fin columnCount) ℝ :=
  fun row column => observed row column * Real.exp (-shifts column)

theorem transport_equivalence
    (observed : Matrix (Fin rowCount) (Fin columnCount) ℝ)
    (scales : Fin columnCount → ℝ) (scales_pos : ∀ column, 0 < scales column) :
    logarithmicTransport observed (fun column => Real.log (scales column)) =
      multiplicativeTransport observed scales := by
  ext row column
  simp [logarithmicTransport, multiplicativeTransport, Real.exp_neg,
    Real.exp_log (scales_pos column), div_eq_mul_inv]

theorem response_collapse
    (profile : Fin rowCount → ℝ) (scales : Fin columnCount → ℝ)
    (scales_ne : ∀ column, scales column ≠ 0) :
    multiplicativeTransport (responseMatrix profile scales) scales =
      fun row _ => profile row := by
  ext row column
  simp [multiplicativeTransport, responseMatrix, Matrix.vecMulVec, scales_ne column]

theorem response_rank_le_one
    (profile : Fin rowCount → ℝ) (scales : Fin columnCount → ℝ) :
    (responseMatrix profile scales).rank ≤ 1 := by
  exact Matrix.rank_vecMulVec_le profile scales

theorem response_rank_eq_one
    (profile : Fin rowCount → ℝ) (scales : Fin columnCount → ℝ)
    (row : Fin rowCount) (column : Fin columnCount)
    (profile_ne : profile row ≠ 0) (scale_ne : scales column ≠ 0) :
    (responseMatrix profile scales).rank = 1 := by
  have rank_le := response_rank_le_one profile scales
  have rank_ne : (responseMatrix profile scales).rank ≠ 0 := by
    intro rank_zero
    have range_zero : LinearMap.range (responseMatrix profile scales).mulVecLin = ⊥ :=
      Submodule.finrank_eq_zero.mp rank_zero
    have map_zero := LinearMap.range_eq_bot.mp range_zero
    have entry_zero := congrFun
      (congrArg (fun linearMap => linearMap (Pi.single column 1)) map_zero) row
    have product_zero : profile row * scales column = 0 := by
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, responseMatrix,
        Matrix.vecMulVec, Pi.single_apply, mul_ite] using entry_zero
    exact mul_ne_zero profile_ne scale_ne product_zero
  omega

theorem log_response
    (profile : Fin rowCount → ℝ) (scales : Fin columnCount → ℝ)
    (profile_pos : ∀ row, 0 < profile row) (scales_pos : ∀ column, 0 < scales column)
    (row : Fin rowCount) (column : Fin columnCount) :
    Real.log (responseMatrix profile scales row column) =
      Real.log (profile row) + Real.log (scales column) := by
  exact Real.log_mul (ne_of_gt (profile_pos row)) (ne_of_gt (scales_pos column))

def HasPositiveFactorization
    (observed : Matrix (Fin rowCount) (Fin columnCount) ℝ) : Prop :=
  ∃ profile scales,
    (∀ row, 0 < profile row) ∧ (∀ column, 0 < scales column) ∧
      observed = responseMatrix profile scales

theorem positive_factorization_iff_log_additive
    (observed : Matrix (Fin rowCount) (Fin columnCount) ℝ)
    (observed_pos : ∀ row column, 0 < observed row column) :
    HasPositiveFactorization observed ↔
      ∃ (profileLogs : Fin rowCount → ℝ) (shifts : Fin columnCount → ℝ), ∀ row column,
        Real.log (observed row column) = profileLogs row + shifts column := by
  constructor
  · rintro ⟨profile, scales, profile_pos, scales_pos, factorization⟩
    refine ⟨fun row => Real.log (profile row), fun column => Real.log (scales column), ?_⟩
    intro row column
    rw [factorization]
    exact log_response profile scales profile_pos scales_pos row column
  · rintro ⟨profileLogs, shifts, log_factorization⟩
    refine ⟨fun row => Real.exp (profileLogs row), fun column => Real.exp (shifts column),
      fun row => Real.exp_pos _, fun column => Real.exp_pos _, ?_⟩
    ext row column
    change observed row column = Real.exp (profileLogs row) * Real.exp (shifts column)
    rw [← Real.exp_add, ← log_factorization row column,
      Real.exp_log (observed_pos row column)]

def mean (values : Fin columnCount → ℝ) : ℝ :=
  (∑ column, values column) / columnCount

def center (values : Fin columnCount → ℝ) : Fin columnCount → ℝ :=
  fun column => values column - mean values

def rowClr (observed : Matrix (Fin rowCount) (Fin columnCount) ℝ) :
    Matrix (Fin rowCount) (Fin columnCount) ℝ :=
  fun row => center (fun column => Real.log (observed row column))

theorem sum_center (values : Fin columnCount → ℝ) (count_pos : 0 < columnCount) :
    ∑ column, center values column = 0 := by
  have count_ne : (columnCount : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt count_pos)
  simp only [center, mean, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem mean_add_constant
    (values : Fin columnCount → ℝ) (offset : ℝ) (count_pos : 0 < columnCount) :
    mean (fun column => offset + values column) = offset + mean values := by
  have count_ne : (columnCount : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt count_pos)
  simp [mean, Finset.sum_add_distrib, add_div, count_ne]

theorem center_add_constant
    (values : Fin columnCount → ℝ) (offset : ℝ) (count_pos : 0 < columnCount) :
    center (fun column => offset + values column) = center values := by
  funext column
  simp only [center, mean_add_constant values offset count_pos]
  ring

theorem clr_response
    (profile : Fin rowCount → ℝ) (scales : Fin columnCount → ℝ)
    (profile_pos : ∀ row, 0 < profile row) (scales_pos : ∀ column, 0 < scales column)
    (count_pos : 0 < columnCount) :
    rowClr (responseMatrix profile scales) =
      fun _ => center (fun column => Real.log (scales column)) := by
  funext row
  unfold rowClr
  simp_rw [log_response profile scales profile_pos scales_pos]
  exact center_add_constant _ _ count_pos

theorem positive_factorization_iff_common_clr
    (observed : Matrix (Fin rowCount) (Fin columnCount) ℝ)
    (observed_pos : ∀ row column, 0 < observed row column)
    (count_pos : 0 < columnCount) :
    HasPositiveFactorization observed ↔
      ∃ shifts : Fin columnCount → ℝ, ∀ row column,
        rowClr observed row column = shifts column := by
  constructor
  · rintro ⟨profile, scales, profile_pos, scales_pos, factorization⟩
    refine ⟨center (fun column => Real.log (scales column)), ?_⟩
    intro row column
    rw [factorization, clr_response profile scales profile_pos scales_pos count_pos]
  · rintro ⟨shifts, common_clr⟩
    apply (positive_factorization_iff_log_additive observed observed_pos).mpr
    refine ⟨fun row => mean (fun column => Real.log (observed row column)), shifts, ?_⟩
    intro row column
    have equality := common_clr row column
    dsimp [rowClr, center] at equality
    linarith

theorem row_clr_invariant_under_row_scaling
    (observed : Matrix (Fin rowCount) (Fin columnCount) ℝ)
    (multipliers : Fin rowCount → ℝ)
    (observed_pos : ∀ row column, 0 < observed row column)
    (multipliers_pos : ∀ row, 0 < multipliers row)
    (count_pos : 0 < columnCount) :
    rowClr (fun row column => multipliers row * observed row column) = rowClr observed := by
  funext row
  unfold rowClr
  simp_rw [Real.log_mul (ne_of_gt (multipliers_pos row))
    (ne_of_gt (observed_pos row _))]
  exact center_add_constant _ _ count_pos

def geometricMean (scales : Fin columnCount → ℝ) : ℝ :=
  Real.exp (mean (fun column => Real.log (scales column)))

def normalizedScales (scales : Fin columnCount → ℝ) : Fin columnCount → ℝ :=
  fun column => scales column / geometricMean scales

theorem geometric_mean_pos (scales : Fin columnCount → ℝ) :
    0 < geometricMean scales := by
  exact Real.exp_pos _

theorem normalized_scale_eq_exp_center
    (scales : Fin columnCount → ℝ) (scales_pos : ∀ column, 0 < scales column)
    (column : Fin columnCount) :
    normalizedScales scales column =
      Real.exp (center (fun position => Real.log (scales position)) column) := by
  simp [normalizedScales, geometricMean, center, Real.exp_sub,
    Real.exp_log (scales_pos column)]

theorem normalized_scales_product
    (scales : Fin columnCount → ℝ) (scales_pos : ∀ column, 0 < scales column)
    (count_pos : 0 < columnCount) :
    ∏ column, normalizedScales scales column = 1 := by
  simp_rw [normalized_scale_eq_exp_center scales scales_pos]
  rw [← Real.exp_sum, sum_center _ count_pos, Real.exp_zero]

theorem normalized_factorization
    (profile : Fin rowCount → ℝ) (scales : Fin columnCount → ℝ) :
    responseMatrix profile scales =
      responseMatrix (fun row => profile row * geometricMean scales) (normalizedScales scales) := by
  ext row column
  dsimp [responseMatrix, Matrix.vecMulVec, normalizedScales]
  have mean_ne := ne_of_gt (geometric_mean_pos scales)
  field_simp

theorem centered_transport_collapse
    (profile : Fin rowCount → ℝ) (scales : Fin columnCount → ℝ)
    (scales_pos : ∀ column, 0 < scales column) :
    logarithmicTransport (responseMatrix profile scales)
        (center (fun column => Real.log (scales column))) =
      fun row _ => profile row * geometricMean scales := by
  ext row column
  dsimp [logarithmicTransport, responseMatrix, Matrix.vecMulVec, center]
  rw [neg_sub, Real.exp_sub, Real.exp_log (scales_pos column)]
  change profile row * scales column * (geometricMean scales / scales column) =
    profile row * geometricMean scales
  field_simp [ne_of_gt (scales_pos column)]

theorem transport_residual
    (observed : Matrix (Fin rowCount) (Fin columnCount) ℝ)
    (profile : Fin rowCount → ℝ) (scales : Fin columnCount → ℝ)
    (scales_ne : ∀ column, scales column ≠ 0)
    (row : Fin rowCount) (column : Fin columnCount) :
    multiplicativeTransport observed scales row column - profile row =
      (observed row column - responseMatrix profile scales row column) / scales column := by
  dsimp [multiplicativeTransport, responseMatrix, Matrix.vecMulVec]
  field_simp [scales_ne column]

end

end InfoGeometry.Spectrometry.SvdClrEquivalence
