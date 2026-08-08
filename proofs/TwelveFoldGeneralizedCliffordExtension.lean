import Mathlib
import proofs.TwoSheetThreeColorWeyl
import proofs.SixStateGeneralizedCliffordAlgebra
import proofs.TwelveFoldExtendedWeylBridge
import proofs.TwelveFoldArithmetic
import proofs.TwelveFoldCyclicRepresentation

noncomputable section
namespace TwelveFoldGeneralizedCliffordExtension

open TwoSheetThreeColorWeyl
open CRTGeneralizedPauliSix
open TwelveFoldArithmetic
open TwelveFoldExtendedWeylBridge
open SixStateGeneralizedCliffordAlgebra

/-- The two tensor generators used for the mixed-order span witness of `masterTwelve`. -/
def sheet_shift_generators : Set M6C :=
  ({tensor (1 : M2C) (colorShift ^ 2), tensor sheetGamma (colorShift ^ 2)} : Set M6C)

def masterTwelve_sheetColorShift_span : Submodule ℂ M6C :=
  Submodule.span ℂ sheet_shift_generators

def masterTwelve_tensor_generator_span : Submodule ℂ M6C :=
  Submodule.span ℂ ({tensor (1 : M2C) (colorShift ^ 2), tensor sheetGamma (colorShift ^ 2)} : Set M6C)

theorem masterTwelve_tensor_generator_decomposition :
    masterTwelve =
      ((1 - Complex.I) / 2 : ℂ) • tensor (1 : M2C) (colorShift ^ 2) +
      ((1 + Complex.I) / 2 : ℂ) • tensor sheetGamma (colorShift ^ 2) := by
  have hOmegaCube : omegaSheet ^ 3 = ((1 - Complex.I) / 2 : ℂ) • (1 : M2C) +
      ((1 + Complex.I) / 2 : ℂ) • sheetGamma := by
    ext i j <;> fin_cases i <;> fin_cases j
    · simp [omegaSheet, sheetPlus, sheetMinus, sheetGamma, pow_succ, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]; ring_nf
    · simp [omegaSheet, sheetPlus, sheetMinus, sheetGamma, pow_succ, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]; ring_nf
    · simp [omegaSheet, sheetPlus, sheetMinus, sheetGamma, pow_succ, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]; ring_nf
    · simp [omegaSheet, sheetPlus, sheetMinus, sheetGamma, pow_succ, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]; ring_nf
  calc
    masterTwelve = tensor (omegaSheet ^ 3) (colorShift ^ 2) := by
      rw [masterTwelve_tensor_formula]
    _ = tensor (((1 - Complex.I) / 2 : ℂ) • (1 : M2C) +
        ((1 + Complex.I) / 2 : ℂ) • sheetGamma) (colorShift ^ 2) := by
      rw [hOmegaCube]
    _ = ((1 - Complex.I) / 2 : ℂ) • tensor (1 : M2C) (colorShift ^ 2) +
        ((1 + Complex.I) / 2 : ℂ) • tensor sheetGamma (colorShift ^ 2) := by
      ext ⟨i, a⟩ ⟨j, b⟩ <;> simp [tensor, Matrix.kroneckerMap_apply, pow_succ, mul_add,
        add_smul, smul_add]

/-- The twelvefold master is a concrete linear combination of `I ⊗ X²` and `Γ ⊗ X²`. -/
theorem masterTwelve_in_I_tensor_X2_span :
    masterTwelve ∈ masterTwelve_sheetColorShift_span := by
  let S := masterTwelve_sheetColorShift_span
  rw [masterTwelve_tensor_generator_decomposition]
  apply Submodule.add_mem
  · exact Submodule.smul_mem S ((1 - Complex.I) / 2 : ℂ) (Submodule.subset_span (by simp [S, sheet_shift_generators]))
  · exact Submodule.smul_mem S ((1 + Complex.I) / 2 : ℂ) (Submodule.subset_span (by simp [S, sheet_shift_generators]))

/-- Same membership stated directly in the explicit two-generator `Set` span form. -/
theorem masterTwelve_in_exact_generator_span :
    masterTwelve ∈ masterTwelve_tensor_generator_span := by
  simpa [masterTwelve_tensor_generator_span] using masterTwelve_in_I_tensor_X2_span

/-- The mixed-order master order is genuinely twelvefold. -/
theorem masterTwelve_order_twelve : orderOf masterTwelve = 12 := by
  simpa using masterTwelve_orderOf

/-- Direct connection between the operator pipeline and the CRT monomial label `(4,3)`. -/
theorem masterTwelve_CRT_pipeline :
    (Matrix.reindexAlgEquiv ℂ ℂ CRTGeneralizedPauliSix.CRT_equiv).symm
      (masterTwelve ^ 2 : M6C) = crt6Monomial (4 : ZMod 6) (3 : ZMod 6) := by
  simpa [crt6Monomial] using masterTwelve_sq_CRT_monomial

/-- Concrete full classification statement for the six-state master: Clifford-normalizer-or-extension. -/
theorem masterTwelve_full_classification :
    masterTwelveInCliffordNormalizerCase ∨ masterTwelveInLargerSheetPhase := by
  exact masterTwelve_pipeline_classification

/-- Canonical full classification: disjunction + direct CRT squared-monomial bridge. -/
theorem masterTwelve_full_classification_masterSq :
    (masterTwelveInCliffordNormalizerCase ∨ masterTwelveInLargerSheetPhase) ∧
      masterTwelve_sq_CRT_monomial := by
  exact ⟨masterTwelve_full_classification, masterTwelve_sq_CRT_monomial⟩

/-- The two branches in the full classification are mutually exclusive by definition. -/
theorem masterTwelve_classification_exclusive :
    ¬ (masterTwelveInCliffordNormalizerCase ∧ masterTwelveInLargerSheetPhase) := by
  rintro ⟨hN, hL⟩
  exact hL.1 hN

/-- The larger-sheet-phase branch is equivalent to “not Clifford-normalizer” for this setup. -/
theorem masterTwelve_larger_sheet_phase_iff_not_normalizer :
    masterTwelveInLargerSheetPhase ↔ ¬ masterTwelveInCliffordNormalizerCase := by
  constructor
  · intro hL
    exact hL.1
  · intro hN
    exact ⟨hN, masterTwelve_not_phase_free_crt_half_root⟩

/-- The full classification package with the monomial pipeline tag. -/
theorem masterTwelve_full_classification_with_CRT :
    (masterTwelveInCliffordNormalizerCase ∨ masterTwelveInLargerSheetPhase) ∧
      (Matrix.reindexAlgEquiv ℂ ℂ CRTGeneralizedPauliSix.CRT_equiv).symm
        (masterTwelve ^ 2 : M6C) = crt6Monomial (4 : ZMod 6) (3 : ZMod 6) := by
  exact ⟨masterTwelve_full_classification, masterTwelve_CRT_pipeline⟩

theorem masterTwelve_full_pipeline_classification_sq :
    (masterTwelveInCliffordNormalizerCase ∨ masterTwelveInLargerSheetPhase) ∧
      masterTwelve_sq_CRT_monomial := by
  exact ⟨masterTwelve_full_classification, masterTwelve_sq_CRT_monomial⟩

theorem masterTwelve_full_pipeline_classification_pow_packet :
    (masterTwelveInCliffordNormalizerCase ∨ masterTwelveInLargerSheetPhase) ∧
      (Matrix.reindexAlgEquiv ℂ ℂ CRTGeneralizedPauliSix.CRT_equiv).symm
        (masterTwelve ^ 2 : M6C) = crt6Monomial (4 : ZMod 6) (3 : ZMod 6) ∧
      masterTwelve =
        ((1 - Complex.I) / 2 : ℂ) • tensor (1 : M2C) (colorShift ^ 2) +
        ((1 + Complex.I) / 2 : ℂ) • tensor sheetGamma (colorShift ^ 2) := by
  exact ⟨masterTwelve_full_classification, masterTwelve_CRT_pipeline, by
    simpa using masterTwelve_tensor_generator_decomposition⟩

/-- Canonical bridge: direct reuse of bridge-level full pipeline classifier and CRT monomial. -/
theorem masterTwelve_full_pipeline_classification :
    (masterTwelveInCliffordNormalizerCase ∨ masterTwelveInLargerSheetPhase) ∧
      (Matrix.reindexAlgEquiv ℂ ℂ CRTGeneralizedPauliSix.CRT_equiv).symm
        (masterTwelve ^ 2 : M6C) = crt6Monomial (4 : ZMod 6) (3 : ZMod 6) := by
  exact masterTwelve_full_classification_with_CRT

theorem masterTwelve_full_pipeline_classification_masterSq_direct :
    (masterTwelveInCliffordNormalizerCase ∨ masterTwelveInLargerSheetPhase) ∧
      masterTwelve_sq_CRT_monomial := by
  exact ⟨masterTwelve_full_classification, masterTwelve_sq_CRT_monomial⟩

/-- Direct final classification package: `Clifford-normalizer ∨ larger sheet phase` with the CRT squared monomial pipeline. -/
theorem masterTwelve_pipeline_full_classification_sq :
    (masterTwelveInCliffordNormalizerCase ∨ masterTwelveInLargerSheetPhase) ∧
      masterTwelve_sq_CRT_monomial := by
  exact ⟨masterTwelve_full_classification, masterTwelve_sq_CRT_monomial⟩

end TwelveFoldGeneralizedCliffordExtension
end noncomputable section
