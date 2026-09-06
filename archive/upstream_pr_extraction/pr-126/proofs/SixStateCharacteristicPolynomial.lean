import proofs.SixStateSpectralBridge
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Six-state spectral separation

This owner proves scalar separation and injectivity of the six labelled
eigenvalues.  Linear independence, a spectral basis, and the characteristic
polynomial are deliberately left as subsequent finite-dimensional theorems.
-/

noncomputable section
namespace SixStateCharacteristicPolynomial

open HexagonalSixRootTiling SixStateSpectralBridge TwoSheetThreeColorWeyl

theorem omega_ne_zero (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  intro h
  rw [h] at hω
  norm_num at hω

theorem omega_ne_one (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  intro h
  rw [h] at hω
  norm_num at hω

theorem omega_sq_ne_one (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 2 ≠ 1 := by
  intro h2
  apply omega_ne_one ω hω
  calc
    ω = ω * 1 := by ring
    _ = ω * ω ^ 2 := by rw [h2]
    _ = ω ^ 3 := by ring
    _ = 1 := omega_cube ω hω

theorem omega_ne_omega_sq (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ≠ ω ^ 2 := by
  intro h
  have hz : ω ≠ 0 := omega_ne_zero ω hω
  apply omega_ne_one ω hω
  apply mul_left_cancel₀ hz
  simpa [pow_two] using h.symm

theorem colorEigenvalue_injective (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Injective (colorEigenvalue ω) := by
  intro a b h
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  have hb : b = 0 ∨ b = 1 ∨ b = 2 := by fin_cases b <;> simp
  have h20 : (2 : HexColor) ≠ 0 := by decide
  have h21 : (2 : HexColor) ≠ 1 := by decide
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals
    simp [colorEigenvalue, h20, h21,
      omega_ne_one ω hω, Ne.symm (omega_ne_one ω hω),
      omega_sq_ne_one ω hω, Ne.symm (omega_sq_ne_one ω hω),
      omega_ne_omega_sq ω hω, Ne.symm (omega_ne_omega_sq ω hω)] at h ⊢

theorem colorEigenvalue_ne_neg (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (a b : HexColor) :
    colorEigenvalue ω a ≠ -colorEigenvalue ω b := by
  intro h
  have ha := colorEigenvalue_cube ω hω a
  have hb := colorEigenvalue_cube ω hω b
  have hc : (1 : ℂ) = -1 := calc
    1 = colorEigenvalue ω a ^ 3 := ha.symm
    _ = (-colorEigenvalue ω b) ^ 3 := congrArg (fun z : ℂ => z ^ 3) h
    _ = -(colorEigenvalue ω b ^ 3) := by ring
    _ = -1 := by rw [hb]
  norm_num at hc

theorem labelledEigenvalue_sheet_cube (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (n : HexIndex) :
    labelledEigenvalue ω n ^ 3 =
      match sheetOf n with
      | .positive => 1
      | .negative => -1 := by
  cases h : sheetOf n
  · simpa [labelledEigenvalue, h] using colorEigenvalue_cube ω hω (colorOf n)
  · simp only [labelledEigenvalue, h]
    calc
      (-colorEigenvalue ω (colorOf n)) ^ 3 =
          -(colorEigenvalue ω (colorOf n) ^ 3) := by ring
      _ = -1 := by rw [colorEigenvalue_cube ω hω]

theorem labelledEigenvalue_injective (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Injective (labelledEigenvalue ω) := by
  intro n m hnm
  have hs : sheetOf n = sheetOf m := by
    cases hn : sheetOf n <;> cases hm : sheetOf m
    · rfl
    · exfalso
      apply colorEigenvalue_ne_neg ω hω (colorOf n) (colorOf m)
      simpa [labelledEigenvalue, hn, hm] using hnm
    · exfalso
      apply colorEigenvalue_ne_neg ω hω (colorOf m) (colorOf n)
      simpa [labelledEigenvalue, hn, hm] using hnm.symm
    · rfl
  have hc : colorOf n = colorOf m := by
    have hnm' := hnm
    simp only [labelledEigenvalue] at hnm'
    rw [hs] at hnm'
    cases hm : sheetOf m
    · apply colorEigenvalue_injective ω hω
      simpa [hm] using hnm'
    · apply colorEigenvalue_injective ω hω
      have heq := congrArg Neg.neg hnm'
      simpa [hm] using heq
  apply sheetColorEquiv.injective
  change (sheetOf n, colorOf n) = (sheetOf m, colorOf m)
  exact Prod.ext hs hc

/-- The six concrete spectral labels have pairwise distinct eigenvalues. -/
theorem labelled_values_pairwise (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) {n m : HexIndex} (hnm : n ≠ m) :
    labelledEigenvalue ω n ≠ labelledEigenvalue ω m := by
  intro h
  exact hnm (labelledEigenvalue_injective ω hω h)

/-! ## Spectral completeness -/

/-- Native linear endomorphism associated to the concrete triality matrix. -/
def trialityEnd : Module.End ℂ State := sixfoldTriality.mulVecLin

theorem labelled_hasEigenvector (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (n : HexIndex) :
    trialityEnd.HasEigenvector (labelledEigenvalue ω n) (labelledVector ω n) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    simpa [trialityEnd, Matrix.mulVecLin_apply] using labelledVector_eigen ω hω n
  · exact labelledVector_nonzero ω n

/-- Distinct labelled eigenvalues make the six concrete eigenvectors independent. -/
theorem labelledVector_linearIndependent (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    LinearIndependent ℂ (labelledVector ω) := by
  exact trialityEnd.eigenvectors_linearIndependent'
    (labelledEigenvalue ω) (labelledEigenvalue_injective ω hω)
    (labelledVector ω) (labelled_hasEigenvector ω hω)

theorem hexIndex_card_eq_state_finrank :
    Fintype.card HexIndex = Module.finrank ℂ State := by
  simp [State, TwoSheetThreeColorWeyl.SixIndex]

/-- The six labelled triality eigenvectors form a basis of the six-state carrier. -/
noncomputable def labelledSpectralBasis (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) : Module.Basis HexIndex ℂ State :=
  basisOfLinearIndependentOfCardEqFinrank
    (labelledVector_linearIndependent ω hω) hexIndex_card_eq_state_finrank

@[simp] theorem labelledSpectralBasis_apply (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (n : HexIndex) :
    labelledSpectralBasis ω hω n = labelledVector ω n := by
  simp [labelledSpectralBasis]

end SixStateCharacteristicPolynomial
end noncomputable section
