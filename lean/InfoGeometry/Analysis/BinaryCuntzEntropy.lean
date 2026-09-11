import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.AxiomFreeGNS

namespace InfoGeometry.Analysis

open InfoGeometry.Analysis.L2CantorCommutation

/-! Finite binary entropy readouts for concrete Cuntz branch projections. -/

noncomputable def binaryEntropy (p : ℝ) : ℝ := Real.binEntropy p

@[simp] theorem binaryEntropy_half : binaryEntropy (1 / 2 : ℝ) = Real.log 2 := by
  unfold binaryEntropy
  convert Real.binEntropy_two_inv using 1 <;> norm_num

theorem cuntz_symmetric_branch_entropy_eq_log_two
    (φ : (H → H) →+ ℝ)
    (h_one : φ id = 1)
    (h_symm : φ (S_left ∘ star_S_left) = φ (S_right ∘ star_S_right)) :
    binaryEntropy (φ (S_left ∘ star_S_left)) = Real.log 2 := by
  obtain ⟨hleft, _⟩ :=
    InfoGeometry.Analysis.AxiomFreeGNS.branch_weight_one_half φ
      (S_left ∘ star_S_left) (S_right ∘ star_S_right) id
      (by simpa using S_left_star_S_left_add_S_right_star_S_right)
      h_one h_symm
  rw [hleft]
  exact binaryEntropy_half

theorem binaryEntropy_le_log_two {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    binaryEntropy p ≤ Real.log 2 := by
  by_cases hhalf : p ≤ (1 / 2 : ℝ)
  · have hp_mem : p ∈ Set.Icc (0 : ℝ) (2⁻¹) := by simpa [show (1 / 2 : ℝ) = 2⁻¹ by norm_num] using And.intro hp₀ hhalf
    have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) (2⁻¹) := by norm_num
    have hmono := Real.binEntropy_strictMonoOn.monotoneOn hp_mem hhalf_mem (by simpa using hhalf)
    simpa [binaryEntropy] using hmono
  · have hhalf' : (1 / 2 : ℝ) ≤ p := by linarith
    have hp_mem : p ∈ Set.Icc (2⁻¹ : ℝ) 1 := by simpa using And.intro hhalf' hp₁
    have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc (2⁻¹ : ℝ) 1 := by norm_num
    have hanti := Real.binEntropy_strictAntiOn.antitoneOn hhalf_mem hp_mem (by simpa using hhalf')
    simpa [binaryEntropy] using hanti

theorem binaryEntropy_eq_log_two_iff {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    binaryEntropy p = Real.log 2 ↔ p = 1 / 2 := by
  constructor
  · intro heq
    by_contra hne
    have heq' : Real.binEntropy p = Real.log 2 := by simpa [binaryEntropy] using heq
    by_cases hlt : p < (1 / 2 : ℝ)
    · have hp_mem : p ∈ Set.Icc (0 : ℝ) (2⁻¹) := by simpa using And.intro hp₀ hlt.le
      have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) (2⁻¹) := by norm_num
      have hstrict := Real.binEntropy_strictMonoOn hp_mem hhalf_mem (by simpa using hlt)
      have hlog : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
        convert Real.binEntropy_two_inv using 1 <;> norm_num
      rw [heq', hlog] at hstrict
      exact lt_irrefl _ hstrict
    · have hgt : (1 / 2 : ℝ) < p := by
        have hle : (1 / 2 : ℝ) ≤ p := by linarith
        exact lt_of_le_of_ne hle (Ne.symm hne)
      have hp_mem : p ∈ Set.Icc (2⁻¹ : ℝ) 1 := by simpa using And.intro hgt.le hp₁
      have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc (2⁻¹ : ℝ) 1 := by norm_num
      have hstrict := Real.binEntropy_strictAntiOn hhalf_mem hp_mem (by simpa using hgt)
      have hlog : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
        convert Real.binEntropy_two_inv using 1 <;> norm_num
      rw [heq', hlog] at hstrict
      exact lt_irrefl _ hstrict
  · intro h
    subst p
    exact binaryEntropy_half

end InfoGeometry.Analysis
